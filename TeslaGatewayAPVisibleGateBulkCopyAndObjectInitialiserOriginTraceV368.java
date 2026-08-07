// TeslaGatewayAPVisibleGateBulkCopyAndObjectInitialiserOriginTraceV368.java
//
// Read-only follow-up to V367. V367 validated the 0x40046F57 consumer but did
// not establish a causal producer. This pass widens only to the containing
// 0x40046F40..0x40046F8F object and looks for bulk/structure initialisation.
//
// It does not modify the Ghidra database, patch bytes, or export firmware.
// Ghidra 12.1.2.
//
// @category TeslaGateway.Analysis

import ghidra.app.decompiler.DecompInterface;
import ghidra.app.decompiler.DecompileResults;
import ghidra.app.script.GhidraScript;
import ghidra.program.model.address.Address;
import ghidra.program.model.lang.Register;
import ghidra.program.model.listing.Function;
import ghidra.program.model.listing.FunctionIterator;
import ghidra.program.model.listing.FunctionManager;
import ghidra.program.model.listing.Instruction;
import ghidra.program.model.listing.InstructionIterator;
import ghidra.program.model.listing.Listing;
import ghidra.program.model.mem.Memory;
import ghidra.program.model.mem.MemoryBlock;
import ghidra.program.model.scalar.Scalar;
import ghidra.program.model.symbol.Reference;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.OutputStreamWriter;
import java.nio.charset.StandardCharsets;
import java.text.SimpleDateFormat;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.Date;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Queue;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.zip.ZipEntry;
import java.util.zip.ZipOutputStream;

public class TeslaGatewayAPVisibleGateBulkCopyAndObjectInitialiserOriginTraceV368
        extends GhidraScript {

    private static final String SCRIPT_NAME =
        "TeslaGatewayAPVisibleGateBulkCopyAndObjectInitialiserOriginTraceV368";

    private static final long GATE = 0x40046F57L;
    private static final long OBJECT_START = 0x40046F40L;
    private static final long OBJECT_END = 0x40046F8FL;
    private static final long GATE_WORD = 0x40046F54L;

    private static final long[] ROOT_SITES = {
        0x000870F0L, // autopilot config callback
        0x00088340L, // vehicle config check/apply owner
        0x00095354L, // comparator family
        0x000771B4L  // command 0x32 front end
    };
    private static final String[] ROOT_NAMES = {
        "AUTOPILOT_CONFIG_CALLBACK",
        "VEHICLE_CONFIG_CHECK",
        "CONFIG_COMPARATOR",
        "COMMAND32_FRONTEND"
    };

    private static final int MAX_BACK = 120;
    private static final int MAX_REVERSE_DEPTH = 5;
    private static final int DECOMPILE_TIMEOUT_SECONDS = 45;

    private static final Pattern MEM_PATTERN = Pattern.compile(
        "(-?0x[0-9a-fA-F]+|-?[0-9]+)\\s*\\(\\s*(r(?:[12]?\\d|3[01]|[0-9]))\\s*\\)",
        Pattern.CASE_INSENSITIVE);

    private Listing listing;
    private Memory memory;
    private FunctionManager functions;
    private DecompInterface decompiler;
    private File outputDirectory;
    private String stem;

    private final Map<Long, Function> functionByEntry = new LinkedHashMap<Long, Function>();
    private final Map<Long, Set<Long>> callees = new LinkedHashMap<Long, Set<Long>>();
    private final Map<Long, Set<Long>> callers = new LinkedHashMap<Long, Set<Long>>();

    private final List<String[]> scopeRows = new ArrayList<String[]>();
    private final List<String[]> accessRows = new ArrayList<String[]>();
    private final List<String[]> bulkRows = new ArrayList<String[]>();
    private final List<String[]> pointerRows = new ArrayList<String[]>();
    private final List<String[]> ownerRows = new ArrayList<String[]>();
    private final List<String[]> pathRows = new ArrayList<String[]>();
    private final List<String[]> assessmentRows = new ArrayList<String[]>();
    private final List<String[]> errorRows = new ArrayList<String[]>();

    private final Map<Long, int[]> ownerCounts = new LinkedHashMap<Long, int[]>();
    private final Set<Long> candidateOwners = new LinkedHashSet<Long>();
    private final Set<Long> selectedFunctions = new LinkedHashSet<Long>();

    private int gateDirectWriters;
    private int objectWriterOwners;
    private int bulkSpanCandidates;
    private int rootPathCount;

    private static class MemOp {
        long displacement;
        String base;
    }

    private static class ReverseNode {
        final long entry;
        final int depth;
        final List<Long> path;
        ReverseNode(long entry, int depth, List<Long> path) {
            this.entry = entry;
            this.depth = depth;
            this.path = path;
        }
    }

    @Override
    public void run() throws Exception {
        listing = currentProgram.getListing();
        memory = currentProgram.getMemory();
        functions = currentProgram.getFunctionManager();
        outputDirectory = askDirectory("Select V368 output directory", "Select");
        if (outputDirectory == null) return;

        stem = SCRIPT_NAME + "_" +
            new SimpleDateFormat("yyyyMMdd_HHmmss").format(new Date());
        decompiler = new DecompInterface();
        decompiler.openProgram(currentProgram);

        try {
            emitScope();
            indexFunctions();
            scanObjectAccesses();
            scanBulkCallArguments();
            scanRawPointerOccurrences();
            buildOwnerSummary();
            buildReverseRootPaths();
            buildAssessment();
            writeOutputs();
        }
        catch (Throwable t) {
            errorRows.add(new String[]{"run", t.getClass().getSimpleName(), safe(t)});
            buildAssessment();
            writeOutputs();
        }
        finally {
            if (decompiler != null) decompiler.dispose();
        }
    }

    private void emitScope() {
        scopeRows.add(new String[]{"PROGRAM", currentProgram.getName(), "READ_ONLY"});
        scopeRows.add(new String[]{"LANGUAGE", currentProgram.getLanguageID().toString(), "EXPECTED_POWERPC_BE_VLE"});
        scopeRows.add(new String[]{"VISIBLE_GATE", hex(GATE), "V367_CONSUMER_VALIDATED"});
        scopeRows.add(new String[]{"OBJECT_WINDOW", hex(OBJECT_START) + ".." + hex(OBJECT_END), "ONLY_WIDENING_NEEDED_TO_FIND_STRUCTURE_OR_BULK_WRITES"});
        scopeRows.add(new String[]{"GATE_WORD", hex(GATE_WORD), "WHOLE_WORD_WRITE_CONTROL"});
        scopeRows.add(new String[]{"EXCLUSION", "AP-trial 0x4004AA1C / AA34 / 0x7C03E owner", "ALREADY_ANALYSED"});
    }

    private void indexFunctions() {
        FunctionIterator it = listing.getFunctions(true);
        while (it.hasNext()) {
            Function f = it.next();
            long e = f.getEntryPoint().getOffset();
            functionByEntry.put(Long.valueOf(e), f);
            callees.put(Long.valueOf(e), new LinkedHashSet<Long>());
            callers.put(Long.valueOf(e), new LinkedHashSet<Long>());
        }
        for (Function f : functionByEntry.values()) {
            long e = f.getEntryPoint().getOffset();
            InstructionIterator ii = listing.getInstructions(f.getBody(), true);
            while (ii.hasNext()) {
                Instruction ins = ii.next();
                if (ins.getFlowType() == null || !ins.getFlowType().isCall()) continue;
                for (Address flow : ins.getFlows()) {
                    if (flow == null) continue;
                    Function c = functions.getFunctionAt(flow);
                    if (c == null) c = functions.getFunctionContaining(flow);
                    if (c == null) continue;
                    long ce = c.getEntryPoint().getOffset();
                    callees.get(Long.valueOf(e)).add(Long.valueOf(ce));
                    Set<Long> reverse = callers.get(Long.valueOf(ce));
                    if (reverse != null) reverse.add(Long.valueOf(e));
                }
            }
        }
    }

    private void scanObjectAccesses() {
        FunctionIterator it = listing.getFunctions(true);
        while (it.hasNext() && !monitor.isCancelled()) {
            Function owner = it.next();
            InstructionIterator ii = listing.getInstructions(owner.getBody(), true);
            while (ii.hasNext()) {
                Instruction ins = ii.next();
                String m = lower(ins.getMnemonicString());
                boolean load = isLoad(m), store = isStore(m);
                if (!load && !store) continue;
                int width = width(m);
                String kind = store ? "WRITE" : "READ";

                boolean emitted = false;
                for (Reference r : ins.getReferencesFrom()) {
                    if (r.getToAddress() == null) continue;
                    long target = r.getToAddress().getOffset();
                    if (!overlaps(target, width, OBJECT_START, OBJECT_END)) continue;
                    recordAccess(owner, ins, kind, width, target, "DIRECT_REFERENCE");
                    emitted = true;
                }

                Long ea = effectiveAddress(owner, ins);
                if (ea != null && overlaps(ea.longValue(), width, OBJECT_START, OBJECT_END)) {
                    if (!emitted || !hasSameTargetReference(ins, ea.longValue())) {
                        recordAccess(owner, ins, kind, width, ea.longValue(), "COMPUTED_EA");
                    }
                }
            }
        }
    }

    private void recordAccess(Function owner, Instruction ins, String kind,
                              int width, long target, String evidence) {
        long entry = owner.getEntryPoint().getOffset();
        boolean gateOverlap = overlaps(target, width, GATE, GATE);
        accessRows.add(new String[]{
            hex(entry), owner.getName(), hex(ins.getAddress().getOffset()), kind,
            Integer.toString(width), hex(target), gateOverlap ? "YES" : "NO",
            evidence, ins.toString()
        });

        int[] counts = ownerCounts.get(Long.valueOf(entry));
        if (counts == null) {
            counts = new int[4];
            ownerCounts.put(Long.valueOf(entry), counts);
        }
        if ("WRITE".equals(kind)) {
            counts[0]++;
            if (gateOverlap) {
                counts[2]++;
                gateDirectWriters++;
            }
            candidateOwners.add(Long.valueOf(entry));
            selectedFunctions.add(Long.valueOf(entry));
        }
        else {
            counts[1]++;
        }
        counts[3]++;
    }

    private void scanBulkCallArguments() {
        for (Function owner : functionByEntry.values()) {
            InstructionIterator ii = listing.getInstructions(owner.getBody(), true);
            while (ii.hasNext()) {
                Instruction call = ii.next();
                if (call.getFlowType() == null || !call.getFlowType().isCall()) continue;

                Long r3 = resolveRegister(owner, call, "r3", MAX_BACK, new HashSet<String>());
                Long r4 = resolveRegister(owner, call, "r4", MAX_BACK, new HashSet<String>());
                Long r5 = resolveRegister(owner, call, "r5", MAX_BACK, new HashSet<String>());

                boolean objectArg = inObject(r3) || inObject(r4);
                boolean spans = false;
                if (r3 != null && r5 != null && r5.longValue() > 0L && r5.longValue() <= 0x10000L) {
                    long start = u32(r3.longValue());
                    long len = r5.longValue() & 0xffffffffL;
                    long end = u32(start + len - 1L);
                    spans = Long.compareUnsigned(start, GATE) <= 0 &&
                        Long.compareUnsigned(end, GATE) >= 0;
                }
                if (!objectArg && !spans) continue;

                String semantics;
                if (spans && r4 != null && (r4.longValue() & 0xffffffffL) <= 0xffL) {
                    semantics = "MEMSET_LIKE_ARGUMENT_SHAPE";
                }
                else if (spans && r4 != null && looksPointer(r4.longValue())) {
                    semantics = "MEMCPY_OR_STRUCTURE_COPY_ARGUMENT_SHAPE";
                }
                else if (spans) {
                    semantics = "DESTINATION_RANGE_SPANS_GATE";
                }
                else {
                    semantics = "OBJECT_POINTER_ARGUMENT";
                }

                String target = "";
                Function callee = null;
                for (Address flow : call.getFlows()) {
                    if (flow == null) continue;
                    callee = functions.getFunctionAt(flow);
                    if (callee == null) callee = functions.getFunctionContaining(flow);
                    if (callee != null) {
                        target = hex(callee.getEntryPoint().getOffset()) + ":" + callee.getName();
                        selectedFunctions.add(Long.valueOf(callee.getEntryPoint().getOffset()));
                        break;
                    }
                }

                if (spans) bulkSpanCandidates++;
                long ownerEntry = owner.getEntryPoint().getOffset();
                candidateOwners.add(Long.valueOf(ownerEntry));
                selectedFunctions.add(Long.valueOf(ownerEntry));

                bulkRows.add(new String[]{
                    hex(ownerEntry), owner.getName(), hex(call.getAddress().getOffset()),
                    target, value(r3), value(r4), value(r5),
                    spans ? "YES" : "NO", semantics, call.toString()
                });
            }
        }
    }

    private void scanRawPointerOccurrences() {
        long[] targets = { OBJECT_START, GATE_WORD, GATE };
        String[] labels = { "OBJECT_START", "GATE_WORD", "VISIBLE_GATE" };
        for (int ti = 0; ti < targets.length; ti++) {
            byte[] needle = u32be(targets[ti]);
            for (MemoryBlock block : memory.getBlocks()) {
                if (!block.isInitialized() || !block.isRead()) continue;
                long span = block.getEnd().getOffset() - block.getStart().getOffset();
                if (span > 0x01000000L) continue;
                Address cursor = block.getStart();
                while (cursor != null && !monitor.isCancelled()) {
                    Address found = memory.findBytes(cursor, needle, null, true, monitor);
                    if (found == null || Long.compareUnsigned(found.getOffset(), block.getEnd().getOffset()) > 0) break;
                    Instruction ins = listing.getInstructionContaining(found);
                    Function owner = functions.getFunctionContaining(found);
                    pointerRows.add(new String[]{
                        labels[ti], hex(targets[ti]), hex(found.getOffset()), block.getName(),
                        owner == null ? "" : hex(owner.getEntryPoint().getOffset()),
                        ins == null ? "" : ins.toString()
                    });
                    try { cursor = found.add(1L); } catch (Throwable t) { break; }
                }
            }
        }
    }

    private void buildOwnerSummary() {
        for (Map.Entry<Long, int[]> e : ownerCounts.entrySet()) {
            int[] c = e.getValue();
            if (c[0] <= 0) continue;
            objectWriterOwners++;
            Function f = functionByEntry.get(e.getKey());
            ownerRows.add(new String[]{
                hex(e.getKey().longValue()), f == null ? "" : f.getName(),
                Integer.toString(c[0]), Integer.toString(c[1]),
                Integer.toString(c[2]), Integer.toString(c[3]),
                c[2] > 0 ? "DIRECT_GATE_WRITER_OWNER" : "NEIGHBOUR_OBJECT_WRITER_OWNER"
            });
        }
    }

    private void buildReverseRootPaths() {
        Map<Long, String> roots = new LinkedHashMap<Long, String>();
        for (int i = 0; i < ROOT_SITES.length; i++) {
            Function f = functions.getFunctionContaining(address(ROOT_SITES[i]));
            if (f == null) f = functions.getFunctionAt(address(ROOT_SITES[i]));
            if (f != null) roots.put(Long.valueOf(f.getEntryPoint().getOffset()), ROOT_NAMES[i]);
        }

        for (Long source : candidateOwners) {
            Queue<ReverseNode> q = new ArrayDeque<ReverseNode>();
            Set<Long> seen = new LinkedHashSet<Long>();
            List<Long> first = new ArrayList<Long>();
            first.add(source);
            q.add(new ReverseNode(source.longValue(), 0, first));
            seen.add(source);

            while (!q.isEmpty()) {
                ReverseNode n = q.remove();
                if (n.depth >= MAX_REVERSE_DEPTH) continue;
                Set<Long> cs = callers.get(Long.valueOf(n.entry));
                if (cs == null) continue;
                for (Long caller : cs) {
                    List<Long> path = new ArrayList<Long>(n.path);
                    path.add(caller);
                    if (roots.containsKey(caller)) {
                        rootPathCount++;
                        Collections.reverse(path);
                        pathRows.add(new String[]{
                            roots.get(caller), hex(caller.longValue()), hex(source.longValue()),
                            Integer.toString(n.depth + 1), pathText(path),
                            "ROOT_TO_OBJECT_OR_BULK_WRITER_REACHABILITY"
                        });
                    }
                    if (seen.add(caller)) q.add(new ReverseNode(caller.longValue(), n.depth + 1, path));
                }
            }
        }
    }

    private void buildAssessment() {
        String classification;
        String note;
        if (gateDirectWriters > 0) {
            classification = "DIRECT_VISIBLE_GATE_WRITER_RECOVERED";
            note = "Review the direct writer owner and its incoming root path before broadening further.";
        }
        else if (bulkSpanCandidates > 0) {
            classification = "BULK_OR_STRUCTURE_WRITE_CAN_SPAN_VISIBLE_GATE";
            note = "At least one call has destination/length arguments whose range includes 0x40046F57. Review callee semantics and source pointer.";
        }
        else if (objectWriterOwners > 0) {
            classification = "VISIBLE_GATE_OBJECT_OWNER_NARROWED_BUT_GATE_POPULATION_INDIRECT";
            note = "Neighbouring fields have defined writers, but no direct store or resolved bulk destination spans the gate.";
        }
        else {
            classification = "VISIBLE_GATE_ORIGIN_REMAINS_OUTSIDE_DEFINED_MAIN_CORE_WRITES";
            note = "No direct or bulk defined-code origin was recovered. Remaining possibilities are startup/undefined code, secondary-core/DMA, or an unresolved computed destination.";
        }
        assessmentRows.add(new String[]{
            classification,
            Integer.toString(gateDirectWriters),
            Integer.toString(objectWriterOwners),
            Integer.toString(bulkSpanCandidates),
            Integer.toString(candidateOwners.size()),
            Integer.toString(rootPathCount),
            Integer.toString(errorRows.size()),
            note
        });
    }

    private Long effectiveAddress(Function owner, Instruction ins) {
        MemOp op = parseMem(ins);
        if (op == null) return null;
        Long base = resolveRegister(owner, ins, op.base, MAX_BACK, new HashSet<String>());
        return base == null ? null : Long.valueOf(u32(base.longValue() + op.displacement));
    }

    private Long resolveRegister(Function owner, Instruction before, String register,
                                 int maximum, Set<String> guard) {
        if (owner == null || before == null || register == null || maximum <= 0) return null;
        String tracked = lower(register);
        String key = hex(owner.getEntryPoint().getOffset()) + ":" + hex(before.getAddress().getOffset()) + ":" + tracked + ":" + maximum;
        if (!guard.add(key)) return null;
        long additive = 0L;
        Instruction cursor = before;
        int count = 0;
        while (count++ < maximum) {
            cursor = previous(owner, cursor);
            if (cursor == null) break;
            if (!writesRegister(cursor, tracked)) continue;
            String m = lower(cursor.getMnemonicString());
            if (m.equals("lis") || m.equals("e_lis") || m.endsWith("_lis")) {
                Long v = firstScalar(cursor, true);
                return v == null ? null : Long.valueOf(u32(((v.longValue() & 0xffffL) << 16) + additive));
            }
            if (m.equals("li") || m.equals("e_li") || m.equals("se_li") || m.endsWith("_li")) {
                Long v = firstScalar(cursor, true);
                return v == null ? null : Long.valueOf(u32(v.longValue() + additive));
            }
            if (m.contains("add16i") || m.equals("addi") || m.equals("e_addi") || m.equals("se_addi") || m.equals("addic") || m.equals("addic.")) {
                String src = firstRegisterAfter(cursor, 0);
                Long imm = lastScalar(cursor, true);
                if (src == null || imm == null) return null;
                additive += imm.longValue();
                tracked = src;
                continue;
            }
            if (m.equals("addis") || m.equals("e_addis")) {
                String src = firstRegisterAfter(cursor, 0);
                Long imm = lastScalar(cursor, true);
                if (src == null || imm == null) return null;
                additive += (imm.longValue() & 0xffffL) << 16;
                tracked = src;
                continue;
            }
            if (isMove(m)) {
                String src = firstRegisterAfter(cursor, 0);
                if (src == null) return null;
                tracked = src;
                continue;
            }
            return null;
        }
        return null;
    }

    private MemOp parseMem(Instruction ins) {
        Matcher m = MEM_PATTERN.matcher(ins.toString());
        if (!m.find()) return null;
        try {
            MemOp op = new MemOp();
            op.displacement = parseNumber(m.group(1));
            op.base = lower(m.group(2));
            return op;
        }
        catch (Throwable t) { return null; }
    }

    private boolean hasSameTargetReference(Instruction ins, long target) {
        for (Reference r : ins.getReferencesFrom()) {
            if (r.getToAddress() != null && r.getToAddress().getOffset() == target) return true;
        }
        return false;
    }

    private boolean inObject(Long value) {
        if (value == null) return false;
        long v = u32(value.longValue());
        return Long.compareUnsigned(v, OBJECT_START) >= 0 && Long.compareUnsigned(v, OBJECT_END) <= 0;
    }

    private boolean looksPointer(long value) {
        long v = u32(value);
        return (v >= 0x00020000L && v <= 0x001fffffL) || (v >= 0x40000000L && v <= 0x400fffffL);
    }

    private boolean overlaps(long start, int width, long wantedStart, long wantedEnd) {
        if (width <= 0) return false;
        long end = u32(start + width - 1L);
        return Long.compareUnsigned(start, wantedEnd) <= 0 && Long.compareUnsigned(end, wantedStart) >= 0;
    }

    private boolean isLoad(String m) {
        return m.contains("lbz") || m.contains("lhz") || m.contains("lha") || m.contains("lwz") || m.equals("ld") || m.endsWith("_ld");
    }
    private boolean isStore(String m) {
        return m.contains("stb") || m.contains("sth") || m.contains("stw") || m.equals("std") || m.endsWith("_std");
    }
    private boolean isMove(String m) {
        return m.equals("mr") || m.equals("se_mr") || m.endsWith("_mr");
    }
    private int width(String m) {
        if (m.contains("lbz") || m.contains("stb")) return 1;
        if (m.contains("lhz") || m.contains("lha") || m.contains("sth")) return 2;
        if (m.equals("ld") || m.equals("std") || m.endsWith("_ld") || m.endsWith("_std")) return 8;
        return 4;
    }

    private Instruction previous(Function owner, Instruction ins) {
        Instruction p = ins == null ? null : ins.getPrevious();
        if (p == null) return null;
        Function po = functions.getFunctionContaining(p.getAddress());
        return po != null && po.getEntryPoint().getOffset() == owner.getEntryPoint().getOffset() ? p : null;
    }

    private boolean writesRegister(Instruction ins, String name) {
        Object[] results = ins.getResultObjects();
        if (results == null) return false;
        for (Object o : results) if (o instanceof Register && name.equalsIgnoreCase(((Register)o).getName())) return true;
        return false;
    }

    private String firstRegister(Instruction ins, int operand) {
        if (operand < 0 || operand >= ins.getNumOperands()) return null;
        for (Object o : ins.getOpObjects(operand)) if (o instanceof Register) return lower(((Register)o).getName());
        return null;
    }
    private String firstRegisterAfter(Instruction ins, int operand) {
        for (int i = operand + 1; i < ins.getNumOperands(); i++) {
            String r = firstRegister(ins, i);
            if (r != null) return r;
        }
        return null;
    }
    private Long firstScalar(Instruction ins, boolean signed) {
        for (int i = 0; i < ins.getNumOperands(); i++) for (Object o : ins.getOpObjects(i)) if (o instanceof Scalar) {
            Scalar s = (Scalar)o;
            return Long.valueOf(signed ? s.getSignedValue() : s.getUnsignedValue());
        }
        return null;
    }
    private Long lastScalar(Instruction ins, boolean signed) {
        Long v = null;
        for (int i = 0; i < ins.getNumOperands(); i++) for (Object o : ins.getOpObjects(i)) if (o instanceof Scalar) {
            Scalar s = (Scalar)o;
            v = Long.valueOf(signed ? s.getSignedValue() : s.getUnsignedValue());
        }
        return v;
    }

    private long parseNumber(String text) {
        String s = text.trim().toLowerCase(Locale.ROOT);
        boolean neg = s.startsWith("-");
        if (neg || s.startsWith("+")) s = s.substring(1);
        long v = s.startsWith("0x") ? Long.parseLong(s.substring(2), 16) : Long.parseLong(s, 10);
        return neg ? -v : v;
    }

    private String value(Long v) { return v == null ? "" : hex(v.longValue()); }
    private long u32(long v) { return v & 0xffffffffL; }
    private Address address(long v) { return currentProgram.getAddressFactory().getDefaultAddressSpace().getAddress(u32(v)); }
    private String hex(long v) { return String.format(Locale.ROOT, "0x%08X", u32(v)); }
    private String lower(String s) { return s == null ? "" : s.toLowerCase(Locale.ROOT); }
    private String safe(Throwable t) { return t.getMessage() == null ? t.toString() : t.getMessage(); }

    private byte[] u32be(long v) {
        return new byte[]{(byte)(v >>> 24), (byte)(v >>> 16), (byte)(v >>> 8), (byte)v};
    }

    private String pathText(List<Long> path) {
        StringBuilder b = new StringBuilder();
        for (Long v : path) { if (b.length() > 0) b.append(" -> "); b.append(hex(v.longValue())); }
        return b.toString();
    }

    private void writeOutputs() throws Exception {
        List<File> filesOut = new ArrayList<File>();
        filesOut.add(writeCsv(stem + "_scope_contract.csv", new String[]{"item","value","meaning"}, scopeRows));
        filesOut.add(writeCsv(stem + "_object_accesses.csv", new String[]{"owner","owner_name","site","kind","width","target","gate_overlap","evidence","instruction"}, accessRows));
        filesOut.add(writeCsv(stem + "_bulk_call_arguments.csv", new String[]{"owner","owner_name","callsite","callee","r3","r4","r5","spans_gate","classification","instruction"}, bulkRows));
        filesOut.add(writeCsv(stem + "_raw_pointer_occurrences.csv", new String[]{"label","value","location","block","function_owner","instruction"}, pointerRows));
        filesOut.add(writeCsv(stem + "_object_writer_owners.csv", new String[]{"owner","owner_name","writes","reads","gate_writes","accesses","classification"}, ownerRows));
        filesOut.add(writeCsv(stem + "_known_root_to_candidate_paths.csv", new String[]{"root","root_owner","candidate_owner","depth","path","classification"}, pathRows));
        filesOut.add(writeCsv(stem + "_assessment.csv", new String[]{"classification","direct_gate_writers","object_writer_owners","bulk_span_candidates","candidate_owners","known_root_paths","errors","note"}, assessmentRows));
        filesOut.add(writeCsv(stem + "_errors.csv", new String[]{"stage","type","detail"}, errorRows));
        filesOut.add(writeDecomp());
        filesOut.add(writeSummary());
        File bundle = new File(outputDirectory, stem + "_bundle.zip");
        zip(bundle, filesOut);
        println("V368 complete: " + bundle.getAbsolutePath());
    }

    private File writeDecomp() throws Exception {
        File f = new File(outputDirectory, stem + "_selected_decompilation.txt");
        BufferedWriter w = writer(f);
        try {
            List<Long> entries = new ArrayList<Long>(selectedFunctions);
            Collections.sort(entries, new Comparator<Long>() {
                public int compare(Long a, Long b) { return Long.compareUnsigned(a.longValue(), b.longValue()); }
            });
            for (Long e : entries) {
                Function fn = functionByEntry.get(e);
                if (fn == null) continue;
                w.write("============================================================\n" + hex(e.longValue()) + " " + fn.getName() + "\n============================================================\n\n");
                try {
                    DecompileResults r = decompiler.decompileFunction(fn, DECOMPILE_TIMEOUT_SECONDS, monitor);
                    w.write(r != null && r.decompileCompleted() && r.getDecompiledFunction() != null ? r.getDecompiledFunction().getC() : "Decompilation unavailable.\n");
                } catch (Throwable t) { w.write("Decompilation error: " + t + "\n"); }
                w.write("\n\n");
            }
        } finally { w.close(); }
        return f;
    }

    private File writeSummary() throws Exception {
        File f = new File(outputDirectory, stem + "_summary.md");
        BufferedWriter w = writer(f);
        try {
            String c = assessmentRows.isEmpty() ? "NO_ASSESSMENT" : assessmentRows.get(assessmentRows.size()-1)[0];
            w.write("# " + SCRIPT_NAME + "\n\n");
            w.write("- Program: `" + currentProgram.getName() + "`\n");
            w.write("- Object window: `" + hex(OBJECT_START) + ".." + hex(OBJECT_END) + "`\n");
            w.write("- Direct gate writers: `" + gateDirectWriters + "`\n");
            w.write("- Object writer owners: `" + objectWriterOwners + "`\n");
            w.write("- Bulk destination ranges spanning gate: `" + bulkSpanCandidates + "`\n");
            w.write("- Known root paths: `" + rootPathCount + "`\n");
            w.write("- Errors: `" + errorRows.size() + "`\n");
            w.write("- Classification: `" + c + "`\n\n");
            w.write("This pass is intentionally limited to recovering how the containing state object is populated. It does not revisit AP-trial, AA34, queue diagnostics, or the exhausted 0x7C03E static-owner route.\n");
        } finally { w.close(); }
        return f;
    }

    private File writeCsv(String name, String[] header, List<String[]> rows) throws Exception {
        File f = new File(outputDirectory, name);
        BufferedWriter w = writer(f);
        try {
            w.write(csv(header)); w.write("\r\n");
            for (String[] row : rows) { w.write(csv(row)); w.write("\r\n"); }
        } finally { w.close(); }
        return f;
    }

    private BufferedWriter writer(File f) throws Exception {
        return new BufferedWriter(new OutputStreamWriter(new FileOutputStream(f), StandardCharsets.UTF_8));
    }

    private String csv(String[] values) {
        StringBuilder b = new StringBuilder();
        for (int i = 0; i < values.length; i++) {
            if (i > 0) b.append(',');
            String v = values[i] == null ? "" : values[i].replace("\"", "\"\"");
            b.append('"').append(v).append('"');
        }
        return b.toString();
    }

    private void zip(File bundle, List<File> filesOut) throws Exception {
        ZipOutputStream z = new ZipOutputStream(new FileOutputStream(bundle));
        try {
            byte[] buffer = new byte[65536];
            for (File f : filesOut) {
                z.putNextEntry(new ZipEntry(f.getName()));
                FileInputStream in = new FileInputStream(f);
                try { int n; while ((n = in.read(buffer)) >= 0) if (n > 0) z.write(buffer, 0, n); }
                finally { in.close(); }
                z.closeEntry();
            }
        } finally { z.close(); }
    }
}