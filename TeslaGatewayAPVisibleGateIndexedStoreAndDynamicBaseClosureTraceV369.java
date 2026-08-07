// TeslaGatewayAPVisibleGateIndexedStoreAndDynamicBaseClosureTraceV369.java
//
// Read-only follow-up to V368.
//
// V368 found 13 writers to neighbouring bytes in 0x40046F40..0x40046F8F,
// but no direct write to 0x40046F57 and no memcpy/memset-like destination range
// spanning the gate. Two root paths were only to neighbouring fields.
//
// V369 closes the remaining defined-main-core addressing gap only:
//   - indexed stores (stbx/sthx/stwx and VLE variants),
//   - computed base+index stores where the base resolves near 0x40046F57,
//   - pointer-update/self-increment stores whose exact EA was not recovered by V368,
//   - High-P-code STORE address expressions in the V368 writer-owner set.
//
// It does not revisit AP-trial, AA34, the 0x7C03E owner search, queue failure,
// generic action scans, or reset suppression.
//
// No database changes. No disassembly creation. No firmware modification/export.
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
import ghidra.program.model.pcode.HighFunction;
import ghidra.program.model.pcode.PcodeOp;
import ghidra.program.model.pcode.PcodeOpAST;
import ghidra.program.model.pcode.Varnode;
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
import java.util.Iterator;
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

public class TeslaGatewayAPVisibleGateIndexedStoreAndDynamicBaseClosureTraceV369
        extends GhidraScript {

    private static final String SCRIPT_NAME =
        "TeslaGatewayAPVisibleGateIndexedStoreAndDynamicBaseClosureTraceV369";

    private static final long GATE = 0x40046F57L;
    private static final long NARROW_START = 0x40046F50L;
    private static final long NARROW_END = 0x40046F5FL;
    private static final long OBJECT_START = 0x40046F40L;
    private static final long OBJECT_END = 0x40046F8FL;
    private static final long NEAR_BASE_START = 0x40046E00L;
    private static final long NEAR_BASE_END = 0x400470FFL;

    private static final long[] V368_OWNER_SEEDS = {
        0x0007E09CL, 0x0007E1C6L, 0x0007EC98L, 0x0007F288L,
        0x0007FECEL, 0x00080110L, 0x0008162EL, 0x000829C4L,
        0x00082FCCL, 0x000831F8L, 0x00083B28L, 0x00088340L,
        0x000FBD2CL
    };

    private static final long[] ROOT_SITES = {
        0x000771B4L, 0x00088340L, 0x000870F0L, 0x00095354L
    };
    private static final String[] ROOT_NAMES = {
        "COMMAND32_FRONTEND", "VEHICLE_CONFIG_CHECK",
        "AUTOPILOT_CONFIG_CALLBACK", "CONFIG_COMPARATOR"
    };

    private static final int MAX_BACK = 140;
    private static final int CONTEXT_BEFORE = 18;
    private static final int CONTEXT_AFTER = 10;
    private static final int MAX_CALL_DEPTH = 5;
    private static final int DECOMPILE_TIMEOUT_SECONDS = 45;
    private static final int MAX_PCODE_DEPTH = 16;

    private static final Pattern REGISTER_PATTERN = Pattern.compile(
        "\\br(?:[12]?\\d|3[01]|[0-9])\\b", Pattern.CASE_INSENSITIVE);
    private static final Pattern MEM_PATTERN = Pattern.compile(
        "(-?0x[0-9a-fA-F]+|-?[0-9]+)\\s*\\(\\s*(r(?:[12]?\\d|3[01]|[0-9]))\\s*\\)",
        Pattern.CASE_INSENSITIVE);

    private Listing listing;
    private FunctionManager functions;
    private DecompInterface decompiler;
    private File outputDirectory;
    private String stem;

    private final Map<Long, Function> byEntry = new LinkedHashMap<Long, Function>();
    private final Map<Long, Set<Long>> callees = new LinkedHashMap<Long, Set<Long>>();
    private final Set<Long> candidateOwners = new LinkedHashSet<Long>();
    private final Set<Long> selectedFunctions = new LinkedHashSet<Long>();

    private final List<String[]> scopeRows = new ArrayList<String[]>();
    private final List<String[]> narrowRows = new ArrayList<String[]>();
    private final List<String[]> indexedRows = new ArrayList<String[]>();
    private final List<String[]> updateRows = new ArrayList<String[]>();
    private final List<String[]> pcodeRows = new ArrayList<String[]>();
    private final List<String[]> pathRows = new ArrayList<String[]>();
    private final List<String[]> assessmentRows = new ArrayList<String[]>();
    private final List<String[]> errorRows = new ArrayList<String[]>();

    private int exactDynamicGateWrites;
    private int indexedNearBaseCandidates;
    private int pointerUpdateCandidates;
    private int highPcodeExactGateWrites;
    private int highPcodeDynamicCandidates;
    private int rootPathCount;

    private static class MemOp {
        long displacement;
        String base;
    }

    private static class Affine {
        boolean known;
        long value;
        boolean dynamic;
        String expression;

        static Affine unknown(String text) {
            Affine a = new Affine();
            a.known = false;
            a.dynamic = true;
            a.expression = text == null ? "UNKNOWN" : text;
            return a;
        }

        static Affine constant(long value, String text) {
            Affine a = new Affine();
            a.known = true;
            a.value = value & 0xffffffffL;
            a.dynamic = false;
            a.expression = text;
            return a;
        }
    }

    private static class CallNode {
        final long entry;
        final int depth;
        final List<Long> path;
        CallNode(long entry, int depth, List<Long> path) {
            this.entry = entry;
            this.depth = depth;
            this.path = path;
        }
    }

    @Override
    public void run() throws Exception {
        listing = currentProgram.getListing();
        functions = currentProgram.getFunctionManager();
        outputDirectory = askDirectory("Select V369 output directory", "Select");
        if (outputDirectory == null) return;

        stem = SCRIPT_NAME + "_" +
            new SimpleDateFormat("yyyyMMdd_HHmmss").format(new Date());

        decompiler = new DecompInterface();
        decompiler.openProgram(currentProgram);

        try {
            emitScope();
            indexFunctions();
            scanNarrowDirectAccesses();
            scanIndexedAndUpdateStores();
            analyseHighPcodeForSeedOwners();
            buildRootPaths();
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
        scopeRows.add(new String[]{"NARROW_WINDOW", hex(NARROW_START) + ".." + hex(NARROW_END), "V369_DYNAMIC_ADDRESS_FOCUS"});
        scopeRows.add(new String[]{"V368_RESULT", "VISIBLE_GATE_OBJECT_OWNER_NARROWED_BUT_GATE_POPULATION_INDIRECT", "0 direct writers; 13 neighbouring writer owners; 0 bulk spans"});
        scopeRows.add(new String[]{"NEW_SCOPE", "INDEXED_STORE_POINTER_UPDATE_HIGH_PCODE_STORE_ADDRESS", "NOT_REPEATING_V368_DISPLACEMENT_BASE_OR_R3_R4_R5_BULK_SCAN"});
        scopeRows.add(new String[]{"EXCLUSION", "AP-trial / AA34 / 0x7C03E owner / reset suppression", "PREVIOUSLY_ANALYSED"});
    }

    private void indexFunctions() {
        FunctionIterator it = listing.getFunctions(true);
        while (it.hasNext()) {
            Function f = it.next();
            long e = f.getEntryPoint().getOffset();
            byEntry.put(Long.valueOf(e), f);
            callees.put(Long.valueOf(e), new LinkedHashSet<Long>());
        }

        for (Function f : byEntry.values()) {
            long e = f.getEntryPoint().getOffset();
            InstructionIterator ii = listing.getInstructions(f.getBody(), true);
            while (ii.hasNext()) {
                Instruction ins = ii.next();
                if (ins.getFlowType() == null || !ins.getFlowType().isCall()) continue;
                for (Address flow : ins.getFlows()) {
                    if (flow == null) continue;
                    Function c = functions.getFunctionAt(flow);
                    if (c == null) c = functions.getFunctionContaining(flow);
                    if (c != null) callees.get(Long.valueOf(e)).add(
                        Long.valueOf(c.getEntryPoint().getOffset()));
                }
            }
        }
    }

    private void scanNarrowDirectAccesses() {
        FunctionIterator it = listing.getFunctions(true);
        while (it.hasNext() && !monitor.isCancelled()) {
            Function owner = it.next();
            InstructionIterator ii = listing.getInstructions(owner.getBody(), true);
            while (ii.hasNext()) {
                Instruction ins = ii.next();
                String m = lower(ins.getMnemonicString());
                if (!isLoad(m) && !isStore(m)) continue;
                int w = width(m);
                for (Reference r : ins.getReferencesFrom()) {
                    Address to = r.getToAddress();
                    if (to == null) continue;
                    long target = to.getOffset();
                    if (!overlaps(target, w, NARROW_START, NARROW_END)) continue;
                    narrowRows.add(new String[]{
                        hex(owner.getEntryPoint().getOffset()), owner.getName(),
                        hex(ins.getAddress().getOffset()), isStore(m) ? "WRITE" : "READ",
                        Integer.toString(w), hex(target), r.getReferenceType().toString(),
                        ins.toString()
                    });
                }
            }
        }
    }

    private void scanIndexedAndUpdateStores() {
        FunctionIterator it = listing.getFunctions(true);
        while (it.hasNext() && !monitor.isCancelled()) {
            Function owner = it.next();
            InstructionIterator ii = listing.getInstructions(owner.getBody(), true);
            while (ii.hasNext()) {
                Instruction ins = ii.next();
                String m = lower(ins.getMnemonicString());
                if (!isStore(m)) continue;

                List<String> regs = registers(ins);
                boolean indexed = looksIndexedStore(m, ins, regs);
                boolean update = looksUpdateStore(m);

                if (indexed && regs.size() >= 3) {
                    String valueReg = regs.get(0);
                    String baseReg = regs.get(1);
                    String indexReg = regs.get(2);
                    Long base = resolveRegister(owner, ins, baseReg, MAX_BACK,
                        new HashSet<String>());
                    Long index = resolveRegister(owner, ins, indexReg, MAX_BACK,
                        new HashSet<String>());
                    Long exact = base != null && index != null
                        ? Long.valueOf(u32(base.longValue() + index.longValue()))
                        : null;

                    boolean exactGate = exact != null &&
                        overlaps(exact.longValue(), width(m), GATE, GATE);
                    boolean nearBase = base != null &&
                        betweenUnsigned(base.longValue(), NEAR_BASE_START, NEAR_BASE_END);

                    if (!exactGate && !nearBase) continue;

                    if (exactGate) exactDynamicGateWrites++;
                    if (nearBase && exact == null) indexedNearBaseCandidates++;

                    long entry = owner.getEntryPoint().getOffset();
                    candidateOwners.add(Long.valueOf(entry));
                    selectedFunctions.add(Long.valueOf(entry));

                    indexedRows.add(new String[]{
                        hex(entry), owner.getName(), hex(ins.getAddress().getOffset()),
                        m, valueReg, baseReg, indexReg,
                        value(base), value(index), value(exact),
                        exactGate ? "EXACT_GATE_EA" : "NEAR_OBJECT_BASE_PLUS_DYNAMIC_INDEX",
                        indexEvidence(owner, ins, indexReg), ins.toString(),
                        context(ins, CONTEXT_BEFORE, CONTEXT_AFTER)
                    });
                }

                if (update) {
                    MemOp op = parseMem(ins);
                    if (op == null) continue;
                    Long base = resolveRegister(owner, ins, op.base, MAX_BACK,
                        new HashSet<String>());
                    if (base == null) continue;
                    long ea = u32(base.longValue() + op.displacement);
                    if (!betweenUnsigned(ea, NEAR_BASE_START, NEAR_BASE_END)) continue;

                    pointerUpdateCandidates++;
                    long entry = owner.getEntryPoint().getOffset();
                    candidateOwners.add(Long.valueOf(entry));
                    selectedFunctions.add(Long.valueOf(entry));
                    updateRows.add(new String[]{
                        hex(entry), owner.getName(), hex(ins.getAddress().getOffset()),
                        m, op.base, hex(base.longValue()), Long.toString(op.displacement),
                        hex(ea), overlaps(ea, width(m), GATE, GATE) ? "EXACT_GATE_EA" : "NEAR_OBJECT_POINTER_UPDATE",
                        ins.toString(), context(ins, CONTEXT_BEFORE, CONTEXT_AFTER)
                    });
                }
            }
        }
    }

    private boolean looksIndexedStore(String m, Instruction ins, List<String> regs) {
        if (regs.size() < 3) return false;
        return m.endsWith("x") || m.contains("stbx") || m.contains("sthx") ||
            m.contains("stwx") || m.contains("stdx");
    }

    private boolean looksUpdateStore(String m) {
        return m.contains("stbu") || m.contains("sthu") || m.contains("stwu") ||
            m.contains("stdu") || m.endsWith("_stu");
    }

    private String indexEvidence(Function owner, Instruction site, String indexReg) {
        List<String> evidence = new ArrayList<String>();
        Instruction cur = site;
        for (int i = 0; i < 28; i++) {
            cur = previous(owner, cur);
            if (cur == null) break;
            String text = lower(cur.toString());
            if (text.contains(lower(indexReg)) &&
                (text.contains("andi") || text.contains("clrl") || text.contains("rlwinm") ||
                 text.contains("cmp") || text.contains("cmpl") || text.contains("subi") ||
                 text.contains("addi"))) {
                evidence.add(0, hex(cur.getAddress().getOffset()) + ":" + cur.toString());
            }
        }
        return join(evidence, " | ");
    }

    private void analyseHighPcodeForSeedOwners() {
        Set<Long> seeds = new LinkedHashSet<Long>();
        for (long e : V368_OWNER_SEEDS) seeds.add(Long.valueOf(e));
        seeds.addAll(candidateOwners);

        for (Long requested : seeds) {
            if (monitor.isCancelled()) break;
            Function f = byEntry.get(requested);
            if (f == null) {
                f = functions.getFunctionContaining(address(requested.longValue()));
            }
            if (f == null) continue;

            long entry = f.getEntryPoint().getOffset();
            selectedFunctions.add(Long.valueOf(entry));

            try {
                DecompileResults results = decompiler.decompileFunction(
                    f, DECOMPILE_TIMEOUT_SECONDS, monitor);
                if (results == null || !results.decompileCompleted() ||
                    results.getHighFunction() == null) {
                    continue;
                }

                HighFunction hf = results.getHighFunction();
                Iterator<PcodeOpAST> ops = hf.getPcodeOps();
                while (ops.hasNext()) {
                    PcodeOpAST op = ops.next();
                    if (op.getOpcode() != PcodeOp.STORE || op.getNumInputs() < 3) continue;
                    Varnode addrNode = op.getInput(1);
                    Affine a = resolveAffine(addrNode, MAX_PCODE_DEPTH,
                        new HashSet<Varnode>());

                    boolean exactGate = a.known && !a.dynamic &&
                        a.value == GATE;
                    boolean exactNarrow = a.known && !a.dynamic &&
                        betweenUnsigned(a.value, NARROW_START, NARROW_END);
                    boolean dynamicNear = a.known && a.dynamic &&
                        betweenUnsigned(a.value, NEAR_BASE_START, NEAR_BASE_END);

                    if (!exactGate && !exactNarrow && !dynamicNear) continue;

                    if (exactGate) highPcodeExactGateWrites++;
                    if (dynamicNear) highPcodeDynamicCandidates++;
                    candidateOwners.add(Long.valueOf(entry));

                    Address site = op.getSeqnum() == null ? null : op.getSeqnum().getTarget();
                    pcodeRows.add(new String[]{
                        hex(entry), f.getName(), site == null ? "" : hex(site.getOffset()),
                        exactGate ? "EXACT_GATE_STORE" :
                            exactNarrow ? "EXACT_NARROW_STORE" : "DYNAMIC_NEAR_OBJECT_BASE",
                        a.known ? hex(a.value) : "", Boolean.toString(a.dynamic),
                        a.expression == null ? "" : a.expression,
                        op.toString()
                    });
                }
            }
            catch (Throwable t) {
                errorRows.add(new String[]{
                    "high_pcode_" + hex(entry), t.getClass().getSimpleName(), safe(t)
                });
            }
        }
    }

    private Affine resolveAffine(Varnode node, int depth, Set<Varnode> guard) {
        if (node == null || depth <= 0 || !guard.add(node)) return Affine.unknown("RECURSION_LIMIT");
        if (node.isConstant()) return Affine.constant(node.getOffset(), "CONST(" + hex(node.getOffset()) + ")");

        PcodeOp def = node.getDef();
        if (def == null) return Affine.unknown(node.toString());
        int code = def.getOpcode();

        if (code == PcodeOp.COPY || code == PcodeOp.CAST || code == PcodeOp.INT_ZEXT || code == PcodeOp.INT_SEXT) {
            return resolveAffine(def.getInput(0), depth - 1, guard);
        }

        if (code == PcodeOp.INT_ADD || code == PcodeOp.PTRSUB) {
            Affine a = resolveAffine(def.getInput(0), depth - 1, guard);
            Affine b = resolveAffine(def.getInput(1), depth - 1, guard);
            if (a.known && !a.dynamic && b.known && !b.dynamic) {
                return Affine.constant(u32(a.value + b.value), a.expression + "+" + b.expression);
            }
            if (a.known && !a.dynamic) {
                a.dynamic = true;
                a.expression = a.expression + "+DYNAMIC(" + b.expression + ")";
                return a;
            }
            if (b.known && !b.dynamic) {
                b.dynamic = true;
                b.expression = b.expression + "+DYNAMIC(" + a.expression + ")";
                return b;
            }
            return Affine.unknown("ADD_DYNAMIC");
        }

        if (code == PcodeOp.PTRADD && def.getNumInputs() >= 3) {
            Affine base = resolveAffine(def.getInput(0), depth - 1, guard);
            Affine index = resolveAffine(def.getInput(1), depth - 1, guard);
            Affine scale = resolveAffine(def.getInput(2), depth - 1, guard);
            if (base.known && !base.dynamic && index.known && !index.dynamic && scale.known && !scale.dynamic) {
                return Affine.constant(u32(base.value + index.value * scale.value),
                    base.expression + "+(" + index.expression + "*" + scale.expression + ")");
            }
            if (base.known && !base.dynamic) {
                base.dynamic = true;
                base.expression = base.expression + "+PTRADD_DYNAMIC";
                return base;
            }
            return Affine.unknown("PTRADD_DYNAMIC");
        }

        if (code == PcodeOp.MULTIEQUAL) {
            Long same = null;
            boolean anyDynamic = false;
            for (int i = 0; i < def.getNumInputs(); i++) {
                Affine a = resolveAffine(def.getInput(i), depth - 1,
                    new HashSet<Varnode>(guard));
                if (!a.known) return Affine.unknown("MULTIEQUAL_UNKNOWN");
                if (same == null) same = Long.valueOf(a.value);
                else if (same.longValue() != a.value) anyDynamic = true;
                anyDynamic |= a.dynamic;
            }
            if (same != null) {
                Affine out = Affine.constant(same.longValue(), "MULTIEQUAL_BASE");
                out.dynamic = anyDynamic;
                return out;
            }
        }

        return Affine.unknown(def.toString());
    }

    private void buildRootPaths() {
        Map<Long, String> roots = new LinkedHashMap<Long, String>();
        for (int i = 0; i < ROOT_SITES.length; i++) {
            Function f = functions.getFunctionContaining(address(ROOT_SITES[i]));
            if (f == null) f = functions.getFunctionAt(address(ROOT_SITES[i]));
            if (f != null) roots.put(Long.valueOf(f.getEntryPoint().getOffset()), ROOT_NAMES[i]);
        }

        for (Map.Entry<Long, String> root : roots.entrySet()) {
            Queue<CallNode> q = new ArrayDeque<CallNode>();
            Set<Long> seen = new LinkedHashSet<Long>();
            List<Long> first = new ArrayList<Long>();
            first.add(root.getKey());
            q.add(new CallNode(root.getKey().longValue(), 0, first));
            seen.add(root.getKey());

            while (!q.isEmpty()) {
                CallNode n = q.remove();
                if (n.depth >= MAX_CALL_DEPTH) continue;
                Set<Long> cs = callees.get(Long.valueOf(n.entry));
                if (cs == null) continue;
                for (Long c : cs) {
                    List<Long> p = new ArrayList<Long>(n.path);
                    p.add(c);
                    if (candidateOwners.contains(c)) {
                        rootPathCount++;
                        pathRows.add(new String[]{
                            root.getValue(), hex(root.getKey().longValue()), hex(c.longValue()),
                            Integer.toString(n.depth + 1), pathText(p),
                            "ROOT_TO_DYNAMIC_GATE_CANDIDATE_REACHABILITY"
                        });
                    }
                    if (seen.add(c)) q.add(new CallNode(c.longValue(), n.depth + 1, p));
                }
            }
        }
    }

    private void buildAssessment() {
        String classification;
        String note;
        if (exactDynamicGateWrites > 0 || highPcodeExactGateWrites > 0) {
            classification = "EXACT_DYNAMIC_VISIBLE_GATE_WRITER_RECOVERED";
            note = "A defined-main-core indexed or High-P-code STORE resolves exactly to 0x40046F57. Review that owner and predicate only.";
        }
        else if (indexedNearBaseCandidates > 0 || highPcodeDynamicCandidates > 0 || pointerUpdateCandidates > 0) {
            classification = "DYNAMIC_ADDRESS_WRITER_CANDIDATES_CAN_REACH_VISIBLE_GATE_REGION";
            note = "No exact gate writer was resolved, but dynamic/indexed address expressions are rooted near the object. Review index bounds and path predicates before attributing the gate.";
        }
        else {
            classification = "NO_DEFINED_MAIN_CORE_DYNAMIC_VISIBLE_GATE_WRITER_RECOVERED";
            note = "V368 displacement/base and bulk-copy searches plus V369 indexed/pointer-update/High-P-code searches found no defined-main-core producer. Remaining static origins are undefined/startup code, secondary core, DMA/shared-memory, or analysis gaps.";
        }

        assessmentRows.add(new String[]{
            classification,
            Integer.toString(exactDynamicGateWrites),
            Integer.toString(indexedNearBaseCandidates),
            Integer.toString(pointerUpdateCandidates),
            Integer.toString(highPcodeExactGateWrites),
            Integer.toString(highPcodeDynamicCandidates),
            Integer.toString(candidateOwners.size()),
            Integer.toString(rootPathCount),
            Integer.toString(errorRows.size()), note
        });
    }

    private Long resolveRegister(Function owner, Instruction before, String register,
                                 int maximum, Set<String> guard) {
        if (owner == null || before == null || register == null || maximum <= 0) return null;
        String tracked = lower(register);
        String key = hex(owner.getEntryPoint().getOffset()) + ":" +
            hex(before.getAddress().getOffset()) + ":" + tracked + ":" + maximum;
        if (!guard.add(key)) return null;

        long additive = 0L;
        Instruction cur = before;
        int count = 0;
        while (count++ < maximum) {
            cur = previous(owner, cur);
            if (cur == null) break;
            if (!writesRegister(cur, tracked)) continue;
            String m = lower(cur.getMnemonicString());

            if (m.equals("lis") || m.equals("e_lis") || m.endsWith("_lis")) {
                Long v = firstScalar(cur, true);
                return v == null ? null : Long.valueOf(u32(((v.longValue() & 0xffffL) << 16) + additive));
            }
            if (m.equals("li") || m.equals("e_li") || m.equals("se_li") || m.endsWith("_li")) {
                Long v = firstScalar(cur, true);
                return v == null ? null : Long.valueOf(u32(v.longValue() + additive));
            }
            if (m.contains("add16i") || m.equals("addi") || m.equals("e_addi") ||
                m.equals("se_addi") || m.equals("addic") || m.equals("addic.")) {
                String src = firstRegisterAfter(cur, 0);
                Long imm = lastScalar(cur, true);
                if (src == null || imm == null) return null;
                additive += imm.longValue();
                tracked = src;
                continue;
            }
            if (m.equals("addis") || m.equals("e_addis")) {
                String src = firstRegisterAfter(cur, 0);
                Long imm = lastScalar(cur, true);
                if (src == null || imm == null) return null;
                additive += (imm.longValue() & 0xffffL) << 16;
                tracked = src;
                continue;
            }
            if (isMove(m)) {
                String src = firstRegisterAfter(cur, 0);
                if (src == null) return null;
                tracked = src;
                continue;
            }
            return null;
        }
        return null;
    }

    private MemOp parseMem(Instruction ins) {
        if (ins == null) return null;
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

    private List<String> registers(Instruction ins) {
        List<String> out = new ArrayList<String>();
        Matcher m = REGISTER_PATTERN.matcher(ins.toString());
        while (m.find()) out.add(lower(m.group()));
        return out;
    }

    private Instruction previous(Function owner, Instruction ins) {
        Instruction p = ins == null ? null : ins.getPrevious();
        if (p == null) return null;
        Function po = functions.getFunctionContaining(p.getAddress());
        if (po == null || po.getEntryPoint().getOffset() != owner.getEntryPoint().getOffset()) return null;
        return p;
    }

    private boolean writesRegister(Instruction ins, String name) {
        if (ins == null || name == null) return false;
        Object[] results = ins.getResultObjects();
        if (results == null) return false;
        for (Object o : results) {
            if (o instanceof Register && name.equalsIgnoreCase(((Register)o).getName())) return true;
        }
        return false;
    }

    private String firstRegisterAfter(Instruction ins, int operand) {
        for (int i = operand + 1; i < ins.getNumOperands(); i++) {
            for (Object o : ins.getOpObjects(i)) {
                if (o instanceof Register) return lower(((Register)o).getName());
            }
        }
        return null;
    }

    private Long firstScalar(Instruction ins, boolean signed) {
        for (int i = 0; i < ins.getNumOperands(); i++) {
            for (Object o : ins.getOpObjects(i)) {
                if (o instanceof Scalar) {
                    Scalar s = (Scalar)o;
                    return Long.valueOf(signed ? s.getSignedValue() : s.getUnsignedValue());
                }
            }
        }
        return null;
    }

    private Long lastScalar(Instruction ins, boolean signed) {
        Long out = null;
        for (int i = 0; i < ins.getNumOperands(); i++) {
            for (Object o : ins.getOpObjects(i)) {
                if (o instanceof Scalar) {
                    Scalar s = (Scalar)o;
                    out = Long.valueOf(signed ? s.getSignedValue() : s.getUnsignedValue());
                }
            }
        }
        return out;
    }

    private String context(Instruction center, int before, int after) {
        List<Instruction> prior = new ArrayList<Instruction>();
        Instruction cur = center;
        for (int i = 0; i < before; i++) {
            cur = cur == null ? null : cur.getPrevious();
            if (cur == null) break;
            prior.add(cur);
        }
        Collections.reverse(prior);
        StringBuilder b = new StringBuilder();
        for (Instruction i : prior) append(b, i);
        append(b, center);
        cur = center;
        for (int i = 0; i < after; i++) {
            cur = cur == null ? null : cur.getNext();
            if (cur == null) break;
            append(b, cur);
        }
        return b.toString();
    }

    private void append(StringBuilder b, Instruction i) {
        if (i == null) return;
        if (b.length() > 0) b.append(" | ");
        b.append(hex(i.getAddress().getOffset())).append(":").append(i.toString());
    }

    private boolean isLoad(String m) {
        return m.contains("lbz") || m.contains("lhz") || m.contains("lha") ||
            m.contains("lwz") || m.equals("ld") || m.endsWith("_ld");
    }

    private boolean isStore(String m) {
        return m.contains("stb") || m.contains("sth") || m.contains("stw") ||
            m.equals("std") || m.endsWith("_std");
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

    private boolean overlaps(long start, int width, long wantedStart, long wantedEnd) {
        long end = u32(start + Math.max(1, width) - 1L);
        return Long.compareUnsigned(start, wantedEnd) <= 0 &&
            Long.compareUnsigned(end, wantedStart) >= 0;
    }

    private boolean betweenUnsigned(long value, long start, long end) {
        long v = u32(value);
        return Long.compareUnsigned(v, start) >= 0 && Long.compareUnsigned(v, end) <= 0;
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
    private Address address(long v) {
        return currentProgram.getAddressFactory().getDefaultAddressSpace().getAddress(u32(v));
    }
    private String hex(long v) { return String.format(Locale.ROOT, "0x%08X", u32(v)); }
    private String lower(String s) { return s == null ? "" : s.toLowerCase(Locale.ROOT); }
    private String safe(Throwable t) { return t == null ? "" : (t.getMessage() == null ? t.toString() : t.getMessage()); }

    private String join(List<String> values, String delimiter) {
        StringBuilder b = new StringBuilder();
        for (String v : values) {
            if (b.length() > 0) b.append(delimiter);
            b.append(v == null ? "" : v);
        }
        return b.toString();
    }

    private String pathText(List<Long> path) {
        List<String> values = new ArrayList<String>();
        for (Long v : path) values.add(hex(v.longValue()));
        return join(values, " -> ");
    }

    private void writeOutputs() throws Exception {
        List<File> out = new ArrayList<File>();
        out.add(writeCsv(stem + "_scope_contract.csv",
            new String[]{"item","value","meaning"}, scopeRows));
        out.add(writeCsv(stem + "_narrow_direct_accesses.csv",
            new String[]{"owner","owner_name","site","kind","width","target","reference_type","instruction"}, narrowRows));
        out.add(writeCsv(stem + "_indexed_store_candidates.csv",
            new String[]{"owner","owner_name","site","mnemonic","value_reg","base_reg","index_reg","resolved_base","resolved_index","resolved_ea","classification","index_evidence","instruction","context"}, indexedRows));
        out.add(writeCsv(stem + "_pointer_update_store_candidates.csv",
            new String[]{"owner","owner_name","site","mnemonic","base_reg","resolved_base","displacement","resolved_ea","classification","instruction","context"}, updateRows));
        out.add(writeCsv(stem + "_high_pcode_store_addresses.csv",
            new String[]{"owner","owner_name","site","classification","resolved_base_or_ea","dynamic","expression","pcode"}, pcodeRows));
        out.add(writeCsv(stem + "_known_root_paths.csv",
            new String[]{"root","root_owner","candidate_owner","depth","path","classification"}, pathRows));
        out.add(writeCsv(stem + "_assessment.csv",
            new String[]{"classification","exact_indexed_gate_writes","indexed_near_base_candidates","pointer_update_candidates","high_pcode_exact_gate_writes","high_pcode_dynamic_candidates","candidate_owners","known_root_paths","errors","note"}, assessmentRows));
        out.add(writeCsv(stem + "_errors.csv",
            new String[]{"stage","type","detail"}, errorRows));
        out.add(writeDecomp());
        out.add(writeSummary());

        File bundle = new File(outputDirectory, stem + "_bundle.zip");
        zip(bundle, out);
        println("V369 complete: " + bundle.getAbsolutePath());
    }

    private File writeDecomp() throws Exception {
        File f = new File(outputDirectory, stem + "_selected_decompilation.txt");
        BufferedWriter w = writer(f);
        try {
            List<Long> entries = new ArrayList<Long>(selectedFunctions);
            Collections.sort(entries, new Comparator<Long>() {
                @Override public int compare(Long a, Long b) {
                    return Long.compareUnsigned(a.longValue(), b.longValue());
                }
            });
            for (Long e : entries) {
                Function fn = byEntry.get(e);
                if (fn == null) continue;
                w.write("============================================================\n");
                w.write(hex(e.longValue()) + " " + fn.getName() + "\n");
                w.write("============================================================\n\n");
                try {
                    DecompileResults r = decompiler.decompileFunction(fn,
                        DECOMPILE_TIMEOUT_SECONDS, monitor);
                    if (r != null && r.decompileCompleted() && r.getDecompiledFunction() != null)
                        w.write(r.getDecompiledFunction().getC());
                    else w.write("Decompilation unavailable.\n");
                }
                catch (Throwable t) {
                    w.write("Decompilation error: " + t + "\n");
                }
                w.write("\n\n");
            }
        }
        finally { w.close(); }
        return f;
    }

    private File writeSummary() throws Exception {
        File f = new File(outputDirectory, stem + "_summary.md");
        BufferedWriter w = writer(f);
        try {
            String c = assessmentRows.isEmpty() ? "NO_ASSESSMENT" :
                assessmentRows.get(assessmentRows.size() - 1)[0];
            w.write("# " + SCRIPT_NAME + "\n\n");
            w.write("- Program: `" + currentProgram.getName() + "`\n");
            w.write("- Gate: `" + hex(GATE) + "`\n");
            w.write("- Exact indexed gate writes: `" + exactDynamicGateWrites + "`\n");
            w.write("- Indexed near-base candidates: `" + indexedNearBaseCandidates + "`\n");
            w.write("- Pointer-update candidates: `" + pointerUpdateCandidates + "`\n");
            w.write("- High-P-code exact gate writes: `" + highPcodeExactGateWrites + "`\n");
            w.write("- High-P-code dynamic candidates: `" + highPcodeDynamicCandidates + "`\n");
            w.write("- Candidate owners: `" + candidateOwners.size() + "`\n");
            w.write("- Known root paths: `" + rootPathCount + "`\n");
            w.write("- Errors: `" + errorRows.size() + "`\n");
            w.write("- Classification: `" + c + "`\n\n");
            w.write("V369 is intentionally the indexed/dynamic-address closure missing from V368; it does not repeat the previous displacement-base or bulk-call scan.\n");
        }
        finally { w.close(); }
        return f;
    }

    private File writeCsv(String name, String[] header, List<String[]> rows) throws Exception {
        File f = new File(outputDirectory, name);
        BufferedWriter w = writer(f);
        try {
            w.write(csv(header)); w.write("\r\n");
            for (String[] row : rows) { w.write(csv(row)); w.write("\r\n"); }
        }
        finally { w.close(); }
        return f;
    }

    private BufferedWriter writer(File f) throws Exception {
        return new BufferedWriter(new OutputStreamWriter(
            new FileOutputStream(f), StandardCharsets.UTF_8));
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
                if (f == null || !f.isFile()) continue;
                z.putNextEntry(new ZipEntry(f.getName()));
                FileInputStream in = new FileInputStream(f);
                try {
                    int n;
                    while ((n = in.read(buffer)) >= 0) if (n > 0) z.write(buffer, 0, n);
                }
                finally { in.close(); }
                z.closeEntry();
            }
        }
        finally { z.close(); }
    }
}
