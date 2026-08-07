// TeslaGatewayAPVisibleGateStartupSecondaryCoreAndDmaOriginTraceV370.java
//
// Read-only follow-up to V369.
//
// V369 exhausted defined-main-core direct, indexed, pointer-update and High-P-code
// STORE-address paths to 0x40046F57. V370 tests only the remaining static origin
// classes for this exact byte/window:
//   1. startup ROM-copy / zero-fill tables covering 0x40046F57;
//   2. exact target-address materialisation subsequently written into high MMIO,
//      especially the provisional MPC5668 eDMA range;
//   3. secondary-core start-vector programming and bounded call-graph reachability
//      from the recovered secondary-core entry to exact target materialisations;
//   4. raw exact target-address occurrences outside decoded instructions, for a
//      later focused undefined-code pass if necessary.
//
// This intentionally reuses the V338 provenance methodology on a NEW exact target
// (V338 targeted 0x4004A2B8..0x4004A2BF). It does not repeat the V367-V369 main-core
// writer searches, AP-trial, AA34, 0x7C03E owner recovery, or reset suppression.
//
// No program/database mutation. No disassembly creation. No firmware export.
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
import ghidra.program.model.symbol.ReferenceIterator;
import ghidra.program.model.symbol.ReferenceManager;

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
import java.util.zip.ZipEntry;
import java.util.zip.ZipOutputStream;

public class TeslaGatewayAPVisibleGateStartupSecondaryCoreAndDmaOriginTraceV370
        extends GhidraScript {

    private static final String SCRIPT_NAME =
        "TeslaGatewayAPVisibleGateStartupSecondaryCoreAndDmaOriginTraceV370";

    private static final long FLASH_START = 0x00000000L;
    private static final long FLASH_END = 0x001FFFFFL;
    private static final long APP_START = 0x00020000L;
    private static final long APP_END = 0x00149299L;

    private static final long TARGET = 0x40046F57L;
    private static final long TARGET_WORD = 0x40046F54L;
    private static final long NARROW_START = 0x40046F50L;
    private static final long NARROW_END = 0x40046F5FL;
    private static final long OBJECT_START = 0x40046F40L;
    private static final long OBJECT_END = 0x40046F8FL;

    private static final long RAM_START = 0x40000000L;
    private static final long RAM_END_EXCLUSIVE = 0x40100000L;
    private static final long MAX_INIT_LENGTH = 0x00200000L;

    private static final long Z0_VECTOR = 0xFFFEC054L;
    private static final long EDMA_START = 0xFFF44000L;
    private static final long EDMA_END = 0xFFF44FFFL;
    private static final long FLEXCAN_START = 0xFFFC0000L;
    private static final long FLEXCAN_END = 0xFFFDFFFFL;

    private static final int MAX_BACK = 140;
    private static final int MAX_CORE_CALL_DEPTH = 7;
    private static final int DECOMPILE_TIMEOUT_SECONDS = 45;

    private Listing listing;
    private Memory memory;
    private FunctionManager functions;
    private ReferenceManager references;
    private DecompInterface decompiler;
    private File outputDirectory;
    private String stem;

    private final Map<Long, Function> byEntry = new LinkedHashMap<Long, Function>();
    private final Map<Long, Set<Long>> callees = new LinkedHashMap<Long, Set<Long>>();
    private final Set<Long> selectedFunctions = new LinkedHashSet<Long>();
    private final Set<Long> targetMaterialisationOwners = new LinkedHashSet<Long>();

    private final List<String[]> scopeRows = new ArrayList<String[]>();
    private final List<String[]> initRows = new ArrayList<String[]>();
    private final List<String[]> initOwnerRows = new ArrayList<String[]>();
    private final List<String[]> rawRows = new ArrayList<String[]>();
    private final List<String[]> materialRows = new ArrayList<String[]>();
    private final List<String[]> mmioRows = new ArrayList<String[]>();
    private final List<String[]> dmaRows = new ArrayList<String[]>();
    private final List<String[]> coreStartRows = new ArrayList<String[]>();
    private final List<String[]> corePathRows = new ArrayList<String[]>();
    private final List<String[]> assessmentRows = new ArrayList<String[]>();
    private final List<String[]> errorRows = new ArrayList<String[]>();

    private int romCopyCandidates;
    private int zeroFillCandidates;
    private int rawExactHits;
    private int rawUndefinedHits;
    private int targetMaterialisations;
    private int dmaTargetPrograms;
    private int secondaryCoreStarts;
    private int secondaryCoreTargetPaths;

    private static class InitCandidate {
        long table;
        String layout;
        String kind;
        long source;
        long destination;
        long length;
        long targetOffset;
        String initialByte;
        int confidence;
    }

    private static class CoreNode {
        final long entry;
        final int depth;
        final List<Long> path;
        CoreNode(long entry, int depth, List<Long> path) {
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
        references = currentProgram.getReferenceManager();

        outputDirectory = askDirectory("Select V370 output directory", "Select");
        if (outputDirectory == null) return;

        stem = SCRIPT_NAME + "_" +
            new SimpleDateFormat("yyyyMMdd_HHmmss").format(new Date());

        decompiler = new DecompInterface();
        decompiler.openProgram(currentProgram);

        try {
            emitScope();
            indexFunctions();
            scanRawTargetOccurrences();
            List<InitCandidate> init = scanInitialisationTables();
            emitInitialisationRows(init);
            collectInitialisationOwners(init);
            scanCodeMaterialisationsAndMmio();
            buildSecondaryCoreTargetPaths();
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
        scopeRows.add(new String[]{"LANGUAGE", currentProgram.getLanguageID().toString(),
            "EXPECTED_POWERPC_BE_VLE"});
        scopeRows.add(new String[]{"VISIBLE_GATE", hex(TARGET),
            "V367_CONSUMER_VALIDATED_V368_V369_DEFINED_MAIN_CORE_WRITER_NEGATIVE"});
        scopeRows.add(new String[]{"TARGET_WINDOW", hex(NARROW_START) + ".." + hex(NARROW_END),
            "ONLY_FOR_STARTUP_DMA_SECONDARY_CORE_PROVENANCE"});
        scopeRows.add(new String[]{"V338_DIFFERENCE", "V338_TARGETED_0x4004A2B8..0x4004A2BF",
            "V370_REUSES_METHOD_ON_0x40046F57_NOT_THE_OLD_TARGET"});
        scopeRows.add(new String[]{"NEW_SCOPE",
            "STARTUP_INIT_TABLE_EXACT_TARGET_DMA_PROGRAMMING_SECONDARY_CORE_ENTRY_RAW_UNDEFINED_OCCURRENCES",
            "NOT_REPEATING_V367_V368_V369_MAIN_CORE_STORE_SEARCH"});
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
            Set<Long> out = callees.get(Long.valueOf(f.getEntryPoint().getOffset()));
            InstructionIterator ii = listing.getInstructions(f.getBody(), true);
            while (ii.hasNext()) {
                Instruction ins = ii.next();
                if (ins.getFlowType() == null || !ins.getFlowType().isCall()) continue;
                for (Address flow : ins.getFlows()) {
                    if (flow == null) continue;
                    Function c = functions.getFunctionAt(flow);
                    if (c == null) c = functions.getFunctionContaining(flow);
                    if (c != null) out.add(Long.valueOf(c.getEntryPoint().getOffset()));
                }
            }
        }
    }

    private void scanRawTargetOccurrences() {
        long[] values = {TARGET, TARGET_WORD, NARROW_START, OBJECT_START};
        String[] labels = {"VISIBLE_GATE", "GATE_WORD", "NARROW_START", "OBJECT_START"};

        for (int vi = 0; vi < values.length; vi++) {
            byte[] needle = u32be(values[vi]);
            for (MemoryBlock block : memory.getBlocks()) {
                if (!block.isInitialized() || !block.isRead()) continue;
                long span = block.getEnd().getOffset() - block.getStart().getOffset();
                if (span < 0 || span > 0x01000000L) continue;

                Address cursor = block.getStart();
                while (cursor != null && !monitor.isCancelled()) {
                    Address found = memory.findBytes(cursor, needle, null, true, monitor);
                    if (found == null ||
                        Long.compareUnsigned(found.getOffset(), block.getEnd().getOffset()) > 0) break;

                    Instruction containing = listing.getInstructionContaining(found);
                    Function owner = functions.getFunctionContaining(found);
                    String classification = containing == null
                        ? "RAW_UNDEFINED_OR_DATA_OCCURRENCE"
                        : "BYTES_INSIDE_DECODED_INSTRUCTION";

                    rawExactHits++;
                    if (containing == null) rawUndefinedHits++;
                    if (owner != null) selectedFunctions.add(
                        Long.valueOf(owner.getEntryPoint().getOffset()));

                    rawRows.add(new String[]{
                        labels[vi], hex(values[vi]), hex(found.getOffset()), block.getName(),
                        owner == null ? "" : hex(owner.getEntryPoint().getOffset()),
                        owner == null ? "" : owner.getName(), classification,
                        containing == null ? "" : containing.toString(), rawContext(found.getOffset(), 16, 24)
                    });

                    try { cursor = found.add(1L); }
                    catch (Throwable t) { break; }
                }
            }
        }
    }

    private List<InitCandidate> scanInitialisationTables() {
        List<InitCandidate> out = new ArrayList<InitCandidate>();
        Set<String> seen = new LinkedHashSet<String>();

        for (long p = FLASH_START; p + 12 <= FLASH_END && !monitor.isCancelled(); p += 4) {
            Long a = readU32Quiet(p);
            Long b = readU32Quiet(p + 4);
            Long c = readU32Quiet(p + 8);
            if (a == null || b == null || c == null) continue;

            considerCopy(out, seen, p, "SRC_DST_LEN_BYTES",
                a.longValue(), b.longValue(), c.longValue(), 10);
            if (c.longValue() > 0 && c.longValue() <= MAX_INIT_LENGTH / 4L) {
                considerCopy(out, seen, p, "SRC_DST_LEN_WORDS",
                    a.longValue(), b.longValue(), c.longValue() * 4L, 8);
            }
            if (isMappedRom(a.longValue()) && isRam(b.longValue()) && isRam(c.longValue()) &&
                Long.compareUnsigned(c.longValue(), b.longValue()) > 0) {
                considerCopy(out, seen, p, "SRC_DST_END",
                    a.longValue(), b.longValue(), c.longValue() - b.longValue(), 9);
            }

            considerCopy(out, seen, p, "DST_SRC_LEN_BYTES",
                b.longValue(), a.longValue(), c.longValue(), 7);

            considerZero(out, seen, p, "DST_LEN_BYTES",
                a.longValue(), b.longValue(), 6);
            if (b.longValue() > 0 && b.longValue() <= MAX_INIT_LENGTH / 4L) {
                considerZero(out, seen, p, "DST_LEN_WORDS",
                    a.longValue(), b.longValue() * 4L, 5);
            }
            if (isRam(a.longValue()) && isRam(b.longValue()) &&
                Long.compareUnsigned(b.longValue(), a.longValue()) > 0) {
                considerZero(out, seen, p, "DST_END",
                    a.longValue(), b.longValue() - a.longValue(), 5);
            }
        }

        Collections.sort(out, new Comparator<InitCandidate>() {
            @Override public int compare(InitCandidate x, InitCandidate y) {
                int c = Integer.compare(y.confidence, x.confidence);
                if (c != 0) return c;
                return Long.compareUnsigned(x.table, y.table);
            }
        });
        return out;
    }

    private void considerCopy(List<InitCandidate> out, Set<String> seen, long table,
                              String layout, long source, long destination,
                              long length, int confidence) {
        source = u32(source);
        destination = u32(destination);
        length = u32(length);
        if (!isMappedRom(source) || !isRam(destination) || !validLength(length) ||
            !coversTarget(destination, length)) return;

        String key = "C:" + source + ":" + destination + ":" + length;
        if (!seen.add(key)) return;

        InitCandidate r = new InitCandidate();
        r.table = table;
        r.layout = layout;
        r.kind = "ROM_COPY";
        r.source = source;
        r.destination = destination;
        r.length = length;
        r.targetOffset = TARGET - destination;
        r.confidence = confidence;
        Long byteValue = readByteQuiet(source + r.targetOffset);
        r.initialByte = byteValue == null ? "" : String.format(Locale.ROOT, "0x%02X", byteValue.longValue());
        out.add(r);
        romCopyCandidates++;
    }

    private void considerZero(List<InitCandidate> out, Set<String> seen, long table,
                              String layout, long destination, long length,
                              int confidence) {
        destination = u32(destination);
        length = u32(length);
        if (!isRam(destination) || !validLength(length) ||
            !coversTarget(destination, length)) return;

        String key = "Z:" + destination + ":" + length;
        if (!seen.add(key)) return;

        InitCandidate r = new InitCandidate();
        r.table = table;
        r.layout = layout;
        r.kind = "ZERO_FILL";
        r.source = 0;
        r.destination = destination;
        r.length = length;
        r.targetOffset = TARGET - destination;
        r.initialByte = "0x00";
        r.confidence = confidence;
        out.add(r);
        zeroFillCandidates++;
    }

    private void emitInitialisationRows(List<InitCandidate> init) {
        for (InitCandidate r : init) {
            initRows.add(new String[]{
                hex(r.table), r.layout, r.kind,
                r.source == 0 ? "" : hex(r.source),
                hex(r.destination), hex(r.length), hex(r.targetOffset),
                r.initialByte, Integer.toString(r.confidence),
                "COVERS_VISIBLE_GATE"
            });
        }
    }

    private void collectInitialisationOwners(List<InitCandidate> init) {
        for (InitCandidate r : init) {
            long[] containers = {r.table, r.table & ~3L, r.table & ~7L, r.table & ~15L};
            Set<Long> seen = new HashSet<Long>();
            for (long c : containers) {
                if (!seen.add(Long.valueOf(c))) continue;
                ReferenceIterator it = references.getReferencesTo(addr(c));
                while (it.hasNext()) {
                    Reference ref = it.next();
                    Function owner = functions.getFunctionContaining(ref.getFromAddress());
                    if (owner != null) selectedFunctions.add(
                        Long.valueOf(owner.getEntryPoint().getOffset()));
                    initOwnerRows.add(new String[]{
                        hex(r.table), r.layout, r.kind, hex(c),
                        hex(ref.getFromAddress().getOffset()), ref.getReferenceType().toString(),
                        owner == null ? "" : hex(owner.getEntryPoint().getOffset()),
                        owner == null ? "" : owner.getName(),
                        instructionAt(ref.getFromAddress())
                    });
                }
            }
        }
    }

    private void scanCodeMaterialisationsAndMmio() {
        FunctionIterator fit = listing.getFunctions(true);
        while (fit.hasNext() && !monitor.isCancelled()) {
            Function owner = fit.next();
            InstructionIterator ii = listing.getInstructions(owner.getBody(), true);
            while (ii.hasNext()) {
                Instruction ins = ii.next();
                long ownerEntry = owner.getEntryPoint().getOffset();

                Object[] results = ins.getResultObjects();
                if (results != null) {
                    for (Object o : results) {
                        if (!(o instanceof Register)) continue;
                        String reg = ((Register)o).getName();
                        Long value = resolveWrittenRegister(owner, ins, reg, MAX_BACK,
                            new HashSet<String>());
                        if (value == null || !isTrackedTarget(value.longValue())) continue;

                        targetMaterialisations++;
                        targetMaterialisationOwners.add(Long.valueOf(ownerEntry));
                        selectedFunctions.add(Long.valueOf(ownerEntry));
                        materialRows.add(new String[]{
                            hex(ownerEntry), owner.getName(), hex(ins.getAddress().getOffset()),
                            reg, hex(value.longValue()), targetRole(value.longValue()),
                            ins.toString()
                        });
                    }
                }

                String m = lower(ins.getMnemonicString());
                if (!isStore(m)) continue;
                Long effective = effectiveAddress(owner, ins);
                if (effective == null || !isHighPeripheral(effective.longValue())) continue;

                String sourceReg = firstRegister(ins, 0);
                Long sourceConst = sourceReg == null ? null :
                    resolveRegisterBefore(owner, ins, sourceReg, MAX_BACK, new HashSet<String>());
                String label = classifyMmio(effective.longValue());

                mmioRows.add(new String[]{
                    hex(ownerEntry), owner.getName(), hex(ins.getAddress().getOffset()),
                    hex(effective.longValue()), label, sourceReg == null ? "" : sourceReg,
                    sourceConst == null ? "" : hex(sourceConst.longValue()),
                    sourceConst == null ? "" : targetRoleOrOther(sourceConst.longValue()),
                    ins.toString()
                });

                if (sourceConst != null && isTrackedTarget(sourceConst.longValue()) &&
                    isDmaLike(label)) {
                    dmaTargetPrograms++;
                    selectedFunctions.add(Long.valueOf(ownerEntry));
                    dmaRows.add(new String[]{
                        hex(ownerEntry), owner.getName(), hex(ins.getAddress().getOffset()),
                        hex(effective.longValue()), label, sourceReg,
                        hex(sourceConst.longValue()), targetRole(sourceConst.longValue()),
                        "EXACT_VISIBLE_GATE_OR_NEAR_TARGET_ADDRESS_PROGRAMMED_TO_PERIPHERAL",
                        ins.toString()
                    });
                }

                if (u32(effective.longValue()) == Z0_VECTOR && sourceConst != null &&
                    isExecutable(sourceConst.longValue())) {
                    secondaryCoreStarts++;
                    long entry = sourceConst.longValue() & 0xFFFFFFFEL;
                    selectedFunctions.add(Long.valueOf(ownerEntry));
                    Function ef = functions.getFunctionAt(addr(entry));
                    if (ef == null) ef = functions.getFunctionContaining(addr(entry));
                    if (ef != null) selectedFunctions.add(Long.valueOf(ef.getEntryPoint().getOffset()));
                    coreStartRows.add(new String[]{
                        hex(ownerEntry), owner.getName(), hex(ins.getAddress().getOffset()),
                        hex(effective.longValue()), sourceReg,
                        hex(sourceConst.longValue()), hex(entry),
                        ef == null ? "" : hex(ef.getEntryPoint().getOffset()),
                        ef == null ? "" : ef.getName(), ins.toString()
                    });
                }
            }
        }
    }

    private void buildSecondaryCoreTargetPaths() {
        Set<Long> starts = new LinkedHashSet<Long>();
        for (String[] row : coreStartRows) {
            if (row.length < 8 || row[7].isEmpty()) continue;
            starts.add(Long.valueOf(parseHex(row[7])));
        }

        for (Long start : starts) {
            Queue<CoreNode> q = new ArrayDeque<CoreNode>();
            Set<Long> seen = new LinkedHashSet<Long>();
            List<Long> first = new ArrayList<Long>();
            first.add(start);
            q.add(new CoreNode(start.longValue(), 0, first));
            seen.add(start);

            while (!q.isEmpty()) {
                CoreNode n = q.remove();
                if (targetMaterialisationOwners.contains(Long.valueOf(n.entry))) {
                    secondaryCoreTargetPaths++;
                    corePathRows.add(new String[]{
                        hex(start.longValue()), hex(n.entry), Integer.toString(n.depth),
                        pathText(n.path), "SECONDARY_CORE_CALL_PATH_REACHES_TARGET_MATERIALISATION_OWNER"
                    });
                }
                if (n.depth >= MAX_CORE_CALL_DEPTH) continue;
                Set<Long> next = callees.get(Long.valueOf(n.entry));
                if (next == null) continue;
                for (Long c : next) {
                    if (!seen.add(c)) continue;
                    List<Long> p = new ArrayList<Long>(n.path);
                    p.add(c);
                    q.add(new CoreNode(c.longValue(), n.depth + 1, p));
                }
            }
        }
    }

    private void buildAssessment() {
        String classification;
        String note;

        if (dmaTargetPrograms > 0) {
            classification = "VISIBLE_GATE_ADDRESS_PROGRAMMED_INTO_DMA_OR_PERIPHERAL_PATH";
            note = "Review only the exact peripheral programming rows and source register provenance; this is stronger than the exhausted main-core store searches.";
        }
        else if (secondaryCoreTargetPaths > 0) {
            classification = "SECONDARY_CORE_PATH_REACHES_VISIBLE_GATE_TARGET_MATERIALISATION";
            note = "A recovered secondary-core entry reaches a function that materialises the visible-gate address. Review that exact path before widening further.";
        }
        else if (romCopyCandidates > 0) {
            classification = "VISIBLE_GATE_ROM_COPY_INITIALISER_RECOVERED";
            note = "A startup copy table covers 0x40046F57. This establishes only the initial byte value, not the later runtime producer.";
        }
        else if (zeroFillCandidates > 0) {
            classification = "VISIBLE_GATE_ZERO_FILL_ONLY_NO_RUNTIME_PRODUCER";
            note = "Startup zero-fill covers the gate but does not explain a later nonzero runtime value. Main-core runtime ownership remains excluded by V367-V369.";
        }
        else if (rawUndefinedHits > 0) {
            classification = "RAW_UNDEFINED_VISIBLE_GATE_ADDRESS_OCCURRENCE_REQUIRES_FOCUSED_DECODE";
            note = "Exact address bytes exist outside decoded instructions. The next pass should pseudo-decode only those local raw contexts.";
        }
        else {
            classification = "VISIBLE_GATE_STATIC_ORIGIN_REMAINS_UNRESOLVED_AFTER_STARTUP_DMA_SECONDARY_CORE_PASS";
            note = "No startup-copy/zero candidate, exact DMA destination programming, secondary-core path, or raw undefined target occurrence explains 0x40046F57.";
        }

        assessmentRows.add(new String[]{
            classification,
            Integer.toString(romCopyCandidates),
            Integer.toString(zeroFillCandidates),
            Integer.toString(rawExactHits),
            Integer.toString(rawUndefinedHits),
            Integer.toString(targetMaterialisations),
            Integer.toString(dmaTargetPrograms),
            Integer.toString(secondaryCoreStarts),
            Integer.toString(secondaryCoreTargetPaths),
            Integer.toString(errorRows.size()),
            note
        });
    }

    private Long effectiveAddress(Function owner, Instruction ins) {
        if (ins.getNumOperands() < 2) return null;
        long total = 0;
        boolean any = false;
        for (Object o : ins.getOpObjects(1)) {
            if (o instanceof Register) {
                Long v = resolveRegisterBefore(owner, ins, ((Register)o).getName(),
                    MAX_BACK, new HashSet<String>());
                if (v == null) return null;
                total += v.longValue();
                any = true;
            }
            else if (o instanceof Scalar) {
                total += ((Scalar)o).getSignedValue();
                any = true;
            }
            else if (o instanceof Address) {
                total += ((Address)o).getOffset();
                any = true;
            }
        }
        if (!any) {
            for (Reference r : ins.getReferencesFrom()) {
                if (r.getToAddress() != null && isHighPeripheral(r.getToAddress().getOffset()))
                    return Long.valueOf(r.getToAddress().getOffset());
            }
            return null;
        }
        return Long.valueOf(u32(total));
    }

    private Long resolveWrittenRegister(Function owner, Instruction def, String register,
                                        int maximum, Set<String> guard) {
        if (def == null || register == null || maximum <= 0) return null;
        String m = lower(def.getMnemonicString());
        String dst = firstRegister(def, 0);
        if (dst == null || !dst.equalsIgnoreCase(register)) return null;

        if (m.equals("lis") || m.equals("e_lis") || m.endsWith("_lis")) {
            Long imm = lastScalar(def, true);
            return imm == null ? null : Long.valueOf(u32((imm.longValue() & 0xFFFFL) << 16));
        }
        if (m.equals("li") || m.equals("e_li") || m.equals("se_li") || m.endsWith("_li")) {
            Long imm = lastScalar(def, true);
            return imm == null ? null : Long.valueOf(u32(imm.longValue()));
        }
        if (m.contains("add16i") || m.equals("addi") || m.equals("e_addi") ||
            m.equals("se_addi") || m.equals("addic") || m.equals("addic.")) {
            String src = firstRegisterAfter(def, 0);
            Long imm = lastScalar(def, true);
            Long base = src == null ? null : resolveRegisterBefore(owner, def, src,
                maximum - 1, guard);
            return base == null || imm == null ? null : Long.valueOf(u32(base.longValue() + imm.longValue()));
        }
        if (m.equals("addis") || m.equals("e_addis")) {
            String src = firstRegisterAfter(def, 0);
            Long imm = lastScalar(def, true);
            Long base = src == null ? null : resolveRegisterBefore(owner, def, src,
                maximum - 1, guard);
            return base == null || imm == null ? null :
                Long.valueOf(u32(base.longValue() + ((imm.longValue() & 0xFFFFL) << 16)));
        }
        if (m.equals("ori") || m.equals("e_ori") || m.endsWith("_ori")) {
            String src = firstRegisterAfter(def, 0);
            Long imm = lastScalar(def, false);
            Long base = src == null ? null : resolveRegisterBefore(owner, def, src,
                maximum - 1, guard);
            return base == null || imm == null ? null :
                Long.valueOf(u32(base.longValue() | (imm.longValue() & 0xFFFFL)));
        }
        if (m.equals("oris") || m.equals("e_oris") || m.endsWith("_oris")) {
            String src = firstRegisterAfter(def, 0);
            Long imm = lastScalar(def, false);
            Long base = src == null ? null : resolveRegisterBefore(owner, def, src,
                maximum - 1, guard);
            return base == null || imm == null ? null :
                Long.valueOf(u32(base.longValue() | ((imm.longValue() & 0xFFFFL) << 16)));
        }
        if (isMove(m)) {
            String src = firstRegisterAfter(def, 0);
            return src == null ? null : resolveRegisterBefore(owner, def, src,
                maximum - 1, guard);
        }
        return null;
    }

    private Long resolveRegisterBefore(Function owner, Instruction before, String register,
                                       int maximum, Set<String> guard) {
        if (owner == null || before == null || register == null || maximum <= 0) return null;
        String key = hex(owner.getEntryPoint().getOffset()) + ":" +
            hex(before.getAddress().getOffset()) + ":" + lower(register) + ":" + maximum;
        if (!guard.add(key)) return null;

        Instruction cur = before;
        for (int i = 0; i < maximum; i++) {
            cur = previous(owner, cur);
            if (cur == null) break;
            if (!writesRegister(cur, register)) continue;
            return resolveWrittenRegister(owner, cur, register, maximum - i - 1, guard);
        }
        return null;
    }

    private Instruction previous(Function owner, Instruction ins) {
        Instruction p = ins == null ? null : ins.getPrevious();
        if (p == null) return null;
        Function po = functions.getFunctionContaining(p.getAddress());
        if (po == null || po.getEntryPoint().getOffset() != owner.getEntryPoint().getOffset()) return null;
        return p;
    }

    private boolean writesRegister(Instruction ins, String name) {
        Object[] results = ins == null ? null : ins.getResultObjects();
        if (results == null) return false;
        for (Object o : results)
            if (o instanceof Register && name.equalsIgnoreCase(((Register)o).getName())) return true;
        return false;
    }

    private String firstRegister(Instruction ins, int operand) {
        if (ins == null || operand < 0 || operand >= ins.getNumOperands()) return null;
        for (Object o : ins.getOpObjects(operand))
            if (o instanceof Register) return ((Register)o).getName();
        return null;
    }

    private String firstRegisterAfter(Instruction ins, int operand) {
        for (int i = operand + 1; i < ins.getNumOperands(); i++) {
            String r = firstRegister(ins, i);
            if (r != null) return r;
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

    private boolean coversTarget(long destination, long length) {
        if (length <= 0) return false;
        long end = destination + length - 1L;
        return Long.compareUnsigned(destination, TARGET) <= 0 &&
            Long.compareUnsigned(end, TARGET) >= 0;
    }

    private boolean validLength(long length) {
        return length > 0 && length <= MAX_INIT_LENGTH;
    }

    private boolean isMappedRom(long value) {
        long v = u32(value);
        return v >= FLASH_START && v <= FLASH_END && memory.contains(addr(v));
    }

    private boolean isRam(long value) {
        long v = u32(value);
        return Long.compareUnsigned(v, RAM_START) >= 0 &&
            Long.compareUnsigned(v, RAM_END_EXCLUSIVE) < 0;
    }

    private boolean isTrackedTarget(long value) {
        long v = u32(value);
        return v == TARGET || v == TARGET_WORD ||
            (Long.compareUnsigned(v, NARROW_START) >= 0 &&
             Long.compareUnsigned(v, NARROW_END) <= 0) ||
            v == OBJECT_START;
    }

    private String targetRole(long value) {
        long v = u32(value);
        if (v == TARGET) return "VISIBLE_GATE_EXACT";
        if (v == TARGET_WORD) return "GATE_WORD";
        if (v == NARROW_START) return "NARROW_START";
        if (v == OBJECT_START) return "OBJECT_START";
        if (Long.compareUnsigned(v, NARROW_START) >= 0 &&
            Long.compareUnsigned(v, NARROW_END) <= 0) return "NARROW_WINDOW_ADDRESS";
        return "OTHER";
    }

    private String targetRoleOrOther(long value) {
        return isTrackedTarget(value) ? targetRole(value) : "OTHER_CONSTANT";
    }

    private boolean isExecutable(long value) {
        long v = u32(value) & 0xFFFFFFFEL;
        return v >= APP_START && v <= APP_END;
    }

    private boolean isHighPeripheral(long value) {
        return Long.compareUnsigned(u32(value), 0xC0000000L) >= 0;
    }

    private String classifyMmio(long value) {
        long v = u32(value);
        if (v == Z0_VECTOR) return "SECONDARY_CORE_Z0_VECTOR";
        if (v >= EDMA_START && v <= EDMA_END) return "PROVISIONAL_EDMA_RANGE";
        if (v >= FLEXCAN_START && v <= FLEXCAN_END) return "PROVISIONAL_FLEXCAN_RANGE";
        if (v >= 0xFFF38000L && v <= 0xFFF38FFFL) return "SWT_WATCHDOG_RANGE";
        if (v >= 0xFFF48000L && v <= 0xFFF4FFFFL) return "PROVISIONAL_INTC_TIMER_RANGE";
        return "HIGH_PERIPHERAL_UNCLASSIFIED";
    }

    private boolean isDmaLike(String label) {
        return "PROVISIONAL_EDMA_RANGE".equals(label) ||
            "PROVISIONAL_FLEXCAN_RANGE".equals(label) ||
            "HIGH_PERIPHERAL_UNCLASSIFIED".equals(label);
    }

    private boolean isStore(String m) {
        return m.contains("stb") || m.contains("sth") || m.contains("stw") ||
            m.equals("std") || m.endsWith("_std");
    }

    private boolean isMove(String m) {
        return m.equals("mr") || m.equals("se_mr") || m.endsWith("_mr");
    }

    private Long readU32Quiet(long p) {
        try {
            byte[] b = new byte[4];
            if (memory.getBytes(addr(p), b) != 4) return null;
            long v = ((long)(b[0] & 0xFF) << 24) |
                     ((long)(b[1] & 0xFF) << 16) |
                     ((long)(b[2] & 0xFF) << 8) |
                     ((long)(b[3] & 0xFF));
            return Long.valueOf(v);
        }
        catch (Throwable t) { return null; }
    }

    private Long readByteQuiet(long p) {
        try { return Long.valueOf(memory.getByte(addr(p)) & 0xFFL); }
        catch (Throwable t) { return null; }
    }

    private byte[] u32be(long value) {
        long v = u32(value);
        return new byte[]{
            (byte)(v >>> 24), (byte)(v >>> 16), (byte)(v >>> 8), (byte)v
        };
    }

    private String rawContext(long center, int before, int after) {
        long start = Math.max(FLASH_START, center - before);
        long end = Math.min(FLASH_END, center + after);
        StringBuilder b = new StringBuilder();
        for (long p = start; p <= end; p++) {
            Long v = readByteQuiet(p);
            if (v == null) continue;
            if (b.length() > 0) b.append(' ');
            b.append(String.format(Locale.ROOT, "%02X", v.longValue()));
        }
        return b.toString();
    }

    private String instructionAt(Address a) {
        Instruction i = listing.getInstructionContaining(a);
        return i == null ? "" : i.toString();
    }

    private long parseHex(String s) {
        String v = s == null ? "" : s.trim().toLowerCase(Locale.ROOT);
        if (v.startsWith("0x")) v = v.substring(2);
        return Long.parseLong(v, 16) & 0xFFFFFFFFL;
    }

    private long u32(long v) { return v & 0xFFFFFFFFL; }
    private Address addr(long v) {
        return currentProgram.getAddressFactory().getDefaultAddressSpace().getAddress(u32(v));
    }
    private String hex(long v) {
        return String.format(Locale.ROOT, "0x%08X", u32(v));
    }
    private String lower(String s) {
        return s == null ? "" : s.toLowerCase(Locale.ROOT);
    }
    private String safe(Throwable t) {
        return t == null ? "" : (t.getMessage() == null ? t.toString() : t.getMessage());
    }

    private String pathText(List<Long> path) {
        StringBuilder b = new StringBuilder();
        for (Long v : path) {
            if (b.length() > 0) b.append(" -> ");
            b.append(hex(v.longValue()));
        }
        return b.toString();
    }

    private void writeOutputs() throws Exception {
        List<File> out = new ArrayList<File>();
        out.add(writeCsv(stem + "_scope_contract.csv",
            new String[]{"item","value","meaning"}, scopeRows));
        out.add(writeCsv(stem + "_ram_initialisation_candidates.csv",
            new String[]{"table","layout","kind","source","destination","length","target_offset","initial_gate_byte","confidence","classification"}, initRows));
        out.add(writeCsv(stem + "_initialisation_table_owner_references.csv",
            new String[]{"table","layout","kind","container","reference_site","reference_type","owner","owner_name","instruction"}, initOwnerRows));
        out.add(writeCsv(stem + "_raw_target_occurrences.csv",
            new String[]{"label","value","location","block","owner","owner_name","classification","instruction","raw_context"}, rawRows));
        out.add(writeCsv(stem + "_target_materialisations.csv",
            new String[]{"owner","owner_name","site","register","value","role","instruction"}, materialRows));
        out.add(writeCsv(stem + "_resolved_high_mmio_accesses.csv",
            new String[]{"owner","owner_name","site","mmio_address","mmio_class","source_register","source_constant","source_role","instruction"}, mmioRows));
        out.add(writeCsv(stem + "_dma_target_programming_candidates.csv",
            new String[]{"owner","owner_name","site","mmio_address","mmio_class","source_register","source_constant","source_role","classification","instruction"}, dmaRows));
        out.add(writeCsv(stem + "_secondary_core_start_candidates.csv",
            new String[]{"owner","owner_name","site","vector_address","source_register","source_value","normalized_entry","entry_owner","entry_name","instruction"}, coreStartRows));
        out.add(writeCsv(stem + "_secondary_core_target_paths.csv",
            new String[]{"secondary_core_entry","target_owner","depth","path","classification"}, corePathRows));
        out.add(writeCsv(stem + "_assessment.csv",
            new String[]{"classification","rom_copy_candidates","zero_fill_candidates","raw_exact_hits","raw_undefined_hits","target_materialisations","dma_target_programming","secondary_core_starts","secondary_core_target_paths","errors","note"}, assessmentRows));
        out.add(writeCsv(stem + "_errors.csv",
            new String[]{"stage","type","detail"}, errorRows));
        out.add(writeDecomp());
        out.add(writeSummary());

        File bundle = new File(outputDirectory, stem + "_bundle.zip");
        zip(bundle, out);
        println("V370 complete: " + bundle.getAbsolutePath());
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
            w.write("- Visible gate: `" + hex(TARGET) + "`\n");
            w.write("- ROM-copy initialisation candidates: `" + romCopyCandidates + "`\n");
            w.write("- Zero-fill initialisation candidates: `" + zeroFillCandidates + "`\n");
            w.write("- Raw exact/undefined target-address hits: `" + rawExactHits + "/" + rawUndefinedHits + "`\n");
            w.write("- Target-address materialisations: `" + targetMaterialisations + "`\n");
            w.write("- DMA/peripheral target-address programming candidates: `" + dmaTargetPrograms + "`\n");
            w.write("- Secondary-core start candidates: `" + secondaryCoreStarts + "`\n");
            w.write("- Secondary-core paths to target materialisation owners: `" + secondaryCoreTargetPaths + "`\n");
            w.write("- Errors: `" + errorRows.size() + "`\n");
            w.write("- Classification: `" + c + "`\n\n");
            w.write("V370 is the exact visible-gate startup/DMA/secondary-core provenance pass left after V369; it does not repeat defined-main-core writer analysis.\n");
        }
        finally { w.close(); }
        return f;
    }

    private File writeCsv(String name, String[] header, List<String[]> rows) throws Exception {
        File f = new File(outputDirectory, name);
        BufferedWriter w = writer(f);
        try {
            w.write(csv(header)); w.write("\r\n");
            for (String[] row : rows) {
                w.write(csv(row)); w.write("\r\n");
            }
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
            b.append('\"').append(v).append('\"');
        }
        return b.toString();
    }

    private void zip(File bundle, List<File> filesOut) throws Exception {
        ZipOutputStream z = new ZipOutputStream(new FileOutputStream(bundle));
        try {
            byte[] buf = new byte[8192];
            for (File f : filesOut) {
                if (f == null || !f.isFile()) continue;
                z.putNextEntry(new ZipEntry(f.getName()));
                FileInputStream in = new FileInputStream(f);
                try {
                    int n;
                    while ((n = in.read(buf)) > 0) z.write(buf, 0, n);
                }
                finally { in.close(); }
                z.closeEntry();
            }
        }
        finally { z.close(); }
    }
}
