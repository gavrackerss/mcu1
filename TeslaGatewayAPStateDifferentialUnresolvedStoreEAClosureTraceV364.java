// TeslaGatewayAPStateDifferentialUnresolvedStoreEAClosureTraceV364.java
//
// Read-only closure pass following V361 and V363R1.
//
// V361 already compared state-2 and non-state-2 successors near the AP
// ingress/helper anchors. Its remaining limitation was that stores without
// existing Ghidra references were retained only as textual STORE@ effects.
// V363R1 pseudo-decoded the AP record callbacks, not the state helper at
// 0x0006F46E.
//
// This script closes only that remaining gap:
//   1. pseudo-decodes the local CFG rooted at 0x0006F46E;
//   2. finds explicit comparisons against state 1 or state 2;
//   3. finds the first reconvergence of each branch;
//   4. propagates simple PPC/VLE register constants independently per side;
//   5. resolves computed store effective addresses before reconvergence;
//   6. reports the first branch-unique global write or direct call;
//   7. inventories exact consumers of unique RAM targets;
//   8. checks bounded direct-call paths to known pending/reset anchors.
//
// Ghidra 12.1.2.
// No database changes. No disassembly creation. No patching. No export.
//
// @category TeslaGateway.Analysis

import ghidra.app.decompiler.DecompInterface;
import ghidra.app.decompiler.DecompileResults;
import ghidra.app.script.GhidraScript;
import ghidra.program.model.address.Address;
import ghidra.program.model.listing.Function;
import ghidra.program.model.listing.FunctionIterator;
import ghidra.program.model.listing.FunctionManager;
import ghidra.program.model.listing.Instruction;
import ghidra.program.model.listing.Listing;
import ghidra.program.model.scalar.Scalar;
import ghidra.program.model.symbol.Reference;
import ghidra.program.model.symbol.ReferenceIterator;
import ghidra.program.model.symbol.ReferenceManager;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.lang.reflect.Array;
import java.lang.reflect.Constructor;
import java.lang.reflect.Method;
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

public class TeslaGatewayAPStateDifferentialUnresolvedStoreEAClosureTraceV364
        extends GhidraScript {

    private static final String SCRIPT_NAME =
        "TeslaGatewayAPStateDifferentialUnresolvedStoreEAClosureTraceV364";

    private static final long AP_STATE_HELPER = 0x0006F46EL;
    private static final long LOCAL_START = AP_STATE_HELPER - 0x100L;
    private static final long LOCAL_END = AP_STATE_HELPER + 0x1200L;

    private static final int MAX_PSEUDO_INSTRUCTIONS = 900;
    private static final int MAX_COMPARE_TO_BRANCH = 6;
    private static final int MAX_SIDE_INSTRUCTIONS = 260;
    private static final int MAX_CALL_DEPTH = 4;
    private static final int DECOMPILE_TIMEOUT_SECONDS = 45;

    private static final long COMMAND32_ACTION_WORD = 0x4001314CL;
    private static final long STATUS_A2BC = 0x4004A2BCL;
    private static final long ACTION_AA30 = 0x4004AA30L;
    private static final long LATE_GATE_14DDC = 0x40014DDCL;
    private static final long PREDICATE_149C0 = 0x400149C0L;
    private static final long HELPER_STATE_ACF0 = 0x4004ACF0L;
    private static final long HELPER_TIMER_AA60 = 0x4001AA60L;
    private static final long RESET_MMIO = 0xFFFE8010L;

    private static final long GOING_DOWN = 0x0009DF9CL;
    private static final long LATE_RESET_OWNER = 0x000F451EL;
    private static final long LATE_RESET_CALLSITE = 0x000F481EL;
    private static final long RESET_WRITE_1 = 0x0009D85EL;
    private static final long RESET_WRITE_2 = 0x0009BF6AL;

    private static final Pattern REGISTER_PATTERN = Pattern.compile(
        "\\br(?:[12]?\\d|3[01]|[0-9])\\b", Pattern.CASE_INSENSITIVE);

    private static final Pattern MEMORY_PATTERN = Pattern.compile(
        "(-?0x[0-9a-fA-F]+|-?[0-9]+)\\s*\\(\\s*" +
        "(r(?:[12]?\\d|3[01]|[0-9]))\\s*\\)",
        Pattern.CASE_INSENSITIVE);

    private static final Pattern NUMBER_PATTERN = Pattern.compile(
        "(?<![A-Za-z0-9_])(-?0x[0-9a-fA-F]+|-?[0-9]+)" +
        "(?![A-Za-z0-9_])");

    private Listing listing;
    private FunctionManager functionManager;
    private ReferenceManager referenceManager;
    private DecompInterface decompiler;

    private Object pseudoDisassembler;
    private Method pseudoDisassembleMethod;

    private File outputDirectory;
    private String outputStem;

    private final Map<Long, PInsn> pseudoByAddress =
        new LinkedHashMap<Long, PInsn>();
    private final Map<Long, Function> functionsByEntry =
        new LinkedHashMap<Long, Function>();
    private final Map<Long, Set<Long>> calleesByEntry =
        new LinkedHashMap<Long, Set<Long>>();
    private final Set<Long> selectedFunctions =
        new LinkedHashSet<Long>();

    private final List<String[]> contractRows = new ArrayList<String[]>();
    private final List<String[]> pseudoRows = new ArrayList<String[]>();
    private final List<String[]> branchRows = new ArrayList<String[]>();
    private final List<String[]> sideRows = new ArrayList<String[]>();
    private final List<String[]> firstRows = new ArrayList<String[]>();
    private final List<String[]> consumerRows = new ArrayList<String[]>();
    private final List<String[]> pathRows = new ArrayList<String[]>();
    private final List<String[]> assessmentRows = new ArrayList<String[]>();
    private final List<String[]> errorRows = new ArrayList<String[]>();

    private final Set<Effect> firstUniqueEffects =
        new LinkedHashSet<Effect>();

    private int comparisonCount;
    private int branchCount;
    private int reconvergenceCount;
    private int resolvedWriteCount;
    private int unresolvedStoreCount;
    private int state1UniqueCount;
    private int state2UniqueCount;
    private int knownSinkEffectCount;
    private int resetPathCount;

    private static class PInsn {
        long address;
        int length;
        String mnemonic;
        String text;
        Address fallThrough;
        Address[] flows;
        boolean callLike;
        boolean returnLike;
        boolean conditional;
    }

    private static class DecodeWork {
        final long address;
        final String path;
        DecodeWork(long address, String path) {
            this.address = address;
            this.path = path;
        }
    }

    private static class BranchCandidate {
        PInsn compare;
        PInsn branch;
        int comparedValue;
        String comparedRegister;
    }

    private static class SymbolicState {
        final Map<String, Long> registers =
            new LinkedHashMap<String, Long>();
        SymbolicState copy() {
            SymbolicState copy = new SymbolicState();
            copy.registers.putAll(registers);
            return copy;
        }
        String signature() {
            return registers.toString();
        }
    }

    private static class SideWork {
        final long address;
        final int distance;
        final SymbolicState state;
        SideWork(long address, int distance, SymbolicState state) {
            this.address = address;
            this.distance = distance;
            this.state = state;
        }
    }

    private static class Effect {
        String side;
        String semantic;
        String type;
        long site;
        Long target;
        int distance;
        String instruction;
        String classification;
        String key() {
            if (target != null) {
                return type + ":" +
                    Long.toUnsignedString(target.longValue(), 16);
            }
            return type + "@" + Long.toUnsignedString(site, 16) +
                ":" + instruction;
        }
        @Override
        public int hashCode() {
            return key().hashCode();
        }
        @Override
        public boolean equals(Object object) {
            return object instanceof Effect &&
                key().equals(((Effect)object).key());
        }
    }

    private static class SideResult {
        final String side;
        final String semantic;
        final List<Effect> effects = new ArrayList<Effect>();
        SideResult(String side, String semantic) {
            this.side = side;
            this.semantic = semantic;
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
        functionManager = currentProgram.getFunctionManager();
        referenceManager = currentProgram.getReferenceManager();

        outputDirectory = askDirectory(
            "Select V364 output directory", "Select");
        String timestamp = new SimpleDateFormat("yyyyMMdd_HHmmss")
            .format(new Date());
        outputStem = SCRIPT_NAME + "_" + timestamp;

        decompiler = new DecompInterface();
        decompiler.openProgram(currentProgram);

        try {
            emitContract();
            initialisePseudoDisassembler();
            indexFunctionsAndCalls();
            pseudoDecodeHelper();
            analyseStateBranches();
            buildExactTargetConsumers();
            buildBoundedSinkPaths();
            buildAssessment();
            writeOutputs();
        }
        catch (Exception exception) {
            errorRows.add(new String[] {"run", exception.toString()});
            buildAssessment();
            writeOutputs();
        }
        finally {
            if (decompiler != null) {
                decompiler.dispose();
            }
        }
    }

    private void emitContract() {
        contractRows.add(new String[] {
            "PROGRAM", currentProgram.getName(), "READ_ONLY"});
        contractRows.add(new String[] {
            "LANGUAGE", currentProgram.getLanguageID().toString(),
            "EXPECTED_POWERPC_BE_VLE"});
        contractRows.add(new String[] {
            "FUNCTION_COUNT",
            Long.toString((long)functionManager.getFunctionCount()),
            functionManager.getFunctionCount() >= 700
                ? "CACHE_FUNCTION_COUNT_ACCEPTABLE"
                : "FUNCTION_COUNT_BELOW_EXPECTED_CACHE_THRESHOLD"});
        contractRows.add(new String[] {
            "AP_STATE_HELPER", hex(AP_STATE_HELPER),
            "ONLY_PRIMARY_CODE_ANCHOR"});
        contractRows.add(new String[] {
            "SCOPE",
            "PSEUDO_CFG_FIRST_RECONVERGENCE_AND_UNRESOLVED_STORE_EA",
            "DOES_NOT_REPEAT_V359_TO_V363_BROAD_SEARCHES"});
    }

    private void initialisePseudoDisassembler() {
        try {
            Class<?> clazz =
                Class.forName("ghidra.app.util.PseudoDisassembler");
            Constructor<?> constructor = clazz.getConstructor(
                ghidra.program.model.listing.Program.class);
            pseudoDisassembler = constructor.newInstance(currentProgram);
            pseudoDisassembleMethod =
                clazz.getMethod("disassemble", Address.class);
        }
        catch (Throwable throwable) {
            errorRows.add(new String[] {
                "initialisePseudoDisassembler", throwable.toString()});
            pseudoDisassembler = null;
            pseudoDisassembleMethod = null;
        }
    }

    private void indexFunctionsAndCalls() {
        FunctionIterator iterator = listing.getFunctions(true);
        while (iterator.hasNext()) {
            Function function = iterator.next();
            long entry = function.getEntryPoint().getOffset();
            functionsByEntry.put(Long.valueOf(entry), function);
            Set<Long> calls = new LinkedHashSet<Long>();
            ghidra.program.model.listing.InstructionIterator instructions =
                listing.getInstructions(function.getBody(), true);
            while (instructions.hasNext()) {
                Instruction instruction = instructions.next();
                if (!instruction.getFlowType().isCall()) {
                    continue;
                }
                Address[] flows = instruction.getFlows();
                for (Address flow : flows) {
                    if (flow != null) {
                        calls.add(Long.valueOf(flow.getOffset()));
                    }
                }
            }
            calleesByEntry.put(Long.valueOf(entry), calls);
        }
    }

    private void pseudoDecodeHelper() {
        if (pseudoDisassembler == null || pseudoDisassembleMethod == null) {
            return;
        }

        Queue<DecodeWork> queue = new ArrayDeque<DecodeWork>();
        Set<Long> visited = new LinkedHashSet<Long>();
        queue.add(new DecodeWork(AP_STATE_HELPER, "entry"));

        int decoded = 0;
        while (!queue.isEmpty() && decoded < MAX_PSEUDO_INSTRUCTIONS) {
            if (monitor.isCancelled()) {
                break;
            }
            DecodeWork work = queue.remove();
            long value = work.address;
            if (Long.compareUnsigned(value, LOCAL_START) < 0 ||
                Long.compareUnsigned(value, LOCAL_END) > 0 ||
                !visited.add(Long.valueOf(value))) {
                continue;
            }

            Object object = pseudoDisassemble(address(value));
            if (object == null) {
                pseudoRows.add(new String[] {
                    work.path, hex(value), "", "", "", "", "",
                    "PSEUDO_DECODE_FAILED"});
                continue;
            }

            PInsn instruction = buildPseudoInstruction(value, object);
            pseudoByAddress.put(Long.valueOf(value), instruction);
            decoded++;

            pseudoRows.add(new String[] {
                work.path,
                hex(instruction.address),
                Integer.toString(instruction.length),
                instruction.mnemonic,
                instruction.text,
                instruction.fallThrough == null ? "" :
                    hex(instruction.fallThrough.getOffset()),
                joinAddresses(instruction.flows),
                instruction.callLike ? "CALL" :
                    instruction.returnLike ? "RETURN" :
                    instruction.conditional ? "CONDITIONAL" : "DECODED"
            });

            if (!instruction.returnLike &&
                instruction.fallThrough != null) {
                queue.add(new DecodeWork(
                    instruction.fallThrough.getOffset(),
                    work.path + " -> fallthrough"));
            }

            if (!instruction.callLike) {
                for (Address flow : instruction.flows) {
                    if (flow != null) {
                        queue.add(new DecodeWork(
                            flow.getOffset(), work.path + " -> branch"));
                    }
                }
            }
        }
    }

    private Object pseudoDisassemble(Address value) {
        try {
            return pseudoDisassembleMethod.invoke(
                pseudoDisassembler, value);
        }
        catch (Throwable throwable) {
            Throwable detail = throwable.getCause() == null
                ? throwable : throwable.getCause();
            errorRows.add(new String[] {
                "pseudoDisassemble",
                hex(value.getOffset()) + ": " + detail.toString()});
            return null;
        }
    }

    private PInsn buildPseudoInstruction(long value, Object object) {
        PInsn result = new PInsn();
        result.address = value;
        result.length = intValue(invokeNoArg(object, "getLength"), 0);
        result.mnemonic = stringValue(
            invokeNoArg(object, "getMnemonicString"));
        result.text = object.toString();
        result.fallThrough = addressValue(
            invokeNoArg(object, "getFallThrough"));
        if (result.fallThrough == null) {
            result.fallThrough = addressValue(
                invokeNoArg(object, "getDefaultFallThrough"));
        }
        result.flows = addressArrayValue(
            invokeNoArg(object, "getFlows"));
        result.callLike = isCallLike(result.mnemonic, result.text);
        result.returnLike = isReturnLike(result.mnemonic, result.text);
        result.conditional = isConditionalLike(result);
        return result;
    }

    private void analyseStateBranches() {
        List<PInsn> instructions =
            new ArrayList<PInsn>(pseudoByAddress.values());
        Collections.sort(instructions, new Comparator<PInsn>() {
            @Override
            public int compare(PInsn first, PInsn second) {
                return Long.compareUnsigned(first.address, second.address);
            }
        });

        for (PInsn compare : instructions) {
            Integer comparedValue = comparedStateValue(compare);
            if (comparedValue == null) {
                continue;
            }
            comparisonCount++;
            PInsn branch = nextConditional(compare);
            if (branch == null || branch.fallThrough == null ||
                branch.flows.length == 0 || branch.flows[0] == null) {
                branchRows.add(new String[] {
                    hex(compare.address), compare.text,
                    Integer.toString(comparedValue.intValue()), "", "", "",
                    "COMPARE_WITHOUT_RECOVERED_TWO_WAY_BRANCH"});
                continue;
            }

            branchCount++;
            BranchCandidate candidate = new BranchCandidate();
            candidate.compare = compare;
            candidate.branch = branch;
            candidate.comparedValue = comparedValue.intValue();
            candidate.comparedRegister = firstRegister(compare.text);

            long taken = branch.flows[0].getOffset();
            long fall = branch.fallThrough.getOffset();
            long reconvergence = firstReconvergence(taken, fall);
            if (reconvergence >= 0) {
                reconvergenceCount++;
            }

            String[] semantics = branchSemantics(
                branch, candidate.comparedValue);

            branchRows.add(new String[] {
                hex(compare.address), compare.text,
                Integer.toString(candidate.comparedValue),
                candidate.comparedRegister,
                hex(branch.address), branch.text,
                hex(taken), semantics[0],
                hex(fall), semantics[1],
                reconvergence < 0 ? "" : hex(reconvergence),
                reconvergence < 0
                    ? "NO_FIRST_RECONVERGENCE_WITHIN_BOUND"
                    : "FIRST_RECONVERGENCE_RECOVERED"
            });

            SideResult takenResult = traverseSide(
                taken, reconvergence, "taken", semantics[0]);
            SideResult fallResult = traverseSide(
                fall, reconvergence, "fallthrough", semantics[1]);

            emitSideEffects(compare, branch, takenResult);
            emitSideEffects(compare, branch, fallResult);
            emitFirstUniqueEffects(
                compare, branch, reconvergence,
                takenResult, fallResult);
        }
    }

    private Integer comparedStateValue(PInsn instruction) {
        if (instruction == null) {
            return null;
        }
        String mnemonic = lower(instruction.mnemonic);
        if (!mnemonic.contains("cmp")) {
            return null;
        }
        List<Long> numbers = numbersInText(instruction.text);
        for (int index = numbers.size() - 1; index >= 0; index--) {
            long value = numbers.get(index).longValue();
            if (value == 1L || value == 2L) {
                return Integer.valueOf((int)value);
            }
        }
        return null;
    }

    private PInsn nextConditional(PInsn compare) {
        PInsn cursor = compare;
        for (int count = 0; count < MAX_COMPARE_TO_BRANCH; count++) {
            if (cursor.fallThrough == null) {
                return null;
            }
            cursor = pseudoByAddress.get(
                Long.valueOf(cursor.fallThrough.getOffset()));
            if (cursor == null) {
                return null;
            }
            if (cursor.conditional) {
                return cursor;
            }
            if (cursor.callLike || cursor.returnLike) {
                return null;
            }
        }
        return null;
    }

    private long firstReconvergence(long firstStart, long secondStart) {
        Map<Long, Integer> first = reachableDistances(firstStart);
        Map<Long, Integer> second = reachableDistances(secondStart);
        long best = -1L;
        int bestScore = Integer.MAX_VALUE;
        int bestSum = Integer.MAX_VALUE;

        for (Map.Entry<Long, Integer> entry : first.entrySet()) {
            Integer other = second.get(entry.getKey());
            if (other == null) {
                continue;
            }
            int score = Math.max(entry.getValue().intValue(),
                other.intValue());
            int sum = entry.getValue().intValue() + other.intValue();
            if (score < bestScore ||
                (score == bestScore && sum < bestSum)) {
                best = entry.getKey().longValue();
                bestScore = score;
                bestSum = sum;
            }
        }
        return best;
    }

    private Map<Long, Integer> reachableDistances(long start) {
        Map<Long, Integer> distances =
            new LinkedHashMap<Long, Integer>();
        Queue<long[]> queue = new ArrayDeque<long[]>();
        queue.add(new long[] {start, 0L});

        while (!queue.isEmpty()) {
            long[] item = queue.remove();
            long value = item[0];
            int distance = (int)item[1];
            if (distance >= MAX_SIDE_INSTRUCTIONS ||
                distances.containsKey(Long.valueOf(value))) {
                continue;
            }
            PInsn instruction =
                pseudoByAddress.get(Long.valueOf(value));
            if (instruction == null) {
                continue;
            }
            distances.put(Long.valueOf(value), Integer.valueOf(distance));
            if (instruction.returnLike) {
                continue;
            }
            if (instruction.fallThrough != null) {
                queue.add(new long[] {
                    instruction.fallThrough.getOffset(), distance + 1L});
            }
            if (!instruction.callLike) {
                for (Address flow : instruction.flows) {
                    if (flow != null) {
                        queue.add(new long[] {
                            flow.getOffset(), distance + 1L});
                    }
                }
            }
        }
        return distances;
    }

    private SideResult traverseSide(
            long start, long reconvergence,
            String side, String semantic) {

        SideResult result = new SideResult(side, semantic);
        Queue<SideWork> queue = new ArrayDeque<SideWork>();
        Set<String> visited = new LinkedHashSet<String>();
        queue.add(new SideWork(start, 0, new SymbolicState()));

        while (!queue.isEmpty()) {
            SideWork work = queue.remove();
            if (work.distance >= MAX_SIDE_INSTRUCTIONS ||
                (reconvergence >= 0 && work.address == reconvergence)) {
                continue;
            }

            PInsn instruction = pseudoByAddress.get(
                Long.valueOf(work.address));
            if (instruction == null) {
                continue;
            }

            String visitKey = hex(work.address) + ":" +
                work.state.signature();
            if (!visited.add(visitKey)) {
                continue;
            }

            SymbolicState nextState = work.state.copy();
            Effect effect = processInstruction(
                instruction, nextState, side, semantic, work.distance);
            if (effect != null) {
                result.effects.add(effect);
            }

            if (instruction.returnLike) {
                continue;
            }
            if (instruction.fallThrough != null) {
                queue.add(new SideWork(
                    instruction.fallThrough.getOffset(),
                    work.distance + 1, nextState.copy()));
            }
            if (!instruction.callLike) {
                for (Address flow : instruction.flows) {
                    if (flow != null) {
                        queue.add(new SideWork(
                            flow.getOffset(), work.distance + 1,
                            nextState.copy()));
                    }
                }
            }
        }
        return result;
    }

    private Effect processInstruction(
            PInsn instruction, SymbolicState state,
            String side, String semantic, int distance) {

        String mnemonic = lower(instruction.mnemonic);
        List<String> registers = registersInText(instruction.text);

        if (instruction.callLike) {
            if (instruction.flows.length > 0 &&
                instruction.flows[0] != null) {
                Effect effect = new Effect();
                effect.side = side;
                effect.semantic = semantic;
                effect.type = "CALL";
                effect.site = instruction.address;
                effect.target = Long.valueOf(
                    instruction.flows[0].getOffset());
                effect.distance = distance;
                effect.instruction = instruction.text;
                effect.classification = classifyCodeTarget(
                    effect.target.longValue());
                return effect;
            }
            Effect effect = new Effect();
            effect.side = side;
            effect.semantic = semantic;
            effect.type = "CALL_INDIRECT";
            effect.site = instruction.address;
            effect.target = null;
            effect.distance = distance;
            effect.instruction = instruction.text;
            effect.classification = "UNRESOLVED_INDIRECT_CALL";
            return effect;
        }

        if (isStoreMnemonic(mnemonic)) {
            Long target = resolveStoreTarget(
                mnemonic, instruction.text, registers, state);
            Effect effect = new Effect();
            effect.side = side;
            effect.semantic = semantic;
            effect.type = target == null
                ? "STORE_UNRESOLVED" : "WRITE";
            effect.site = instruction.address;
            effect.target = target;
            effect.distance = distance;
            effect.instruction = instruction.text;
            effect.classification = target == null
                ? "COMPUTED_STORE_EA_UNRESOLVED"
                : classifyDataTarget(target.longValue());
            if (target == null) {
                unresolvedStoreCount++;
            }
            else {
                resolvedWriteCount++;
            }
            return effect;
        }

        updateRegisterState(mnemonic, instruction.text, registers, state);
        return null;
    }

    private Long resolveStoreTarget(
            String mnemonic, String text,
            List<String> registers, SymbolicState state) {

        Matcher memoryMatcher = MEMORY_PATTERN.matcher(text);
        if (memoryMatcher.find()) {
            long displacement = parseNumber(memoryMatcher.group(1));
            String base = lower(memoryMatcher.group(2));
            Long baseValue = state.registers.get(base);
            if (baseValue != null) {
                return Long.valueOf(
                    (baseValue.longValue() + displacement) & 0xffffffffL);
            }
            return null;
        }

        if (isIndexedMemoryMnemonic(mnemonic) &&
            registers.size() >= 3) {
            String firstAddressRegister = registers.get(1);
            String secondAddressRegister = registers.get(2);
            Long first = state.registers.get(firstAddressRegister);
            Long second = state.registers.get(secondAddressRegister);
            if (first != null && second != null) {
                return Long.valueOf(
                    (first.longValue() + second.longValue()) & 0xffffffffL);
            }
        }
        return null;
    }

    private void updateRegisterState(
            String mnemonic, String text,
            List<String> registers, SymbolicState state) {

        if (registers.isEmpty() ||
            mnemonic.contains("cmp") || mnemonic.contains("tst") ||
            mnemonic.startsWith("b") || mnemonic.startsWith("mt") ||
            isStoreMnemonic(mnemonic)) {
            return;
        }

        String destination = registers.get(0);
        Long value = null;
        Long immediate = lastNumber(text);

        if ((mnemonic.contains("li") && !mnemonic.contains("lis")) &&
            immediate != null) {
            value = Long.valueOf(immediate.longValue() & 0xffffffffL);
        }
        else if ((mnemonic.contains("lis") ||
                  mnemonic.contains("e_lis")) &&
                 immediate != null) {
            value = Long.valueOf(
                (immediate.longValue() << 16) & 0xffffffffL);
        }
        else if ((mnemonic.contains("mr") ||
                  mnemonic.contains("or") && registers.size() >= 3 &&
                  registers.get(1).equals(registers.get(2))) &&
                 registers.size() >= 2) {
            value = state.registers.get(registers.get(1));
        }
        else if ((mnemonic.contains("addi") ||
                  mnemonic.contains("add16i")) &&
                 registers.size() >= 2 && immediate != null) {
            Long base = state.registers.get(registers.get(1));
            if (base != null) {
                value = Long.valueOf(
                    (base.longValue() + immediate.longValue()) &
                    0xffffffffL);
            }
        }
        else if ((mnemonic.contains("ori") ||
                  mnemonic.contains("or2i")) &&
                 registers.size() >= 2 && immediate != null) {
            Long base = state.registers.get(registers.get(1));
            if (base != null) {
                value = Long.valueOf(
                    (base.longValue() | immediate.longValue()) &
                    0xffffffffL);
            }
        }
        else if ((mnemonic.equals("add") ||
                  mnemonic.endsWith("_add")) &&
                 registers.size() >= 3) {
            Long first = state.registers.get(registers.get(1));
            Long second = state.registers.get(registers.get(2));
            if (first != null && second != null) {
                value = Long.valueOf(
                    (first.longValue() + second.longValue()) &
                    0xffffffffL);
            }
        }

        if (value == null) {
            state.registers.remove(destination);
        }
        else {
            state.registers.put(destination, value);
        }
    }

    private void emitSideEffects(
            PInsn compare, PInsn branch, SideResult result) {
        if (result.effects.isEmpty()) {
            sideRows.add(new String[] {
                hex(compare.address), hex(branch.address),
                result.side, result.semantic, "", "", "", "", "",
                "NO_EFFECT_BEFORE_RECONVERGENCE"});
            return;
        }
        Collections.sort(result.effects, effectComparator());
        for (Effect effect : result.effects) {
            sideRows.add(effectRow(compare, branch, effect,
                "SIDE_EFFECT_BEFORE_RECONVERGENCE"));
        }
    }

    private void emitFirstUniqueEffects(
            PInsn compare, PInsn branch, long reconvergence,
            SideResult first, SideResult second) {

        Set<String> firstKeys = effectKeys(second.effects);
        Set<String> secondKeys = effectKeys(first.effects);
        Effect firstUnique = firstUniqueEffect(first.effects, firstKeys);
        Effect secondUnique = firstUniqueEffect(second.effects, secondKeys);

        emitFirstRow(compare, branch, reconvergence, firstUnique,
            first.side, first.semantic);
        emitFirstRow(compare, branch, reconvergence, secondUnique,
            second.side, second.semantic);
    }

    private Effect firstUniqueEffect(
            List<Effect> effects, Set<String> otherKeys) {
        List<Effect> sorted = new ArrayList<Effect>(effects);
        Collections.sort(sorted, effectComparator());
        for (Effect effect : sorted) {
            if (!otherKeys.contains(effect.key())) {
                return effect;
            }
        }
        return null;
    }

    private void emitFirstRow(
            PInsn compare, PInsn branch, long reconvergence,
            Effect effect, String side, String semantic) {

        if (effect == null) {
            firstRows.add(new String[] {
                hex(compare.address), hex(branch.address), side, semantic,
                reconvergence < 0 ? "" : hex(reconvergence),
                "", "", "", "", "",
                "NO_BRANCH_UNIQUE_EFFECT_BEFORE_RECONVERGENCE"});
            return;
        }

        firstUniqueEffects.add(effect);
        if (semantic.contains("STATE_EQ_1")) {
            state1UniqueCount++;
        }
        if (semantic.contains("STATE_EQ_2")) {
            state2UniqueCount++;
        }
        if (isKnownSinkClassification(effect.classification)) {
            knownSinkEffectCount++;
        }

        firstRows.add(new String[] {
            hex(compare.address), hex(branch.address), side, semantic,
            reconvergence < 0 ? "" : hex(reconvergence),
            Integer.toString(effect.distance),
            hex(effect.site), effect.type,
            effect.target == null ? "" : hex(effect.target.longValue()),
            effect.classification,
            effect.instruction
        });
    }

    private String[] effectRow(
            PInsn compare, PInsn branch, Effect effect,
            String note) {
        return new String[] {
            hex(compare.address), hex(branch.address),
            effect.side, effect.semantic,
            Integer.toString(effect.distance),
            hex(effect.site), effect.type,
            effect.target == null ? "" : hex(effect.target.longValue()),
            effect.classification,
            note + " | " + effect.instruction
        };
    }

    private void buildExactTargetConsumers() {
        Set<Long> targets = new LinkedHashSet<Long>();
        for (Effect effect : firstUniqueEffects) {
            if (effect.target != null && effect.type.equals("WRITE") &&
                isRamAddress(effect.target.longValue())) {
                targets.add(effect.target);
            }
        }

        for (Long targetValue : targets) {
            long target = targetValue.longValue();
            ReferenceIterator references =
                referenceManager.getReferencesTo(address(target));
            int count = 0;
            while (references.hasNext()) {
                Reference reference = references.next();
                Address from = reference.getFromAddress();
                Instruction instruction =
                    listing.getInstructionContaining(from);
                Function owner =
                    functionManager.getFunctionContaining(from);
                if (owner != null) {
                    selectedFunctions.add(Long.valueOf(
                        owner.getEntryPoint().getOffset()));
                }
                String type = reference.getReferenceType().toString();
                consumerRows.add(new String[] {
                    hex(target), hex(from.getOffset()), type,
                    owner == null ? "" :
                        hex(owner.getEntryPoint().getOffset()),
                    owner == null ? "" : owner.getName(),
                    instruction == null ? "" : instruction.toString(),
                    type.toUpperCase(Locale.ROOT).contains("READ")
                        ? "EXACT_READER_OF_UNIQUE_TARGET"
                        : type.toUpperCase(Locale.ROOT).contains("WRITE")
                            ? "EXACT_ADDITIONAL_WRITER_OF_UNIQUE_TARGET"
                            : "EXACT_REFERENCE_TO_UNIQUE_TARGET"
                });
                count++;
            }
            if (count == 0) {
                consumerRows.add(new String[] {
                    hex(target), "", "", "", "", "",
                    "NO_EXACT_GHIDRA_REFERENCE_TO_UNIQUE_TARGET"});
            }
        }
    }

    private void buildBoundedSinkPaths() {
        Set<Long> sources = new LinkedHashSet<Long>();
        for (Effect effect : firstUniqueEffects) {
            if (effect.target != null && effect.type.equals("CALL")) {
                sources.add(effect.target);
            }
        }

        Set<Long> resetTargets = new LinkedHashSet<Long>();
        resetTargets.add(Long.valueOf(GOING_DOWN));
        resetTargets.add(Long.valueOf(LATE_RESET_OWNER));
        resetTargets.add(Long.valueOf(LATE_RESET_CALLSITE));
        resetTargets.add(Long.valueOf(RESET_WRITE_1));
        resetTargets.add(Long.valueOf(RESET_WRITE_2));

        for (Long sourceValue : sources) {
            long source = sourceValue.longValue();
            Queue<CallNode> queue = new ArrayDeque<CallNode>();
            Set<Long> visited = new LinkedHashSet<Long>();
            List<Long> initial = new ArrayList<Long>();
            initial.add(Long.valueOf(source));
            queue.add(new CallNode(source, 0, initial));
            visited.add(Long.valueOf(source));

            boolean found = false;
            while (!queue.isEmpty()) {
                CallNode node = queue.remove();
                if (node.depth >= MAX_CALL_DEPTH) {
                    continue;
                }
                Set<Long> callees = calleesByEntry.get(
                    Long.valueOf(node.entry));
                if (callees == null) {
                    continue;
                }
                for (Long calleeValue : callees) {
                    long callee = calleeValue.longValue();
                    List<Long> path = new ArrayList<Long>(node.path);
                    path.add(calleeValue);
                    if (resetTargets.contains(calleeValue)) {
                        found = true;
                        resetPathCount++;
                        pathRows.add(new String[] {
                            hex(source), Integer.toString(node.depth + 1),
                            hex(callee), pathString(path),
                            "UNIQUE_CALL_REACHES_KNOWN_RESET_ANCHOR"});
                        Function function = functionAtOrContaining(callee);
                        if (function != null) {
                            selectedFunctions.add(Long.valueOf(
                                function.getEntryPoint().getOffset()));
                        }
                    }
                    if (visited.add(calleeValue)) {
                        queue.add(new CallNode(
                            callee, node.depth + 1, path));
                    }
                }
            }
            if (!found) {
                pathRows.add(new String[] {
                    hex(source), "", "", hex(source),
                    "NO_KNOWN_RESET_ANCHOR_WITHIN_BOUND"});
            }
        }
    }

    private void buildAssessment() {
        String classification;
        if (pseudoByAddress.isEmpty()) {
            classification = "AP_STATE_HELPER_PSEUDO_DECODE_FAILED";
        }
        else if (comparisonCount == 0 || branchCount == 0) {
            classification =
                "AP_STATE_HELPER_DECODED_BUT_NO_STATE1_STATE2_BRANCH_RECOVERED";
        }
        else if (state2UniqueCount > 0 &&
            (knownSinkEffectCount > 0 || resetPathCount > 0)) {
            classification =
                "AP_STATE2_FIRST_UNIQUE_EFFECT_HAS_PENDING_OR_RESET_BRIDGE";
        }
        else if (state2UniqueCount > 0) {
            classification =
                "AP_STATE2_FIRST_UNIQUE_EFFECT_RECOVERED_NO_KNOWN_SINK_BRIDGE";
        }
        else if (state1UniqueCount > 0) {
            classification =
                "STATE1_ONLY_FIRST_UNIQUE_EFFECT_RECOVERED";
        }
        else if (reconvergenceCount > 0) {
            classification =
                "STATE1_STATE2_RECONVERGE_WITHOUT_UNIQUE_EFFECT";
        }
        else {
            classification =
                "STATE_DIFFERENTIAL_REMAINS_UNRESOLVED";
        }

        assessmentRows.add(new String[] {
            classification,
            Integer.toString(pseudoByAddress.size()),
            Integer.toString(comparisonCount),
            Integer.toString(branchCount),
            Integer.toString(reconvergenceCount),
            Integer.toString(resolvedWriteCount),
            Integer.toString(unresolvedStoreCount),
            Integer.toString(state1UniqueCount),
            Integer.toString(state2UniqueCount),
            Integer.toString(knownSinkEffectCount),
            Integer.toString(resetPathCount),
            Integer.toString(errorRows.size())
        });
    }

    private void writeOutputs() throws Exception {
        List<File> files = new ArrayList<File>();

        files.add(writeCsv(outputStem + "_scope_contract.csv",
            new String[] {"item", "value", "classification"},
            contractRows));
        files.add(writeCsv(outputStem + "_pseudo_instructions.csv",
            new String[] {"path", "address", "length", "mnemonic",
                "instruction", "fallthrough", "flows", "classification"},
            pseudoRows));
        files.add(writeCsv(outputStem + "_state_branch_candidates.csv",
            new String[] {"compare_site", "compare_instruction",
                "compared_value", "compared_register", "branch_site",
                "branch_instruction", "taken", "taken_semantic",
                "fallthrough", "fallthrough_semantic",
                "first_reconvergence", "classification"},
            branchRows));
        files.add(writeCsv(outputStem + "_side_effects_before_reconvergence.csv",
            new String[] {"compare_site", "branch_site", "side",
                "semantic", "distance", "effect_site", "effect_type",
                "target", "classification", "evidence"},
            sideRows));
        files.add(writeCsv(outputStem + "_first_unique_effects.csv",
            new String[] {"compare_site", "branch_site", "side",
                "semantic", "first_reconvergence", "distance",
                "effect_site", "effect_type", "target",
                "classification", "instruction"},
            firstRows));
        files.add(writeCsv(outputStem + "_exact_unique_target_consumers.csv",
            new String[] {"target", "reference_site", "reference_type",
                "owner", "owner_name", "instruction", "classification"},
            consumerRows));
        files.add(writeCsv(outputStem + "_bounded_reset_paths.csv",
            new String[] {"source_call", "depth", "reset_target",
                "path", "classification"},
            pathRows));
        files.add(writeCsv(outputStem + "_assessment.csv",
            new String[] {"classification", "pseudo_instructions",
                "state_comparisons", "two_way_branches",
                "first_reconvergences", "resolved_writes",
                "unresolved_stores", "state1_first_unique",
                "state2_first_unique", "known_sink_effects",
                "reset_paths", "errors"},
            assessmentRows));
        files.add(writeSelectedDecompilation());
        files.add(writeCsv(outputStem + "_errors.csv",
            new String[] {"stage", "detail"}, errorRows));
        files.add(writeSummary());

        File bundle = new File(
            outputDirectory, outputStem + "_bundle.zip");
        zipFiles(bundle, files);
        println("V364 bundle: " + bundle.getAbsolutePath());
    }

    private File writeSelectedDecompilation() throws IOException {
        File file = new File(outputDirectory,
            outputStem + "_selected_decompilation.txt");
        BufferedWriter writer = writer(file);
        try {
            List<Long> entries = new ArrayList<Long>(selectedFunctions);
            Collections.sort(entries);
            for (Long entryValue : entries) {
                Function function = functionsByEntry.get(entryValue);
                if (function == null) {
                    function = functionAtOrContaining(entryValue.longValue());
                }
                if (function == null) {
                    continue;
                }
                writer.write("==================================================\r\n");
                writer.write(hex(function.getEntryPoint().getOffset()) +
                    " " + function.getName() + "\r\n");
                writer.write("==================================================\r\n");
                try {
                    DecompileResults results = decompiler.decompileFunction(
                        function, DECOMPILE_TIMEOUT_SECONDS, monitor);
                    if (results != null && results.decompileCompleted() &&
                        results.getDecompiledFunction() != null) {
                        writer.write(results.getDecompiledFunction().getC());
                    }
                    else {
                        writer.write("<decompilation unavailable>");
                    }
                }
                catch (Exception exception) {
                    writer.write("<decompilation error: " +
                        exception.toString() + ">");
                }
                writer.write("\r\n\r\n");
            }
        }
        finally {
            writer.close();
        }
        return file;
    }

    private File writeSummary() throws IOException {
        File file = new File(outputDirectory,
            outputStem + "_summary.md");
        BufferedWriter writer = writer(file);
        try {
            String classification = assessmentRows.isEmpty()
                ? "NO_ASSESSMENT" : assessmentRows.get(0)[0];
            writer.write("# Tesla Gateway AP state differential V364\r\n\r\n");
            writer.write("## Classification\r\n\r\n");
            writer.write("`" + classification + "`\r\n\r\n");
            writer.write("## Counts\r\n\r\n");
            writer.write("- Pseudo instructions: " +
                pseudoByAddress.size() + "\r\n");
            writer.write("- State comparisons: " +
                comparisonCount + "\r\n");
            writer.write("- Two-way branches: " +
                branchCount + "\r\n");
            writer.write("- First reconvergences: " +
                reconvergenceCount + "\r\n");
            writer.write("- Resolved computed writes: " +
                resolvedWriteCount + "\r\n");
            writer.write("- Unresolved stores: " +
                unresolvedStoreCount + "\r\n");
            writer.write("- State-1 first unique effects: " +
                state1UniqueCount + "\r\n");
            writer.write("- State-2 first unique effects: " +
                state2UniqueCount + "\r\n");
            writer.write("- Known sink effects: " +
                knownSinkEffectCount + "\r\n");
            writer.write("- Bounded reset paths: " +
                resetPathCount + "\r\n");
            writer.write("- Errors: " + errorRows.size() + "\r\n\r\n");
            writer.write("## Interpretation\r\n\r\n");
            writer.write("This script intentionally does not repeat broad " +
                "AP source, descriptor, callback, A2BC writer, or reset-owner " +
                "searches. Review `_first_unique_effects.csv` first. If a " +
                "single state-2 unique RAM target is recovered without a " +
                "known sink bridge, the next pass should follow only that " +
                "exact target.\r\n");
        }
        finally {
            writer.close();
        }
        return file;
    }

    private File writeCsv(
            String fileName, String[] header,
            List<String[]> rows) throws IOException {
        File file = new File(outputDirectory, fileName);
        BufferedWriter writer = writer(file);
        try {
            writeCsvRow(writer, header);
            for (String[] row : rows) {
                writeCsvRow(writer, row);
            }
        }
        finally {
            writer.close();
        }
        return file;
    }

    private BufferedWriter writer(File file) throws IOException {
        return new BufferedWriter(new OutputStreamWriter(
            new FileOutputStream(file), StandardCharsets.UTF_8));
    }

    private void writeCsvRow(
            BufferedWriter writer, String[] values) throws IOException {
        for (int index = 0; index < values.length; index++) {
            if (index != 0) {
                writer.write(',');
            }
            writer.write(csv(values[index]));
        }
        writer.write("\r\n");
    }

    private String csv(String value) {
        String text = value == null ? "" : value;
        return "\"" + text.replace("\"", "\"\"") + "\"";
    }

    private void zipFiles(File archive, List<File> files)
            throws IOException {
        ZipOutputStream zip = new ZipOutputStream(
            new FileOutputStream(archive));
        byte[] buffer = new byte[65536];
        try {
            for (File file : files) {
                if (file == null || !file.isFile()) {
                    continue;
                }
                zip.putNextEntry(new ZipEntry(file.getName()));
                FileInputStream input = new FileInputStream(file);
                try {
                    int read;
                    while ((read = input.read(buffer)) >= 0) {
                        if (read > 0) {
                            zip.write(buffer, 0, read);
                        }
                    }
                }
                finally {
                    input.close();
                }
                zip.closeEntry();
            }
        }
        finally {
            zip.close();
        }
    }

    private Comparator<Effect> effectComparator() {
        return new Comparator<Effect>() {
            @Override
            public int compare(Effect first, Effect second) {
                if (first.distance != second.distance) {
                    return first.distance - second.distance;
                }
                return Long.compareUnsigned(first.site, second.site);
            }
        };
    }

    private Set<String> effectKeys(List<Effect> effects) {
        Set<String> keys = new LinkedHashSet<String>();
        for (Effect effect : effects) {
            keys.add(effect.key());
        }
        return keys;
    }

    private String[] branchSemantics(PInsn branch, int value) {
        String mnemonic = lower(branch.mnemonic);
        String equals = "STATE_EQ_" + value;
        String notEquals = "STATE_NE_" + value;
        if (mnemonic.contains("eq")) {
            return new String[] {equals, notEquals};
        }
        if (mnemonic.contains("ne")) {
            return new String[] {notEquals, equals};
        }
        return new String[] {
            "STATE_CONDITION_TAKEN_REQUIRES_REVIEW",
            "STATE_CONDITION_FALLTHROUGH_REQUIRES_REVIEW"};
    }

    private String classifyDataTarget(long value) {
        if (value >= COMMAND32_ACTION_WORD &&
            value <= COMMAND32_ACTION_WORD + 3L) {
            return "COMMAND32_ACTION_WORD";
        }
        if (value >= STATUS_A2BC && value <= STATUS_A2BC + 3L) {
            return "STATUS_A2BC";
        }
        if (value >= ACTION_AA30 && value <= ACTION_AA30 + 3L) {
            return "ACTION_AA30";
        }
        if (value >= LATE_GATE_14DDC &&
            value <= LATE_GATE_14DDC + 3L) {
            return "LATE_RESET_GATE_14DDC";
        }
        if (value >= PREDICATE_149C0 &&
            value <= PREDICATE_149C0 + 3L) {
            return "PREDICATE_INPUT_149C0";
        }
        if (value >= HELPER_STATE_ACF0 &&
            value <= HELPER_STATE_ACF0 + 3L) {
            return "HELPER_STATE_ACF0";
        }
        if (value >= HELPER_TIMER_AA60 &&
            value <= HELPER_TIMER_AA60 + 3L) {
            return "HELPER_TIMER_AA60";
        }
        if (value >= RESET_MMIO && value <= RESET_MMIO + 3L) {
            return "RESET_MMIO";
        }
        if (isRamAddress(value)) {
            return "OTHER_GLOBAL_RAM";
        }
        return "OTHER_DATA";
    }

    private String classifyCodeTarget(long value) {
        if (value == GOING_DOWN) {
            return "GOING_DOWN";
        }
        if (value == LATE_RESET_OWNER) {
            return "LATE_RESET_OWNER";
        }
        if (value == LATE_RESET_CALLSITE) {
            return "LATE_RESET_CALLSITE";
        }
        if (value == RESET_WRITE_1 || value == RESET_WRITE_2) {
            return "RESET_WRITE_OWNER";
        }
        Function function = functionAtOrContaining(value);
        return function == null ?
            "OTHER_CODE_UNOWNED" : "OTHER_CODE_FUNCTION";
    }

    private boolean isKnownSinkClassification(String value) {
        if (value == null) {
            return false;
        }
        return value.equals("COMMAND32_ACTION_WORD") ||
            value.equals("STATUS_A2BC") ||
            value.equals("ACTION_AA30") ||
            value.equals("LATE_RESET_GATE_14DDC") ||
            value.equals("PREDICATE_INPUT_149C0") ||
            value.equals("HELPER_STATE_ACF0") ||
            value.equals("HELPER_TIMER_AA60") ||
            value.equals("RESET_MMIO") ||
            value.equals("GOING_DOWN") ||
            value.equals("LATE_RESET_OWNER") ||
            value.equals("LATE_RESET_CALLSITE") ||
            value.equals("RESET_WRITE_OWNER");
    }

    private boolean isRamAddress(long value) {
        return value >= 0x40000000L && value <= 0x400FFFFFL;
    }

    private boolean isStoreMnemonic(String mnemonic) {
        String value = lower(mnemonic);
        return value.contains("stw") || value.contains("stb") ||
            value.contains("sth") || value.contains("std") ||
            value.startsWith("st") || value.contains("_st");
    }

    private boolean isIndexedMemoryMnemonic(String mnemonic) {
        String value = lower(mnemonic);
        return value.endsWith("stwx") || value.endsWith("stbx") ||
            value.endsWith("sthx") || value.equals("stwx") ||
            value.equals("stbx") || value.equals("sthx");
    }

    private boolean isCallLike(String mnemonic, String text) {
        String value = lower(mnemonic + " " + text);
        return value.contains("bl ") || value.endsWith(" bl") ||
            value.contains("e_bl") || value.contains("se_bl") ||
            value.contains("bctrl") || value.contains("blrl");
    }

    private boolean isReturnLike(String mnemonic, String text) {
        String value = lower(mnemonic + " " + text);
        return value.contains("blr") && !value.contains("blrl");
    }

    private boolean isConditionalLike(PInsn instruction) {
        if (instruction.callLike || instruction.returnLike ||
            instruction.fallThrough == null ||
            instruction.flows == null || instruction.flows.length == 0) {
            return false;
        }
        String value = lower(instruction.mnemonic);
        return value.startsWith("b") || value.contains("_b");
    }

    private Function functionAtOrContaining(long value) {
        Address location = address(value);
        Function function = functionManager.getFunctionAt(location);
        if (function == null) {
            function = functionManager.getFunctionContaining(location);
        }
        return function;
    }

    private List<String> registersInText(String text) {
        List<String> values = new ArrayList<String>();
        Matcher matcher = REGISTER_PATTERN.matcher(text == null ? "" : text);
        while (matcher.find()) {
            values.add(lower(matcher.group()));
        }
        return values;
    }

    private String firstRegister(String text) {
        List<String> registers = registersInText(text);
        return registers.isEmpty() ? "" : registers.get(0);
    }

    private List<Long> numbersInText(String text) {
        List<Long> values = new ArrayList<Long>();
        Matcher matcher = NUMBER_PATTERN.matcher(text == null ? "" : text);
        while (matcher.find()) {
            try {
                values.add(Long.valueOf(parseNumber(matcher.group(1))));
            }
            catch (Exception ignored) {
            }
        }
        return values;
    }

    private Long lastNumber(String text) {
        List<Long> values = numbersInText(text);
        return values.isEmpty() ? null : values.get(values.size() - 1);
    }

    private long parseNumber(String text) {
        String value = lower(text.trim());
        boolean negative = value.startsWith("-");
        if (negative) {
            value = value.substring(1);
        }
        long parsed = value.startsWith("0x")
            ? Long.parseUnsignedLong(value.substring(2), 16)
            : Long.parseLong(value, 10);
        return negative ? -parsed : parsed;
    }

    private String pathString(List<Long> path) {
        StringBuilder builder = new StringBuilder();
        for (Long value : path) {
            if (builder.length() != 0) {
                builder.append(" -> ");
            }
            builder.append(hex(value.longValue()));
        }
        return builder.toString();
    }

    private String joinAddresses(Address[] values) {
        StringBuilder builder = new StringBuilder();
        if (values != null) {
            for (Address value : values) {
                if (value == null) {
                    continue;
                }
                if (builder.length() != 0) {
                    builder.append(';');
                }
                builder.append(hex(value.getOffset()));
            }
        }
        return builder.toString();
    }

    private Object invokeNoArg(Object target, String name) {
        if (target == null) {
            return null;
        }
        try {
            Method method = target.getClass().getMethod(name);
            return method.invoke(target);
        }
        catch (Throwable ignored) {
            return null;
        }
    }

    private int intValue(Object value, int fallback) {
        return value instanceof Number
            ? ((Number)value).intValue() : fallback;
    }

    private String stringValue(Object value) {
        return value == null ? "" : value.toString();
    }

    private Address addressValue(Object value) {
        return value instanceof Address ? (Address)value : null;
    }

    private Address[] addressArrayValue(Object value) {
        if (value == null) {
            return new Address[0];
        }
        if (value instanceof Address[]) {
            return (Address[])value;
        }
        if (!value.getClass().isArray()) {
            return new Address[0];
        }
        List<Address> addresses = new ArrayList<Address>();
        int length = Array.getLength(value);
        for (int index = 0; index < length; index++) {
            Object item = Array.get(value, index);
            if (item instanceof Address) {
                addresses.add((Address)item);
            }
        }
        return addresses.toArray(new Address[addresses.size()]);
    }

    private Address address(long value) {
        return currentProgram.getAddressFactory()
            .getDefaultAddressSpace().getAddress(value);
    }

    private String hex(long value) {
        return String.format(Locale.ROOT, "0x%08X", value);
    }

    private String lower(String value) {
        return value == null ? "" : value.toLowerCase(Locale.ROOT);
    }
}
