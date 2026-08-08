// TeslaGatewayNMObjectRawTimerCallerAndCallbackClosureTraceV407.java
//
// Read-only / rollback-only focused analysis for Ghidra 12.1.2.
//
// V406 did not disprove the NM timer path. It failed at the analysis boundary:
//   - 0x000F8B24 was not defined in the current listing;
//   - all normal direct-call discovery therefore returned zero timer callers;
//   - the three callback bodies were recovered only after the call graph had
//     already been built, so helper closure from those callbacks was stale;
//   - attempts to force VLE context over already-decoded callback instructions
//     raised ContextChangeException.
//
// V407 corrects only those defects. It does not rescan command 0x33, A2BC,
// Autopilot consumers, 0x97AA2, 0x95FCE, state 6/7, or the final reset path.
//
// It:
//   1. scans raw application bytes for VLE e_bl encodings whose resolved target
//      is exactly 0x000F8B24;
//   2. temporarily recovers the bounded caller region around each raw call and
//      samples r3-r7 immediately before the call;
//   3. identifies exact 0x4004ACA8 timer registrations and their callbacks;
//   4. recovers the three known callback bodies without overwriting existing
//      VLE context where instructions are already present;
//   5. recursively recovers bounded direct callees from those callbacks;
//   6. rebuilds helper closure AFTER temporary recovery;
//   7. records every direct 0x00097E32 call reachable from the callback family,
//      including r3-r6, target-state semantics and nearest predecessor branch;
//   8. exports selected decompilation and raw timer-dispatch context.
//
// Firmware bytes are never written. All temporary listing/context/function
// changes are inside a transaction that is always rolled back.
//
// @category TeslaGateway.Analysis
// @menupath Tools.Tesla.Trace NM Raw Timer Caller Callback Closure V407

import ghidra.app.cmd.disassemble.PowerPCDisassembleCommand;
import ghidra.app.decompiler.DecompInterface;
import ghidra.app.decompiler.DecompileResults;
import ghidra.app.script.GhidraScript;

import ghidra.program.model.address.Address;
import ghidra.program.model.address.AddressSet;
import ghidra.program.model.address.AddressSetView;
import ghidra.program.model.lang.Register;
import ghidra.program.model.listing.Function;
import ghidra.program.model.listing.FunctionIterator;
import ghidra.program.model.listing.FunctionManager;
import ghidra.program.model.listing.Instruction;
import ghidra.program.model.listing.InstructionIterator;
import ghidra.program.model.listing.Listing;
import ghidra.program.model.listing.ProgramContext;
import ghidra.program.model.mem.Memory;
import ghidra.program.model.scalar.Scalar;
import ghidra.program.model.symbol.SourceType;

import java.io.BufferedOutputStream;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.FileWriter;
import java.io.IOException;

import java.math.BigInteger;
import java.security.MessageDigest;
import java.time.LocalDateTime;
import java.time.format.DateTimeFormatter;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Set;

import java.util.zip.ZipEntry;
import java.util.zip.ZipOutputStream;

public class TeslaGatewayNMObjectRawTimerCallerAndCallbackClosureTraceV407
        extends GhidraScript {

    private static final String SCRIPT_NAME =
        "TeslaGatewayNMObjectRawTimerCallerAndCallbackClosureTraceV407";

    private static final String EXPECTED_LANGUAGE =
        "PowerPC:BE:64:VLE-32addr";

    private static final String STOCK_SHA256 =
        "889ab36ae6d17bb897587df85db6201f32cb33f01ba101962979f765ef0ee3fe";

    private static final long IMAGE_START = 0x00000000L;
    private static final long IMAGE_END   = 0x001FFFFFL;
    private static final long APP_START   = 0x00020000L;
    private static final long APP_END     = 0x00149299L;

    private static final long TIMER_INITIALIZER = 0x000F8B24L;
    private static final long TIMER_DISPATCH_A  = 0x000F8788L;
    private static final long TIMER_DISPATCH_B  = 0x000F89F2L;

    private static final long NM_STATE_OWNER = 0x00097E32L;
    private static final long NM_OBJECT = 0x4004ACA8L;
    private static final long NM_OBJECT_FAMILY_START = 0x4004AC60L;
    private static final long NM_OBJECT_FAMILY_END   = 0x4004ADDFL;

    private static final long CALLBACK_TIMEWAIT_BUS_SLEEP = 0x00098916L;
    private static final long CALLBACK_POWERON_SLEEP      = 0x00098A5EL;
    private static final long CALLBACK_NO_NEED_ON         = 0x0006C748L;

    private static final long STRING_TIMEWAIT_BUS_SLEEP = 0x00022BA0L;
    private static final long STRING_NO_NEED_ON         = 0x00022BB4L;
    private static final long STRING_POWERON_SLEEP      = 0x00022BC8L;

    private static final int MAX_TIMER_CALL_BACKSCAN = 0x700;
    private static final int MAX_STATE_INSTRUCTIONS = 220;
    private static final int RECOVERY_SPAN = 0x900;
    private static final int CALLBACK_SPAN = 0x500;
    private static final int HELPER_DEPTH = 5;
    private static final int DECOMPILE_SECONDS = 45;
    private static final int MAX_DECOMPILE_FUNCTIONS = 50;

    private Listing listing;
    private Memory memory;
    private FunctionManager functions;
    private byte[] image;

    private File workDirectory;
    private File bundleFile;

    private final List<RawTimerRow> rawTimerRows =
        new ArrayList<RawTimerRow>();
    private final List<CallbackProfileRow> callbackProfiles =
        new ArrayList<CallbackProfileRow>();
    private final List<HelperEdgeRow> helperEdges =
        new ArrayList<HelperEdgeRow>();
    private final List<NmCallRow> nmCalls =
        new ArrayList<NmCallRow>();
    private final List<DispatchRow> dispatchRows =
        new ArrayList<DispatchRow>();
    private final List<String[]> errorRows =
        new ArrayList<String[]>();

    private final Map<Long, Function> recoveredFunctions =
        new LinkedHashMap<Long, Function>();
    private final Set<Long> selectedFunctions =
        new LinkedHashSet<Long>();

    private static class Value {
        boolean known;
        long constant;
        String origin;

        static Value unknown() {
            Value v = new Value();
            v.known = false;
            v.origin = "UNKNOWN";
            return v;
        }

        static Value constant(long value, String origin) {
            Value v = new Value();
            v.known = true;
            v.constant = value & 0xffffffffL;
            v.origin = origin == null ? "" : origin;
            return v;
        }

        Value add(long value, String site) {
            if (!known) return unknown();
            return constant(constant + value, origin + " -> add@" + site);
        }

        Value or(long value, String site) {
            if (!known) return unknown();
            return constant(constant | value, origin + " -> or@" + site);
        }

        String describe() {
            if (!known) return "";
            return String.format(Locale.ROOT, "0x%08X", constant & 0xffffffffL);
        }
    }

    private static class State {
        final Map<String, Value> registers =
            new HashMap<String, Value>();
        Value ctr = Value.unknown();

        State() {
            for (int i = 0; i < 32; i++) {
                registers.put("r" + i, Value.unknown());
            }
        }

        Value get(String name) {
            if (name == null) return Value.unknown();
            Value v = registers.get(name.toLowerCase(Locale.ROOT));
            return v == null ? Value.unknown() : v;
        }

        void set(String name, Value value) {
            if (name == null) return;
            registers.put(name.toLowerCase(Locale.ROOT),
                value == null ? Value.unknown() : value);
        }

        void clobberVolatile() {
            for (int i = 3; i <= 12; i++) {
                registers.put("r" + i, Value.unknown());
            }
            ctr = Value.unknown();
        }
    }

    private static class RawCall {
        long site;
        long target;
        RawCall(long site, long target) {
            this.site = site;
            this.target = target;
        }
    }

    private static class RawTimerRow {
        long rawSite;
        long recoveryStart;
        boolean decodedCall;
        String instruction;
        String callerName;
        long callerEntry;
        Value r3 = Value.unknown();
        Value r4 = Value.unknown();
        Value r5 = Value.unknown();
        Value r6 = Value.unknown();
        Value r7 = Value.unknown();
        String namePreview = "";
        String callbackRole = "";
        String objectClass = "";
        String classification = "";
        String previous = "";
        String next = "";
    }

    private static class CallbackProfileRow {
        long callback;
        String role;
        long ownerEntry;
        String ownerName;
        int instructionCount;
        int directCalls;
        int conditionalBranches;
        int helperFunctionsRecovered;
        boolean reachesNm;
    }

    private static class HelperEdgeRow {
        long callbackRoot;
        String callbackRole;
        int depth;
        long sourceEntry;
        String sourceName;
        long site;
        long targetEntry;
        String targetName;
        String instruction;
    }

    private static class NmCallRow {
        long callbackRoot;
        String callbackRole;
        int depth;
        long callerEntry;
        String callerName;
        long callsite;
        Value r3 = Value.unknown();
        Value r4 = Value.unknown();
        Value r5 = Value.unknown();
        Value r6 = Value.unknown();
        String objectClass;
        String targetState;
        String transitionClass;
        String previousPredicate;
        String path;
        String instruction;
    }

    private static class DispatchRow {
        long site;
        String instruction;
        String previous;
        String next;
        boolean computedCall;
    }

    @Override
    protected void run() throws Exception {
        if (currentProgram == null) {
            popup("No Ghidra program is open.");
            return;
        }

        String language = currentProgram.getLanguageID().toString();
        if (!EXPECTED_LANGUAGE.equals(language)) {
            popup("V407 stopped: unexpected Ghidra language.\nExpected: " +
                EXPECTED_LANGUAGE + "\nObserved: " + language);
            return;
        }

        listing = currentProgram.getListing();
        memory = currentProgram.getMemory();
        functions = currentProgram.getFunctionManager();
        image = readBytes(IMAGE_START, (int)(IMAGE_END - IMAGE_START + 1L));

        String sha = sha256(image);
        if (!STOCK_SHA256.equalsIgnoreCase(sha)) {
            popup("V407 stopped: stock image guard failed.\nExpected: " +
                STOCK_SHA256 + "\nObserved: " + sha);
            return;
        }

        File parent = askDirectory("Choose V407 output directory", "Select");
        if (parent == null) return;

        String stamp = LocalDateTime.now().format(
            DateTimeFormatter.ofPattern("yyyyMMdd_HHmmss"));
        workDirectory = new File(parent, SCRIPT_NAME + "_" + stamp);
        if (!workDirectory.mkdirs()) {
            throw new IOException("Unable to create output directory: " +
                workDirectory.getAbsolutePath());
        }
        bundleFile = new File(parent,
            SCRIPT_NAME + "_" + stamp + "_bundle.zip");

        println("Running " + SCRIPT_NAME);
        println("Stock SHA-256: " + sha);

        int transaction = currentProgram.startTransaction(
            SCRIPT_NAME + " temporary recovery");
        try {
            validateStrings();
            recoverRawTimerCallers();
            recoverKnownCallbacksAndClosure();
            analyseTimerDispatch();
            sortRows();
            writeRawTimerRows();
            writeExactObjectRegistrations();
            writeCallbackProfiles();
            writeHelperEdges();
            writeNmCalls();
            writeDispatchRows();
            writeSelectedDecompilation();
            writeErrors();
            writeSummary(sha);
        }
        finally {
            currentProgram.endTransaction(transaction, false);
        }

        zipDirectory(workDirectory, bundleFile);

        println("");
        println("V407 complete.");
        println("  raw timer e_bl candidates: " + rawTimerRows.size());
        println("  callback profiles: " + callbackProfiles.size());
        println("  helper edges: " + helperEdges.size());
        println("  callback-family NM calls: " + nmCalls.size());
        println("  errors: " + errorRows.size());
        println("  bundle: " + bundleFile.getAbsolutePath());
    }

    private void validateStrings() throws Exception {
        requireAsciiPrefix(STRING_TIMEWAIT_BUS_SLEEP, "nmTimeWaitBusSleep");
        requireAsciiPrefix(STRING_NO_NEED_ON, "noNeedToBeOnTimer");
        requireAsciiPrefix(STRING_POWERON_SLEEP, "nmPowerOnSleep");
    }

    private void requireAsciiPrefix(long address, String expected) throws Exception {
        String observed = readAscii(address, expected.length() + 24);
        if (!observed.startsWith(expected)) {
            throw new IllegalStateException(String.format(Locale.ROOT,
                "String mismatch at 0x%08X expected '%s' found '%s'",
                address, expected, observed));
        }
    }

    private void recoverRawTimerCallers() {
        List<RawCall> rawCalls = decodeRawCallsTo(TIMER_INITIALIZER);
        for (RawCall raw : rawCalls) {
            RawTimerRow row = new RawTimerRow();
            row.rawSite = raw.site;
            try {
                long prologue = findNearestPrologue(raw.site, MAX_TIMER_CALL_BACKSCAN);
                long start = prologue >= APP_START ? prologue :
                    Math.max(APP_START, raw.site - 0x200L);
                long end = Math.min(APP_END, raw.site + 0x30L);
                row.recoveryStart = start;

                disassembleRangeBestEffort(start, end);
                Instruction call = listing.getInstructionAt(addressOf(raw.site));
                row.decodedCall = isVerifiedDirectCall(call, TIMER_INITIALIZER);
                row.instruction = call == null ? rawBytesText(raw.site, 4) : call.toString();

                Function caller = call == null ? null :
                    functions.getFunctionContaining(call.getAddress());
                if (caller == null && call != null) {
                    caller = recoverFunction(start, Math.min(APP_END, raw.site + 0x80L),
                        "timer_caller");
                }
                if (caller != null) {
                    row.callerEntry = caller.getEntryPoint().getOffset();
                    row.callerName = caller.getName();
                    selectedFunctions.add(Long.valueOf(row.callerEntry));
                }

                if (call != null) {
                    State state = stateBeforeCall(call, start);
                    row.r3 = state.get("r3");
                    row.r4 = state.get("r4");
                    row.r5 = state.get("r5");
                    row.r6 = state.get("r6");
                    row.r7 = state.get("r7");
                    row.namePreview = previewAscii(row.r3);
                    row.callbackRole = callbackRole(row.r7);
                    row.objectClass = classifyObject(row.r6);
                    row.previous = previousText(call, 24);
                    row.next = nextText(call, 10);
                }

                if ("exact_4004aca8".equals(row.objectClass) &&
                    ("timewait_bus_sleep".equals(row.callbackRole) ||
                     "poweron_sleep".equals(row.callbackRole))) {
                    row.classification = "EXACT_OBJECT_SLEEP_TIMER_REGISTRATION";
                }
                else if ("exact_4004aca8".equals(row.objectClass)) {
                    row.classification = "EXACT_OBJECT_TIMER_REGISTRATION";
                }
                else if (row.decodedCall) {
                    row.classification = "VERIFIED_TIMER_CALL_ARGUMENTS_PARTIAL";
                }
                else {
                    row.classification = "RAW_EBL_TO_TIMER_INITIALIZER";
                }
            }
            catch (Throwable t) {
                row.classification = "RAW_TIMER_CALL_RECOVERY_ERROR";
                addError("timer_caller_recovery", raw.site, t);
            }
            rawTimerRows.add(row);
        }
    }

    private void recoverKnownCallbacksAndClosure() {
        long[] callbacks = new long[] {
            CALLBACK_TIMEWAIT_BUS_SLEEP,
            CALLBACK_POWERON_SLEEP,
            CALLBACK_NO_NEED_ON
        };

        for (long callback : callbacks) {
            CallbackProfileRow profile = new CallbackProfileRow();
            profile.callback = callback;
            profile.role = callbackRole(callback);
            try {
                Function root = recoverFunction(callback,
                    Math.min(APP_END, callback + CALLBACK_SPAN),
                    "callback_" + profile.role);
                if (root == null) {
                    callbackProfiles.add(profile);
                    continue;
                }

                profile.ownerEntry = root.getEntryPoint().getOffset();
                profile.ownerName = root.getName();
                profile.instructionCount = countInstructions(root.getBody());
                selectedFunctions.add(Long.valueOf(profile.ownerEntry));

                Map<Long, String> pathByEntry = new LinkedHashMap<Long, String>();
                Deque<ClosureNode> queue = new ArrayDeque<ClosureNode>();
                Set<Long> visited = new LinkedHashSet<Long>();
                String rootPath = hex(callback) + ":" + profile.role;
                queue.addLast(new ClosureNode(root, 0, rootPath));
                pathByEntry.put(Long.valueOf(profile.ownerEntry), rootPath);

                while (!queue.isEmpty()) {
                    ClosureNode node = queue.removeFirst();
                    Function function = node.function;
                    long sourceEntry = function.getEntryPoint().getOffset();
                    if (!visited.add(Long.valueOf(sourceEntry))) continue;
                    selectedFunctions.add(Long.valueOf(sourceEntry));

                    InstructionIterator iterator =
                        listing.getInstructions(function.getBody(), true);
                    while (iterator.hasNext()) {
                        Instruction instruction = iterator.next();
                        if (instruction.getFlowType() != null &&
                            instruction.getFlowType().isConditional()) {
                            if (sourceEntry == profile.ownerEntry) {
                                profile.conditionalBranches++;
                            }
                        }

                        Long target = directCallTarget(instruction);
                        if (target == null) continue;
                        if (sourceEntry == profile.ownerEntry) profile.directCalls++;

                        long targetEntry = target.longValue();
                        Function targetFunction = functionAtOrContaining(targetEntry);
                        if (targetFunction == null &&
                            isApplicationCode(targetEntry) &&
                            targetEntry != TIMER_INITIALIZER) {
                            targetFunction = recoverFunction(targetEntry,
                                Math.min(APP_END, targetEntry + RECOVERY_SPAN),
                                "helper");
                            if (targetFunction != null) {
                                profile.helperFunctionsRecovered++;
                            }
                        }

                        HelperEdgeRow edge = new HelperEdgeRow();
                        edge.callbackRoot = callback;
                        edge.callbackRole = profile.role;
                        edge.depth = node.depth;
                        edge.sourceEntry = sourceEntry;
                        edge.sourceName = function.getName();
                        edge.site = instruction.getAddress().getOffset();
                        edge.targetEntry = targetEntry;
                        edge.targetName = targetFunction == null ? "" : targetFunction.getName();
                        edge.instruction = instruction.toString();
                        helperEdges.add(edge);

                        if (targetEntry == NM_STATE_OWNER) {
                            profile.reachesNm = true;
                            NmCallRow nm = buildNmCallRow(callback, profile.role,
                                node.depth, function, instruction, node.path);
                            nmCalls.add(nm);
                            continue;
                        }

                        if (node.depth >= HELPER_DEPTH || targetFunction == null) {
                            continue;
                        }

                        long normalized = targetFunction.getEntryPoint().getOffset();
                        if (!isApplicationCode(normalized)) continue;

                        String nextPath = node.path + " -> " +
                            hex(normalized) + ":" + targetFunction.getName();
                        if (!pathByEntry.containsKey(Long.valueOf(normalized))) {
                            pathByEntry.put(Long.valueOf(normalized), nextPath);
                        }
                        queue.addLast(new ClosureNode(targetFunction,
                            node.depth + 1, nextPath));
                    }
                }
            }
            catch (Throwable t) {
                addError("callback_closure", callback, t);
            }
            callbackProfiles.add(profile);
        }
    }

    private static class ClosureNode {
        Function function;
        int depth;
        String path;
        ClosureNode(Function function, int depth, String path) {
            this.function = function;
            this.depth = depth;
            this.path = path;
        }
    }

    private NmCallRow buildNmCallRow(long callback, String role, int depth,
            Function caller, Instruction call, String path) {
        NmCallRow row = new NmCallRow();
        row.callbackRoot = callback;
        row.callbackRole = role;
        row.depth = depth;
        row.callerEntry = caller.getEntryPoint().getOffset();
        row.callerName = caller.getName();
        row.callsite = call.getAddress().getOffset();
        long lower = caller.getBody().getMinAddress().getOffset();
        State state = stateBeforeCall(call, lower);
        row.r3 = state.get("r3");
        row.r4 = state.get("r4");
        row.r5 = state.get("r5");
        row.r6 = state.get("r6");
        row.objectClass = classifyObject(row.r3);
        row.targetState = stateName(row.r4);
        row.transitionClass = transitionClass(row.r4);
        row.previousPredicate = nearestPredicate(call, 18);
        row.path = path + " -> " + hex(NM_STATE_OWNER) + ":FUN_00097e32";
        row.instruction = call.toString();
        return row;
    }

    private void analyseTimerDispatch() {
        long[] sites = new long[] { TIMER_DISPATCH_A, TIMER_DISPATCH_B };
        for (long site : sites) {
            DispatchRow row = new DispatchRow();
            row.site = site;
            try {
                disassembleRangeBestEffort(Math.max(APP_START, site - 0x30L),
                    Math.min(APP_END, site + 0x18L));
                Instruction instruction = instructionAtOrContaining(site);
                if (instruction != null) {
                    row.instruction = instruction.toString();
                    row.computedCall = instruction.getFlowType() != null &&
                        instruction.getFlowType().isComputed() &&
                        instruction.getFlowType().isCall();
                    row.previous = previousText(instruction, 24);
                    row.next = nextText(instruction, 10);
                }
            }
            catch (Throwable t) {
                addError("timer_dispatch", site, t);
            }
            dispatchRows.add(row);
        }
    }

    private List<RawCall> decodeRawCallsTo(long requiredTarget) {
        List<RawCall> result = new ArrayList<RawCall>();
        int start = (int)(APP_START - IMAGE_START);
        int end = (int)(APP_END - IMAGE_START);
        for (int offset = start; offset + 3 <= end; offset += 2) {
            int word = ((image[offset] & 0xff) << 24) |
                       ((image[offset + 1] & 0xff) << 16) |
                       ((image[offset + 2] & 0xff) << 8) |
                       (image[offset + 3] & 0xff);
            if (((word >>> 24) & 0xff) != 0x78 || (word & 1) == 0) continue;
            int displacement = word & 0x00fffffe;
            if ((displacement & 0x00800000) != 0) {
                displacement |= 0xff000000;
            }
            long site = IMAGE_START + offset;
            long target = (site + displacement) & 0xffffffffL;
            if (target == requiredTarget) {
                result.add(new RawCall(site, target));
            }
        }
        return result;
    }

    private long findNearestPrologue(long from, int maximumBack) {
        long minimum = Math.max(APP_START, from - maximumBack);
        for (long candidate = from & ~1L; candidate >= minimum; candidate -= 2L) {
            int offset = (int)(candidate - IMAGE_START);
            if (offset < 0 || offset + 1 >= image.length) continue;
            if ((image[offset] & 0xff) == 0x18 &&
                (image[offset + 1] & 0xff) == 0x21) {
                return candidate;
            }
        }
        return -1L;
    }

    private void disassembleRangeBestEffort(long start, long end) {
        Address startAddress = addressOf(start);
        Address endAddress = addressOf(end);
        try {
            setVleOnlyIfNeeded(startAddress, endAddress);
        }
        catch (Throwable t) {
            addError("vle_context_best_effort", start, t);
        }
        try {
            PowerPCDisassembleCommand command =
                new PowerPCDisassembleCommand(startAddress,
                    new AddressSet(startAddress, endAddress), true);
            command.applyTo(currentProgram, monitor);
        }
        catch (Throwable t) {
            addError("disassemble_best_effort", start, t);
        }
    }

    private void setVleOnlyIfNeeded(Address start, Address end) throws Exception {
        Register vle = currentProgram.getRegister("VLE");
        if (vle == null) vle = currentProgram.getRegister("vle");
        if (vle == null) throw new IllegalStateException("VLE context register not found");

        // Avoid the V406 ContextChangeException by setting VLE only over
        // contiguous gaps that contain no already-decoded instruction.
        ProgramContext context = currentProgram.getProgramContext();
        long cursor = start.getOffset();
        long finalOffset = end.getOffset();
        while (cursor <= finalOffset) {
            Address here = addressOf(cursor);
            Instruction containing = listing.getInstructionContaining(here);
            if (containing != null) {
                cursor = containing.getMaxAddress().getOffset() + 1L;
                continue;
            }
            long gapStart = cursor;
            long gapEnd = gapStart;
            while (gapEnd <= finalOffset) {
                Instruction existing = listing.getInstructionContaining(addressOf(gapEnd));
                if (existing != null) break;
                gapEnd++;
            }
            long inclusiveEnd = Math.min(finalOffset, gapEnd - 1L);
            if (inclusiveEnd >= gapStart) {
                context.setValue(vle, addressOf(gapStart), addressOf(inclusiveEnd),
                    BigInteger.ONE);
            }
            cursor = gapEnd;
        }
    }

    private Function recoverFunction(long start, long maximumEnd, String role) {
        try {
            Address entry = addressOf(start);
            Function exact = functions.getFunctionAt(entry);
            if (exact != null) {
                recoveredFunctions.put(Long.valueOf(exact.getEntryPoint().getOffset()), exact);
                return exact;
            }
            Function containing = functions.getFunctionContaining(entry);
            if (containing != null && containing.getBody().contains(entry)) {
                recoveredFunctions.put(Long.valueOf(containing.getEntryPoint().getOffset()), containing);
                return containing;
            }

            long end = Math.min(APP_END, maximumEnd);
            disassembleRangeBestEffort(start, end);
            AddressSet body = reachableBody(start, end);
            if (body.isEmpty()) return null;

            // Temporary transaction only. Remove overlapping temporary/incorrect
            // bodies so the exact entry can be represented for helper closure.
            List<Address> remove = new ArrayList<Address>();
            FunctionIterator it = functions.getFunctions(true);
            while (it.hasNext()) {
                Function f = it.next();
                if (body.intersects(f.getBody())) {
                    remove.add(f.getEntryPoint());
                }
            }
            for (Address address : remove) {
                functions.removeFunction(address);
            }

            Function created = functions.createFunction(
                "V407_" + role + "_" + String.format(Locale.ROOT, "%08X", start),
                entry, body, SourceType.USER_DEFINED);
            if (created != null) {
                recoveredFunctions.put(Long.valueOf(created.getEntryPoint().getOffset()), created);
            }
            return created;
        }
        catch (Throwable t) {
            addError("recover_function_" + role, start, t);
            return null;
        }
    }

    private AddressSet reachableBody(long start, long end) {
        AddressSet body = new AddressSet();
        Deque<Long> queue = new ArrayDeque<Long>();
        Set<Long> visited = new HashSet<Long>();
        queue.addLast(Long.valueOf(start));
        while (!queue.isEmpty() && visited.size() < 16000) {
            long location = queue.removeFirst().longValue();
            if (location < start || location > end ||
                !visited.add(Long.valueOf(location))) continue;
            Instruction instruction = listing.getInstructionAt(addressOf(location));
            if (instruction == null) continue;
            body.addRange(instruction.getAddress(), instruction.getMaxAddress());
            if (instruction.getFlowType() != null &&
                instruction.getFlowType().isTerminal()) continue;
            Address fall = instruction.getFallThrough();
            if (fall != null) {
                long v = fall.getOffset() & 0xffffffffL;
                if (v >= start && v <= end) queue.addLast(Long.valueOf(v));
            }
            if (instruction.getFlowType() != null &&
                instruction.getFlowType().isCall()) continue;
            Address[] flows = instruction.getFlows();
            if (flows != null) {
                for (Address flow : flows) {
                    if (flow == null) continue;
                    long v = flow.getOffset() & 0xffffffffL;
                    if (v >= start && v <= end) queue.addLast(Long.valueOf(v));
                }
            }
        }
        return body;
    }

    private State stateBeforeCall(Instruction call, long lowerBound) {
        State state = new State();
        List<Instruction> previous = new ArrayList<Instruction>();
        Instruction cursor = call.getPrevious();
        while (cursor != null &&
               cursor.getAddress().getOffset() >= lowerBound &&
               previous.size() < MAX_STATE_INSTRUCTIONS) {
            previous.add(0, cursor);
            cursor = cursor.getPrevious();
        }

        for (Instruction instruction : previous) {
            String mnemonic = normalizeMnemonic(instruction.getMnemonicString());
            if (instruction.getFlowType() != null &&
                instruction.getFlowType().isCall()) {
                state.clobberVolatile();
                continue;
            }
            if (isLoadMnemonic(mnemonic)) {
                String destination = firstRegister(instruction, 0);
                Long effective = resolveEffectiveAddress(instruction, 1, state);
                if (destination != null && effective != null &&
                    widthForMnemonic(mnemonic) == 4 &&
                    effective.longValue() >= IMAGE_START &&
                    effective.longValue() <= IMAGE_END - 3L) {
                    state.set(destination, Value.constant(readU32(effective.longValue()),
                        "LOAD32@" + hex(effective.longValue())));
                }
            }
            updateState(instruction, mnemonic, state);
        }
        return state;
    }

    private void updateState(Instruction instruction, String mnemonic, State state) {
        String site = instruction.getAddress().toString();

        if (mnemonic.contains("lis")) {
            String destination = firstRegister(instruction, 0);
            Long immediate = firstScalarAfterOperand(instruction, 0, false);
            if (destination != null && immediate != null) {
                state.set(destination, Value.constant(
                    (immediate.longValue() & 0xffffL) << 16, site));
            }
            return;
        }

        if (mnemonic.contains("addi") || mnemonic.contains("add16i")) {
            String destination = firstRegister(instruction, 0);
            String source = firstRegisterAfterOperand(instruction, 0);
            Long immediate = firstScalarAfterOperand(instruction, 0, true);
            if (destination != null && source != null && immediate != null) {
                state.set(destination, state.get(source).add(immediate.longValue(), site));
            }
            return;
        }

        if (mnemonic.contains("li") && !mnemonic.contains("lis")) {
            String destination = firstRegister(instruction, 0);
            Long immediate = firstScalarAfterOperand(instruction, 0, true);
            if (destination != null && immediate != null) {
                state.set(destination, Value.constant(immediate.longValue(), site));
            }
            return;
        }

        if (mnemonic.contains("ori") || mnemonic.contains("or2i")) {
            List<String> regs = allRegisters(instruction);
            Long immediate = firstScalar(instruction, false);
            if (!regs.isEmpty() && immediate != null) {
                String destination = regs.get(0);
                String source = regs.size() > 1 ? regs.get(1) : destination;
                long amount = immediate.longValue() & 0xffffL;
                if (mnemonic.contains("oris")) amount <<= 16;
                state.set(destination, state.get(source).or(amount, site));
            }
            return;
        }

        if (isMoveMnemonic(mnemonic)) {
            List<String> regs = allRegisters(instruction);
            if (regs.size() >= 2) state.set(regs.get(0), state.get(regs.get(1)));
            return;
        }

        if (mnemonic.contains("mtctr")) {
            String source = firstRegister(instruction, 0);
            if (source == null) source = firstRegisterAfterOperand(instruction, -1);
            state.ctr = state.get(source);
            return;
        }

        Object[] results = instruction.getResultObjects();
        if (results == null) return;
        for (Object object : results) {
            if (object instanceof Register) {
                state.set(((Register)object).getName(), Value.unknown());
            }
        }
    }

    private boolean isVerifiedDirectCall(Instruction instruction, long target) {
        if (instruction == null || instruction.getFlowType() == null ||
            !instruction.getFlowType().isCall()) return false;
        Address[] flows = instruction.getFlows();
        if (flows == null) return false;
        for (Address flow : flows) {
            if (flow != null &&
                (flow.getOffset() & 0xffffffffL) == target) return true;
        }
        return false;
    }

    private Long directCallTarget(Instruction instruction) {
        if (instruction == null || instruction.getFlowType() == null ||
            !instruction.getFlowType().isCall() ||
            instruction.getFlowType().isComputed()) return null;
        Address[] flows = instruction.getFlows();
        if (flows == null || flows.length == 0 || flows[0] == null) return null;
        return Long.valueOf(flows[0].getOffset() & 0xffffffffL);
    }

    private Long resolveEffectiveAddress(Instruction instruction,
            int operandIndex, State state) {
        if (operandIndex < 0 || operandIndex >= instruction.getNumOperands()) return null;
        long total = 0L;
        boolean found = false;
        Object[] objects = instruction.getOpObjects(operandIndex);
        if (objects == null) return null;
        for (Object object : objects) {
            if (object instanceof Register) {
                found = true;
                Value value = state.get(((Register)object).getName());
                if (!value.known) return null;
                total += value.constant;
            }
            else if (object instanceof Scalar) {
                found = true;
                total += ((Scalar)object).getSignedValue();
            }
        }
        return found ? Long.valueOf(total & 0xffffffffL) : null;
    }

    private String firstRegister(Instruction instruction, int operandIndex) {
        if (operandIndex < 0 || operandIndex >= instruction.getNumOperands()) return null;
        Object[] objects = instruction.getOpObjects(operandIndex);
        if (objects == null) return null;
        for (Object object : objects) {
            if (object instanceof Register) return ((Register)object).getName();
        }
        return null;
    }

    private String firstRegisterAfterOperand(Instruction instruction, int operandIndex) {
        for (int i = Math.max(0, operandIndex + 1); i < instruction.getNumOperands(); i++) {
            String value = firstRegister(instruction, i);
            if (value != null) return value;
        }
        return null;
    }

    private List<String> allRegisters(Instruction instruction) {
        List<String> result = new ArrayList<String>();
        for (int i = 0; i < instruction.getNumOperands(); i++) {
            Object[] objects = instruction.getOpObjects(i);
            if (objects == null) continue;
            for (Object object : objects) {
                if (object instanceof Register) {
                    result.add(((Register)object).getName());
                }
            }
        }
        return result;
    }

    private Long firstScalar(Instruction instruction, boolean signed) {
        return firstScalarAfterOperand(instruction, -1, signed);
    }

    private Long firstScalarAfterOperand(Instruction instruction,
            int operandIndex, boolean signed) {
        for (int i = Math.max(0, operandIndex + 1); i < instruction.getNumOperands(); i++) {
            Object[] objects = instruction.getOpObjects(i);
            if (objects == null) continue;
            for (Object object : objects) {
                if (object instanceof Scalar) {
                    Scalar scalar = (Scalar)object;
                    return Long.valueOf(signed ? scalar.getSignedValue() :
                        scalar.getUnsignedValue());
                }
            }
        }
        return null;
    }

    private boolean isLoadMnemonic(String mnemonic) {
        return mnemonic.contains("lbz") || mnemonic.contains("lhz") ||
               mnemonic.contains("lwz") || mnemonic.contains("ld");
    }

    private int widthForMnemonic(String mnemonic) {
        if (mnemonic.contains("lbz")) return 1;
        if (mnemonic.contains("lhz")) return 2;
        if (mnemonic.contains("lwz")) return 4;
        if (mnemonic.contains("ld")) return 8;
        return 0;
    }

    private boolean isMoveMnemonic(String mnemonic) {
        return mnemonic.equals("mr") || mnemonic.endsWith("_mr");
    }

    private String normalizeMnemonic(String mnemonic) {
        if (mnemonic == null) return "";
        String value = mnemonic.toLowerCase(Locale.ROOT);
        if (value.startsWith("se_")) return value.substring(3);
        if (value.startsWith("e_")) return value.substring(2);
        return value;
    }

    private String callbackRole(Value value) {
        return value != null && value.known ? callbackRole(value.constant) : "unresolved";
    }

    private String callbackRole(long value) {
        long callback = value & 0xfffffffeL;
        if (callback == CALLBACK_TIMEWAIT_BUS_SLEEP) return "timewait_bus_sleep";
        if (callback == CALLBACK_POWERON_SLEEP) return "poweron_sleep";
        if (callback == CALLBACK_NO_NEED_ON) return "no_need_to_be_on";
        return "other";
    }

    private String classifyObject(Value value) {
        if (value == null || !value.known) return "unresolved";
        if (value.constant == NM_OBJECT) return "exact_4004aca8";
        if (value.constant >= NM_OBJECT_FAMILY_START &&
            value.constant <= NM_OBJECT_FAMILY_END) return "nm_object_family";
        return "other";
    }

    private String stateName(Value value) {
        if (value == null || !value.known) return "";
        long state = value.constant & 0xffffffffL;
        if (state == 1) return "PowerOn";
        if (state == 2) return "Sleep";
        if (state == 4) return "WakeUp";
        if (state == 8) return "Normal";
        if (state == 0x10) return "PrepSleep";
        if (state == 0x20) return "TimeWait";
        if (state == 0x40) return "LimpPrep";
        if (state == 0x80) return "LimpHome";
        return String.format(Locale.ROOT, "state_0x%X", state);
    }

    private String transitionClass(Value value) {
        if (value == null || !value.known) return "TARGET_STATE_UNRESOLVED";
        long state = value.constant & 0xffffffffL;
        if (state == 2 || state == 0x10 || state == 0x20) return "SLEEP_DIRECTION";
        if (state == 4) return "WAKE_DIRECTION";
        return "OTHER_NM_TRANSITION";
    }

    private String previewAscii(Value value) {
        if (value == null || !value.known) return "";
        if (value.constant < IMAGE_START || value.constant > IMAGE_END) return "";
        return readAscii(value.constant, 64);
    }

    private String nearestPredicate(Instruction instruction, int count) {
        Instruction cursor = instruction;
        for (int i = 0; i < count; i++) {
            cursor = cursor.getPrevious();
            if (cursor == null) break;
            String m = normalizeMnemonic(cursor.getMnemonicString());
            if (cursor.getFlowType() != null && cursor.getFlowType().isConditional()) {
                return cursor.getAddress() + ": " + cursor.toString();
            }
            if (m.contains("cmp") || m.contains("tst") || m.contains("and") ||
                m.contains("rlwinm")) {
                return cursor.getAddress() + ": " + cursor.toString();
            }
        }
        return "";
    }

    private Function functionAtOrContaining(long address) {
        Address a = addressOf(address);
        Function f = functions.getFunctionAt(a);
        if (f == null) f = functions.getFunctionContaining(a);
        return f;
    }

    private boolean isApplicationCode(long address) {
        long value = address & 0xfffffffeL;
        return value >= APP_START && value <= APP_END;
    }

    private Instruction instructionAtOrContaining(long address) {
        Address a = addressOf(address);
        Instruction i = listing.getInstructionAt(a);
        if (i == null) i = listing.getInstructionContaining(a);
        return i;
    }

    private int countInstructions(AddressSetView body) {
        int count = 0;
        InstructionIterator iterator = listing.getInstructions(body, true);
        while (iterator.hasNext()) {
            iterator.next();
            count++;
        }
        return count;
    }

    private String readAscii(long address, int maximum) {
        StringBuilder b = new StringBuilder();
        for (int i = 0; i < maximum; i++) {
            try {
                int value = memory.getByte(addressOf(address + i)) & 0xff;
                if (value == 0) break;
                if (value < 0x20 || value > 0x7e) break;
                b.append((char)value);
            }
            catch (Throwable t) {
                break;
            }
        }
        return b.toString();
    }

    private String previousText(Instruction instruction, int count) {
        List<String> values = new ArrayList<String>();
        Instruction cursor = instruction;
        for (int i = 0; i < count; i++) {
            cursor = cursor.getPrevious();
            if (cursor == null) break;
            values.add(0, cursor.getAddress() + ": " + cursor.toString());
        }
        return join(values, " ; ");
    }

    private String nextText(Instruction instruction, int count) {
        List<String> values = new ArrayList<String>();
        Instruction cursor = instruction;
        for (int i = 0; i < count; i++) {
            cursor = cursor.getNext();
            if (cursor == null) break;
            values.add(cursor.getAddress() + ": " + cursor.toString());
        }
        return join(values, " ; ");
    }

    private String rawBytesText(long address, int length) {
        StringBuilder b = new StringBuilder();
        for (int i = 0; i < length; i++) {
            int offset = (int)(address - IMAGE_START + i);
            if (offset < 0 || offset >= image.length) break;
            if (b.length() != 0) b.append(' ');
            b.append(String.format(Locale.ROOT, "%02X", image[offset] & 0xff));
        }
        return b.toString();
    }

    private long readU32(long address) {
        int offset = (int)(address - IMAGE_START);
        if (offset < 0 || offset + 3 >= image.length) return 0L;
        return ((long)(image[offset] & 0xff) << 24) |
               ((long)(image[offset + 1] & 0xff) << 16) |
               ((long)(image[offset + 2] & 0xff) << 8) |
               ((long)(image[offset + 3] & 0xff));
    }

    private byte[] readBytes(long address, int length) throws Exception {
        byte[] result = new byte[length];
        int read = memory.getBytes(addressOf(address), result);
        if (read != length) {
            throw new IllegalStateException("Read " + read + " of " + length +
                " bytes at " + hex(address));
        }
        return result;
    }

    private Address addressOf(long value) {
        return currentProgram.getAddressFactory().getDefaultAddressSpace()
            .getAddress(value & 0xffffffffL);
    }

    private void sortRows() {
        Collections.sort(rawTimerRows, new Comparator<RawTimerRow>() {
            public int compare(RawTimerRow a, RawTimerRow b) {
                return Long.compareUnsigned(a.rawSite, b.rawSite);
            }
        });
        Collections.sort(callbackProfiles, new Comparator<CallbackProfileRow>() {
            public int compare(CallbackProfileRow a, CallbackProfileRow b) {
                return Long.compareUnsigned(a.callback, b.callback);
            }
        });
        Collections.sort(helperEdges, new Comparator<HelperEdgeRow>() {
            public int compare(HelperEdgeRow a, HelperEdgeRow b) {
                int c = Long.compareUnsigned(a.callbackRoot, b.callbackRoot);
                if (c != 0) return c;
                c = Integer.compare(a.depth, b.depth);
                if (c != 0) return c;
                return Long.compareUnsigned(a.site, b.site);
            }
        });
        Collections.sort(nmCalls, new Comparator<NmCallRow>() {
            public int compare(NmCallRow a, NmCallRow b) {
                int c = Long.compareUnsigned(a.callbackRoot, b.callbackRoot);
                if (c != 0) return c;
                return Long.compareUnsigned(a.callsite, b.callsite);
            }
        });
    }

    private void writeRawTimerRows() throws Exception {
        BufferedWriter w = writer("_raw_timer_calls.csv");
        w.write("raw_site,recovery_start,decoded_call,caller_entry,caller_name,r3_name,r3_preview,r4_period,r5_autoreload,r6_context,r7_callback,object_class,callback_role,classification,instruction,previous_24,next_10\n");
        for (RawTimerRow r : rawTimerRows) {
            w.write(hex(r.rawSite) + "," + hex(r.recoveryStart) + "," + r.decodedCall + "," +
                (r.callerEntry == 0 ? "" : hex(r.callerEntry)) + "," + csv(r.callerName) + "," +
                csv(r.r3.describe()) + "," + csv(r.namePreview) + "," + csv(r.r4.describe()) + "," +
                csv(r.r5.describe()) + "," + csv(r.r6.describe()) + "," + csv(r.r7.describe()) + "," +
                csv(r.objectClass) + "," + csv(r.callbackRole) + "," + csv(r.classification) + "," +
                csv(r.instruction) + "," + csv(r.previous) + "," + csv(r.next) + "\n");
        }
        w.close();
    }

    private void writeExactObjectRegistrations() throws Exception {
        BufferedWriter w = writer("_exact_4004aca8_registrations.csv");
        w.write("raw_site,name_preview,period,autoreload,context,callback,callback_role,classification\n");
        for (RawTimerRow r : rawTimerRows) {
            if (!"exact_4004aca8".equals(r.objectClass)) continue;
            w.write(hex(r.rawSite) + "," + csv(r.namePreview) + "," + csv(r.r4.describe()) + "," +
                csv(r.r5.describe()) + "," + csv(r.r6.describe()) + "," + csv(r.r7.describe()) + "," +
                csv(r.callbackRole) + "," + csv(r.classification) + "\n");
        }
        w.close();
    }

    private void writeCallbackProfiles() throws Exception {
        BufferedWriter w = writer("_callback_profiles.csv");
        w.write("callback,role,owner_entry,owner_name,instruction_count,direct_calls,conditional_branches,helper_functions_recovered,reaches_nm\n");
        for (CallbackProfileRow r : callbackProfiles) {
            w.write(hex(r.callback) + "," + csv(r.role) + "," +
                (r.ownerEntry == 0 ? "" : hex(r.ownerEntry)) + "," + csv(r.ownerName) + "," +
                r.instructionCount + "," + r.directCalls + "," + r.conditionalBranches + "," +
                r.helperFunctionsRecovered + "," + r.reachesNm + "\n");
        }
        w.close();
    }

    private void writeHelperEdges() throws Exception {
        BufferedWriter w = writer("_callback_helper_edges.csv");
        w.write("callback_root,callback_role,depth,source_entry,source_name,callsite,target_entry,target_name,instruction\n");
        for (HelperEdgeRow r : helperEdges) {
            w.write(hex(r.callbackRoot) + "," + csv(r.callbackRole) + "," + r.depth + "," +
                hex(r.sourceEntry) + "," + csv(r.sourceName) + "," + hex(r.site) + "," +
                hex(r.targetEntry) + "," + csv(r.targetName) + "," + csv(r.instruction) + "\n");
        }
        w.close();
    }

    private void writeNmCalls() throws Exception {
        BufferedWriter w = writer("_callback_nm_calls.csv");
        w.write("callback_root,callback_role,depth,caller_entry,caller_name,callsite,r3_object,r4_target_state,r5_mode,r6,object_class,target_state,transition_class,previous_predicate,path,instruction\n");
        for (NmCallRow r : nmCalls) {
            w.write(hex(r.callbackRoot) + "," + csv(r.callbackRole) + "," + r.depth + "," +
                hex(r.callerEntry) + "," + csv(r.callerName) + "," + hex(r.callsite) + "," +
                csv(r.r3.describe()) + "," + csv(r.r4.describe()) + "," + csv(r.r5.describe()) + "," +
                csv(r.r6.describe()) + "," + csv(r.objectClass) + "," + csv(r.targetState) + "," +
                csv(r.transitionClass) + "," + csv(r.previousPredicate) + "," + csv(r.path) + "," +
                csv(r.instruction) + "\n");
        }
        w.close();
    }

    private void writeDispatchRows() throws Exception {
        BufferedWriter w = writer("_timer_dispatch_context.csv");
        w.write("site,instruction,computed_call,previous_24,next_10\n");
        for (DispatchRow r : dispatchRows) {
            w.write(hex(r.site) + "," + csv(r.instruction) + "," + r.computedCall + "," +
                csv(r.previous) + "," + csv(r.next) + "\n");
        }
        w.close();
    }

    private void writeSelectedDecompilation() throws Exception {
        BufferedWriter w = writer("_selected_decompilation.txt");
        DecompInterface decompiler = new DecompInterface();
        decompiler.toggleCCode(true);
        decompiler.toggleSyntaxTree(true);
        decompiler.setSimplificationStyle("decompile");
        int written = 0;
        try {
            if (!decompiler.openProgram(currentProgram)) {
                w.write("<Decompiler could not open program>\n");
                return;
            }
            List<Long> selected = new ArrayList<Long>(selectedFunctions);
            Collections.sort(selected);
            for (Long value : selected) {
                if (written >= MAX_DECOMPILE_FUNCTIONS) break;
                Function function = functionAtOrContaining(value.longValue());
                if (function == null) continue;
                w.write("\n================================================================================\n");
                w.write(hex(function.getEntryPoint().getOffset()) + " " + function.getName() + "\n");
                w.write("================================================================================\n\n");
                try {
                    DecompileResults result = decompiler.decompileFunction(function,
                        DECOMPILE_SECONDS, monitor);
                    if (result.decompileCompleted() && result.getDecompiledFunction() != null) {
                        w.write(result.getDecompiledFunction().getC());
                    }
                    else {
                        w.write("<decompile incomplete: " + result.getErrorMessage() + ">\n");
                    }
                }
                catch (Throwable t) {
                    w.write("<decompile exception: " + t + ">\n");
                    addError("decompile", function.getEntryPoint().getOffset(), t);
                }
                w.write("\n");
                written++;
            }
        }
        finally {
            decompiler.dispose();
            w.close();
        }
    }

    private void writeErrors() throws Exception {
        BufferedWriter w = writer("_errors.csv");
        w.write("phase,address,error_type,message\n");
        for (String[] r : errorRows) {
            w.write(csv(r[0]) + "," + csv(r[1]) + "," + csv(r[2]) + "," + csv(r[3]) + "\n");
        }
        w.close();
    }

    private void writeSummary(String sha) throws Exception {
        int exactRegistrations = 0;
        int exactSleepTimers = 0;
        int sleepNmCalls = 0;
        for (RawTimerRow r : rawTimerRows) {
            if ("exact_4004aca8".equals(r.objectClass)) exactRegistrations++;
            if ("EXACT_OBJECT_SLEEP_TIMER_REGISTRATION".equals(r.classification)) exactSleepTimers++;
        }
        for (NmCallRow r : nmCalls) {
            if ("SLEEP_DIRECTION".equals(r.transitionClass)) sleepNmCalls++;
        }

        String classification;
        if (exactSleepTimers > 0 && sleepNmCalls > 0) {
            classification = "EXACT_OBJECT_SLEEP_TIMER_TO_NM_TRANSITION_CLOSED";
        }
        else if (exactSleepTimers > 0 && !nmCalls.isEmpty()) {
            classification = "EXACT_OBJECT_SLEEP_TIMER_CALLBACK_REACHES_NM_STATE_UNRESOLVED";
        }
        else if (exactSleepTimers > 0) {
            classification = "EXACT_OBJECT_SLEEP_TIMER_RECOVERED_CALLBACK_CLOSURE_UNRESOLVED";
        }
        else if (!rawTimerRows.isEmpty()) {
            classification = "RAW_TIMER_CALLS_RECOVERED_ARGUMENT_BINDING_INCOMPLETE";
        }
        else {
            classification = "NO_RAW_TIMER_CALLS_TO_F8B24";
        }

        BufferedWriter w = writer("_summary.md");
        w.write("# Tesla Gateway NM Object Raw Timer Caller and Callback Closure Trace V407\n\n");
        w.write("- Program: `" + currentProgram.getName() + "`\n");
        w.write("- Language: `" + currentProgram.getLanguageID() + "`\n");
        w.write("- Initialized flash SHA-256: `" + sha + "`\n");
        w.write("- Exact stock image: `true`\n");
        w.write("- Raw VLE e_bl candidates resolving to `0x000F8B24`: `" + rawTimerRows.size() + "`\n");
        w.write("- Exact `0x4004ACA8` registrations: `" + exactRegistrations + "`\n");
        w.write("- Exact sleep/time-wait registrations: `" + exactSleepTimers + "`\n");
        w.write("- Callback profiles: `" + callbackProfiles.size() + "`\n");
        w.write("- Callback/helper direct-call edges: `" + helperEdges.size() + "`\n");
        w.write("- Callback-family direct `0x00097E32` calls: `" + nmCalls.size() + "`\n");
        w.write("- Explicit sleep-direction NM calls: `" + sleepNmCalls + "`\n");
        w.write("- Errors: `" + errorRows.size() + "`\n\n");
        w.write("## Classification\n\n`" + classification + "`\n\n");

        if ("EXACT_OBJECT_SLEEP_TIMER_TO_NM_TRANSITION_CLOSED".equals(classification)) {
            w.write("The exact 0x4004ACA8 timer registration and a callback/helper path to Sleep, PrepSleep or TimeWait are both statically recovered. Review `_callback_nm_calls.csv` and the predecessor predicate before any bounded stationary experiment.\n\n");
        }
        else if ("EXACT_OBJECT_SLEEP_TIMER_RECOVERED_CALLBACK_CLOSURE_UNRESOLVED".equals(classification)) {
            w.write("The timer registration boundary is now repaired. Stay inside the recovered callback/helper closure next; do not return to command 0x33, A2BC, 0x97AA2 or late reset.\n\n");
        }
        else if ("RAW_TIMER_CALLS_RECOVERED_ARGUMENT_BINDING_INCOMPLETE".equals(classification)) {
            w.write("Raw timer callsites are proven, but PPC ABI argument recovery is still incomplete. The next step, if needed, should be path-sensitive argument provenance at only those recovered raw callsites.\n\n");
        }
        else {
            w.write("No raw e_bl call to 0x000F8B24 was recovered. Because older decompilation showed those registrations, treat this as a decoder/address-contract discrepancy rather than evidence that the timer path does not exist.\n\n");
        }

        w.write("## Review order\n\n");
        w.write("1. `_raw_timer_calls.csv`\n");
        w.write("2. `_exact_4004aca8_registrations.csv`\n");
        w.write("3. `_callback_nm_calls.csv`\n");
        w.write("4. `_callback_helper_edges.csv`\n");
        w.write("5. `_callback_profiles.csv`\n");
        w.write("6. `_timer_dispatch_context.csv`\n");
        w.write("7. `_selected_decompilation.txt`\n");
        w.write("8. `_errors.csv`\n");
        w.close();
    }

    private BufferedWriter writer(String suffix) throws Exception {
        return new BufferedWriter(new FileWriter(
            new File(workDirectory, SCRIPT_NAME + suffix)));
    }

    private void addError(String phase, long address, Throwable t) {
        errorRows.add(new String[] { phase, hex(address),
            t == null ? "" : t.getClass().getSimpleName(),
            t == null ? "" : String.valueOf(t.getMessage()) });
    }

    private String sha256(byte[] bytes) throws Exception {
        MessageDigest digest = MessageDigest.getInstance("SHA-256");
        byte[] hash = digest.digest(bytes);
        StringBuilder b = new StringBuilder();
        for (byte value : hash) {
            b.append(String.format(Locale.ROOT, "%02x", value & 0xff));
        }
        return b.toString();
    }

    private String hex(long value) {
        return String.format(Locale.ROOT, "0x%08X", value & 0xffffffffL);
    }

    private String csv(String value) {
        if (value == null) value = "";
        return "\"" + value.replace("\"", "\"\"")
            .replace("\r", " ").replace("\n", " ") + "\"";
    }

    private String join(List<String> values, String delimiter) {
        StringBuilder b = new StringBuilder();
        for (String value : values) {
            if (b.length() != 0) b.append(delimiter);
            b.append(value);
        }
        return b.toString();
    }

    private void zipDirectory(File directory, File output) throws Exception {
        ZipOutputStream zip = new ZipOutputStream(
            new BufferedOutputStream(new FileOutputStream(output)));
        try {
            File[] files = directory.listFiles();
            if (files == null) return;
            byte[] buffer = new byte[65536];
            for (File file : files) {
                if (!file.isFile()) continue;
                zip.putNextEntry(new ZipEntry(file.getName()));
                FileInputStream input = new FileInputStream(file);
                try {
                    int count;
                    while ((count = input.read(buffer)) >= 0) {
                        if (count > 0) zip.write(buffer, 0, count);
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
}
