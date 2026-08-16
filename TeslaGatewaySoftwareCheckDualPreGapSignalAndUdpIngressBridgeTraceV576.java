// TeslaGatewaySoftwareCheckDualPreGapSignalAndUdpIngressBridgeTraceV576.java
//
// Read-only Ghidra 12.1.2 follow-up after the V571R4 / V571R5R1 Software-page
// bench captures.
//
// Purpose
// -------
// The permanent CAN 0x318 AP0 experiment proved that the CAN318 AP field is both
// necessary for visible AP2 and sufficient to remove the update-check reboot
// boundary.  R4/R5R1 attempted a later temporal AP0 window beginning at the
// command-0x32 call site 0x00077226, but the WDRS behaviour remained unchanged.
// V575 subsequently proved D009016F is fundamentally a CAN 0x3EE receive-backed
// signal, so absence/presence of D009 is not treated as proof that the R4 scratch
// countdown armed.
//
// V576 therefore moves the analysis earlier.  It consumes TWO SD captures:
//   * the R4 capture (log13081352.zip / extracted log), and
//   * the R5R1 capture (log11747.zip / extracted log).
//
// For each capture it:
//   1. parses the framed logger records;
//   2. recovers record time from D00007DD seconds + D00007DE milliseconds;
//   3. identifies the strongest large timestamp discontinuity associated with a
//      D0003F56 startup followed by D0003FC3=0x0800 WDRS;
//   4. scores D-signal ID/value signatures in 20/50/100/250-record windows
//      immediately BEFORE that gap against matched normal-running control
//      windows from the same capture;
//   5. promotes only signatures present before BOTH independent Software-page
//      failures and uncommon in controls.
//
// Static work is strictly downstream of that dual-runtime filter.  For at most
// twelve promoted IDs it:
//   * maps strict stock 20-byte logger tuples;
//   * rollback-only recovers undefined getters where required;
//   * extracts actual SRAM sources used by getter code/decompilation;
//   * finds direct and simple split-constant accesses to those sources;
//   * tests generated 0x20-byte CAN receive descriptors whose primary/secondary
//     buffers contain an actual source;
//   * checks source owners and descriptor callbacks against the already-known
//     earlier/later timing surfaces.
//
// Timing surfaces (not rediscovered):
//   diagTask / UDP command-table owner      0x00078636..0x00078907
//   pre-dispatch corridor                  0x00078636..0x000788F5
//   computed handler dispatch              0x000788F6
//   command-0x32 handler                   0x000771B4..0x0007724B
//   process_vehicle_config_check           0x00088340
//   apply_autopilot_config                 0x000870F0
//   CAN359 / command32 state               0x40016840..0x40016847
//   processed/config-state byte            0x40046F87
//   CAN318 payload/AP field                0x40047CA8..0x40047CAF
//
// Explicitly excluded from runtime promotion because their provenance/reset role
// is already exhausted or they are reset/startup records:
//   D0003F56, D0003FC3, D00040A3, D0043FB1, D0007AD5, D0004E99,
//   D00415A0, D0084A3A, D009016F.
//
// No firmware bytes, RAM, processor state, comments, symbols, references or
// persistent Ghidra database state are modified.  Temporary getter recovery is
// performed inside a transaction that is always rolled back.  Output directory
// need not be empty.
//
// @category TeslaGateway.Analysis
// @menupath Tools.Tesla.Trace Software Check Dual Pre-Gap UDP Ingress Bridge V576

import ghidra.app.cmd.disassemble.PowerPCDisassembleCommand;
import ghidra.app.decompiler.DecompInterface;
import ghidra.app.decompiler.DecompileResults;
import ghidra.app.script.GhidraScript;

import ghidra.program.model.address.Address;
import ghidra.program.model.address.AddressSet;
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
import ghidra.program.model.symbol.Reference;
import ghidra.program.model.symbol.ReferenceIterator;
import ghidra.program.model.symbol.ReferenceManager;

import java.io.BufferedInputStream;
import java.io.BufferedWriter;
import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.FileWriter;
import java.io.InputStream;
import java.io.OutputStreamWriter;
import java.io.PrintWriter;
import java.math.BigInteger;
import java.nio.charset.StandardCharsets;
import java.security.MessageDigest;
import java.text.SimpleDateFormat;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Comparator;
import java.util.Date;
import java.util.Deque;
import java.util.Enumeration;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Queue;
import java.util.Set;
import java.util.TimeZone;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.zip.ZipEntry;
import java.util.zip.ZipFile;
import java.util.zip.ZipOutputStream;

public class TeslaGatewaySoftwareCheckDualPreGapSignalAndUdpIngressBridgeTraceV576
        extends GhidraScript {

    private static final String PREFIX =
        "TeslaGatewaySoftwareCheckDualPreGapSignalAndUdpIngressBridgeTraceV576";

    private static final String EXPECTED_LANGUAGE =
        "PowerPC:BE:64:VLE-32addr";
    private static final String EXPECTED_SHA256 =
        "889ab36ae6d17bb897587df85db6201f32cb33f01ba101962979f765ef0ee3fe";

    private static final String CACHE_OPTIONS =
        "Tesla Gateway Persistent Analysis Cache";
    private static final String CACHE_KEY = "cache_version";
    private static final String CACHE_SHA_KEY = "source_sha256";
    private static final String SECONDARY_KEY = "secondary_recovery";
    private static final String REQUIRED_CACHE = "V448R2";
    private static final String REQUIRED_SECONDARY = "V461R1";

    private static final long IMAGE_START = 0x00000000L;
    private static final long IMAGE_END   = 0x001FFFFFL;
    private static final long APP_START   = 0x00020000L;
    private static final long APP_END     = 0x00149299L;
    private static final long RAM_START   = 0x40000000L;
    private static final long RAM_END     = 0x4009FFFFL;

    private static final long TS_SECONDS  = 0xD00007DDL;
    private static final long TS_MILLIS   = 0xD00007DEL;
    private static final long STARTUP     = 0xD0003F56L;
    private static final long RESET       = 0xD0003FC3L;
    private static final int RESET_WDRS   = 0x0800;

    private static final long DIAGTASK_ENTRY = 0x00078636L;
    private static final long DIAGTASK_END   = 0x00078907L;
    private static final long PRE_DISPATCH_START = 0x00078636L;
    private static final long PRE_DISPATCH_END   = 0x000788F5L;
    private static final long DISPATCH_SITE = 0x000788F6L;
    private static final long COMMAND32_ENTRY = 0x000771B4L;
    private static final long COMMAND32_END   = 0x0007724BL;
    private static final long CONFIG_CHECK    = 0x00088340L;
    private static final long AP_OWNER        = 0x000870F0L;

    private static final long CMD32_MEM_START = 0x40016840L;
    private static final long CMD32_MEM_END   = 0x40016847L;
    private static final long PROCESSED_STATE = 0x40046F87L;
    private static final long CAN318_START    = 0x40047CA8L;
    private static final long CAN318_END      = 0x40047CAFL;

    private static final int[] WINDOWS = new int[]{20,50,100,250};
    private static final int MAX_PROMOTED_IDS = 12;
    private static final int SIGNAL_TUPLE_SIZE = 20;
    private static final long MIN_GAP_MS = 10000L;
    private static final long MAX_GAP_MS = 90000L;

    private static final Set<Long> EXCLUDED_IDS = new HashSet<Long>(Arrays.asList(
        Long.valueOf(0xD0003F56L), Long.valueOf(0xD0003FC3L),
        Long.valueOf(0xD00040A3L), Long.valueOf(0xD0043FB1L),
        Long.valueOf(0xD0007AD5L), Long.valueOf(0xD0004E99L),
        Long.valueOf(0xD00415A0L), Long.valueOf(0xD0084A3AL),
        Long.valueOf(0xD009016FL)
    ));

    private static final Pattern DAT_PATTERN =
        Pattern.compile("(?:_?DAT_)([0-9a-fA-F]{8})");
    private static final Pattern LIS_PATTERN =
        Pattern.compile("^(?:e_)?lis\\s+(r\\d+),([^\\s,]+)$");
    private static final Pattern ADD_PATTERN =
        Pattern.compile("^(?:e_)?(?:add16i|addi)\\s+(r\\d+),(r\\d+),([^\\s,]+)$");
    private static final Pattern ORI_PATTERN =
        Pattern.compile("^(?:e_)?ori\\s+(r\\d+),(r\\d+),([^\\s,]+)$");
    private static final Pattern ORIS_PATTERN =
        Pattern.compile("^(?:e_)?oris\\s+(r\\d+),(r\\d+),([^\\s,]+)$");
    private static final Pattern MEM_PATTERN =
        Pattern.compile("(-?(?:0x)?[0-9a-f]+)\\((r\\d+)\\)");

    private Memory memory;
    private Listing listing;
    private FunctionManager functions;
    private ReferenceManager references;
    private File outDir;
    private String runStem;
    private String sourceSha;

    private final List<String[]> sourceRows = new ArrayList<String[]>();
    private final List<String[]> gapRows = new ArrayList<String[]>();
    private final List<String[]> windowRows = new ArrayList<String[]>();
    private final List<String[]> rankingRows = new ArrayList<String[]>();
    private final List<String[]> promotedRows = new ArrayList<String[]>();
    private final List<String[]> mapRows = new ArrayList<String[]>();
    private final List<String[]> getterRows = new ArrayList<String[]>();
    private final List<String[]> getterSourceRows = new ArrayList<String[]>();
    private final List<String[]> accessRows = new ArrayList<String[]>();
    private final List<String[]> descriptorRows = new ArrayList<String[]>();
    private final List<String[]> focusRows = new ArrayList<String[]>();
    private final List<String[]> errorRows = new ArrayList<String[]>();

    private final Map<Long,String> decompilation =
        new LinkedHashMap<Long,String>();
    private final Map<Long,Set<Long>> outgoing =
        new LinkedHashMap<Long,Set<Long>>();

    private static class LogRecord {
        int index;
        int offset;
        long id = -1L;
        byte[] value = new byte[0];
        long timeMs = -1L;
    }

    private static class Capture {
        String label;
        File input;
        String inputSha;
        String memberName;
        List<LogRecord> records = new ArrayList<LogRecord>();
        TargetGap target;
    }

    private static class ResetEpisode {
        int startupIndex;
        int resetIndex;
        int resetValue;
    }

    private static class TargetGap {
        int gapStartIndex;
        int gapEndIndex;
        long gapStartMs;
        long gapEndMs;
        long gapMs;
        int startupIndex;
        int resetIndex;
        int recordsSincePreviousStartup;
        int score;
    }

    private static class Window {
        String capture;
        String kind;
        int width;
        int ordinal;
        int start;
        int end;
    }

    private static class SignatureStat {
        long id;
        String value;
        int width;
        int targetPresence;
        int controlPresence;
        int controlTotal;
        int nearestA = Integer.MAX_VALUE;
        int nearestB = Integer.MAX_VALUE;
        int score;
    }

    private static class Promoted {
        long id;
        String value;
        int width;
        int score;
        int controlPresence;
        int controlTotal;
        int nearestA;
        int nearestB;
    }

    private static class SignalMap {
        long record;
        long id;
        long backing;
        long flags;
        long getterA;
        long getterB;
    }

    private static class SourceSpan {
        long signalId;
        long getter;
        long start;
        long end;
        String evidence;
    }

    private final List<Promoted> promoted = new ArrayList<Promoted>();
    private final List<SignalMap> signalMaps = new ArrayList<SignalMap>();
    private final List<SourceSpan> sourceSpans = new ArrayList<SourceSpan>();
    private final Set<Long> sourceOwnerEntries = new LinkedHashSet<Long>();
    private final Set<Long> passiveSignalIds = new LinkedHashSet<Long>();
    private final Set<Long> postFocusOwners = new LinkedHashSet<Long>();
    private final Set<Long> preDispatchOwners = new LinkedHashSet<Long>();

    @Override
    protected void run() throws Exception {
        if (currentProgram == null)
            throw new IllegalStateException("No Ghidra program is open.");

        memory = currentProgram.getMemory();
        listing = currentProgram.getListing();
        functions = currentProgram.getFunctionManager();
        references = currentProgram.getReferenceManager();

        validateSource();

        File r4 = askFile(
            "Select R4 Software-page capture (log13081352.zip or extracted log)",
            "Select");
        if (r4 == null) return;

        File r5 = askFile(
            "Select R5R1 Software-page capture (log11747.zip or extracted log)",
            "Select");
        if (r5 == null) return;

        outDir = askDirectory(
            "Select V576 output folder (need not be empty)", "Select");
        if (outDir == null) return;
        if (!outDir.exists() && !outDir.mkdirs())
            throw new IllegalStateException("Could not create output directory.");

        runStem = PREFIX + "_" + timestamp();

        Capture capA = parseCapture("R4", r4);
        Capture capB = parseCapture("R5R1", r5);

        capA.target = findTargetGap(capA);
        capB.target = findTargetGap(capB);
        if (capA.target == null || capB.target == null)
            throw new IllegalStateException(
                "V576 could not recover a large pre-WDRS timestamp gap in both captures. " +
                "Review _errors.csv if partial output was produced.");

        recordGap(capA);
        recordGap(capB);

        List<Window> windows = new ArrayList<Window>();
        buildWindows(capA, windows);
        buildWindows(capB, windows);
        recordWindows(windows);
        rankDualPreGap(capA, capB, windows);

        parseSignalTable();

        int tx = currentProgram.startTransaction(
            PREFIX + " temporary getter recovery");
        try {
            recoverAndAnalyseGetters();
            buildCallGraph();
            collectSourceAccesses();
            scanReceiveDescriptors();
            collectFocusIntersections();
            writeOutputs(capA, capB);
            zipOutputs();
        }
        finally {
            currentProgram.endTransaction(tx, false);
        }

        println(PREFIX + " complete.");
        println("R4 records: " + capA.records.size());
        println("R5R1 records: " + capB.records.size());
        println("Promoted IDs: " + promoted.size());
        println("Actual source spans: " + sourceSpans.size());
        println("Errors: " + errorRows.size());
        println("Bundle: " + file("_bundle.zip").getAbsolutePath());
    }

    private void validateSource() throws Exception {
        String lang = currentProgram.getLanguageID().toString();
        sourceSha = sha256Program();
        String cache = currentProgram.getOptions(CACHE_OPTIONS)
            .getString(CACHE_KEY, "");
        String cacheSha = currentProgram.getOptions(CACHE_OPTIONS)
            .getString(CACHE_SHA_KEY, "");
        String secondary = currentProgram.getOptions(CACHE_OPTIONS)
            .getString(SECONDARY_KEY, "");

        if (!EXPECTED_LANGUAGE.equals(lang))
            throw new IllegalStateException("Unexpected language: " + lang);
        if (!EXPECTED_SHA256.equalsIgnoreCase(sourceSha))
            throw new IllegalStateException(
                "V576 requires exact stock initialized flash SHA256. Found " + sourceSha);
        if (!REQUIRED_CACHE.equals(cache) ||
            !sourceSha.equalsIgnoreCase(cacheSha) ||
            !REQUIRED_SECONDARY.equals(secondary))
            throw new IllegalStateException(
                "V576 requires the saved V448R2 + V461R1 analysed stock project.");

        sourceRows.add(new String[]{"program", currentProgram.getName(), ""});
        sourceRows.add(new String[]{"language", lang, ""});
        sourceRows.add(new String[]{"stock_sha256", sourceSha, ""});
        sourceRows.add(new String[]{"base_cache", cache, ""});
        sourceRows.add(new String[]{"secondary_recovery", secondary, ""});
        sourceRows.add(new String[]{"firmware_modified", "false", ""});
        sourceRows.add(new String[]{"persistent_database_modified", "false",
            "temporary getter recovery always rolled back"});
    }

    private Capture parseCapture(String label, File input) throws Exception {
        Capture cap = new Capture();
        cap.label = label;
        cap.input = input;
        byte[] raw = readFile(input);
        cap.inputSha = sha256(raw);

        if (looksZip(raw)) {
            ZipFile zip = new ZipFile(input);
            try {
                Enumeration<? extends ZipEntry> entries = zip.entries();
                int best = -1;
                while (entries.hasMoreElements()) {
                    ZipEntry ze = entries.nextElement();
                    if (ze.isDirectory()) continue;
                    InputStream in = new BufferedInputStream(zip.getInputStream(ze));
                    byte[] data;
                    try { data = readAll(in); }
                    finally { in.close(); }
                    List<LogRecord> candidate = parseRecords(data);
                    if (candidate.size() > best) {
                        best = candidate.size();
                        cap.records = candidate;
                        cap.memberName = ze.getName();
                    }
                }
            }
            finally { zip.close(); }
        }
        else {
            cap.records = parseRecords(raw);
            cap.memberName = input.getName();
        }

        if (cap.records.size() < 100)
            throw new IllegalStateException(
                label + " capture contains too few framed records: " + cap.records.size());

        assignTimes(cap.records);
        sourceRows.add(new String[]{label + "_input", input.getAbsolutePath(), cap.inputSha});
        sourceRows.add(new String[]{label + "_selected_member", cap.memberName,
            Integer.toString(cap.records.size()) + " framed records"});
        return cap;
    }

    private List<LogRecord> parseRecords(byte[] bytes) {
        List<LogRecord> out = new ArrayList<LogRecord>();
        int p = 0;
        int idx = 0;
        while (p + 4 <= bytes.length && !monitor.isCancelled()) {
            if ((bytes[p] & 0xff) != 0xAA) {
                p++;
                continue;
            }
            int declared = bytes[p + 3] & 0xff;
            int total = declared + 1;
            if (declared < 8 || p + total > bytes.length) {
                p++;
                continue;
            }
            LogRecord r = new LogRecord();
            r.index = idx++;
            r.offset = p;
            if (total >= 11) {
                r.id = u32be(bytes, p + 6);
                int valueStart = p + 10;
                int valueEnd = p + total - 1; // final byte is framing/check byte
                if (valueEnd > valueStart)
                    r.value = slice(bytes, valueStart, valueEnd - valueStart);
            }
            out.add(r);
            p += total;
        }
        return out;
    }

    private void assignTimes(List<LogRecord> records) {
        long seconds = -1L;
        long millis = 0L;
        for (LogRecord r : records) {
            if (r.id == TS_SECONDS && r.value.length >= 4) {
                long v = u32be(r.value, 0);
                if (v >= 1000000000L && v <= 3000000000L)
                    seconds = v;
            }
            else if (r.id == TS_MILLIS && r.value.length > 0) {
                long v;
                if (r.value.length >= 4) v = u32be(r.value, 0);
                else if (r.value.length >= 2)
                    v = ((r.value[0] & 0xffL) << 8) | (r.value[1] & 0xffL);
                else v = r.value[0] & 0xffL;
                millis = v % 1000L;
            }
            if (seconds > 0)
                r.timeMs = seconds * 1000L + millis;
        }
    }

    private TargetGap findTargetGap(Capture cap) {
        List<ResetEpisode> episodes = collectWdrsEpisodes(cap.records);
        TargetGap best = null;

        for (ResetEpisode ep : episodes) {
            int lo = Math.max(1, ep.startupIndex - 350);
            int hi = Math.min(cap.records.size() - 1, ep.startupIndex + 350);
            long bestDelta = -1L;
            int bestJump = -1;

            for (int i = lo; i <= hi; i++) {
                long a = cap.records.get(i - 1).timeMs;
                long b = cap.records.get(i).timeMs;
                if (a <= 0 || b <= 0 || b <= a) continue;
                long d = b - a;
                if (d >= MIN_GAP_MS && d <= MAX_GAP_MS && d > bestDelta) {
                    bestDelta = d;
                    bestJump = i;
                }
            }
            if (bestJump < 0) continue;

            int prevStartup = -1;
            for (int i = ep.startupIndex - 1; i >= 0; i--) {
                if (cap.records.get(i).id == STARTUP) {
                    prevStartup = i;
                    break;
                }
            }
            int since = prevStartup < 0
                ? ep.startupIndex
                : ep.startupIndex - prevStartup;

            TargetGap g = new TargetGap();
            g.gapStartIndex = bestJump - 1;
            g.gapEndIndex = bestJump;
            g.gapStartMs = cap.records.get(bestJump - 1).timeMs;
            g.gapEndMs = cap.records.get(bestJump).timeMs;
            g.gapMs = bestDelta;
            g.startupIndex = ep.startupIndex;
            g.resetIndex = ep.resetIndex;
            g.recordsSincePreviousStartup = since;
            g.score = Math.min(since, 10000) + (int)Math.min(bestDelta / 10L, 9000L);

            if (best == null || g.score > best.score ||
                (g.score == best.score && g.startupIndex > best.startupIndex))
                best = g;
        }

        if (best == null)
            addError("runtime_target_gap", -1L,
                cap.label + ": no 10-90 s timestamp jump associated with WDRS startup");
        return best;
    }

    private List<ResetEpisode> collectWdrsEpisodes(List<LogRecord> records) {
        List<ResetEpisode> out = new ArrayList<ResetEpisode>();
        for (int i = 0; i < records.size(); i++) {
            if (records.get(i).id != STARTUP) continue;
            int limit = Math.min(records.size(), i + 12);
            for (int j = i + 1; j < limit; j++) {
                LogRecord r = records.get(j);
                if (r.id == RESET) {
                    int value = resetValue(r.value);
                    if (value == RESET_WDRS) {
                        ResetEpisode ep = new ResetEpisode();
                        ep.startupIndex = i;
                        ep.resetIndex = j;
                        ep.resetValue = value;
                        out.add(ep);
                    }
                    break;
                }
            }
        }
        return out;
    }

    private int resetValue(byte[] v) {
        if (v == null || v.length == 0) return -1;
        if (v.length >= 2)
            return ((v[0] & 0xff) << 8) | (v[1] & 0xff);
        return v[0] & 0xff;
    }

    private void recordGap(Capture cap) {
        TargetGap g = cap.target;
        gapRows.add(new String[]{
            cap.label,
            Integer.toString(g.gapStartIndex),
            Integer.toString(g.gapEndIndex),
            formatTime(g.gapStartMs),
            formatTime(g.gapEndMs),
            String.format(Locale.ROOT, "%.3f", g.gapMs / 1000.0),
            Integer.toString(g.startupIndex),
            Integer.toString(g.resetIndex),
            Integer.toString(g.recordsSincePreviousStartup),
            Integer.toString(g.score)
        });
    }

    private void buildWindows(Capture cap, List<Window> out) {
        for (int width : WINDOWS) {
            Window target = new Window();
            target.capture = cap.label;
            target.kind = "TARGET";
            target.width = width;
            target.ordinal = 0;
            target.end = cap.target.gapStartIndex;
            target.start = Math.max(0, target.end - width + 1);
            out.add(target);

            int ordinal = 0;
            int[] offsets = new int[]{400,700,1000,1300,1600,1900,2200,2500,2800};
            for (int offset : offsets) {
                int end = cap.target.gapStartIndex - offset;
                int start = end - width + 1;
                if (start < 0 || end < 0) continue;
                if (containsStartupOrReset(cap.records, start, end)) continue;
                if (Math.abs(end - cap.target.gapStartIndex) < 300) continue;
                Window c = new Window();
                c.capture = cap.label;
                c.kind = "CONTROL";
                c.width = width;
                c.ordinal = ++ordinal;
                c.start = start;
                c.end = end;
                out.add(c);
            }
        }
    }

    private boolean containsStartupOrReset(List<LogRecord> records, int start, int end) {
        for (int i = Math.max(0,start); i <= Math.min(end, records.size()-1); i++) {
            long id = records.get(i).id;
            if (id == STARTUP || id == RESET) return true;
        }
        return false;
    }

    private void recordWindows(List<Window> windows) {
        for (Window w : windows) {
            windowRows.add(new String[]{
                w.capture, w.kind, Integer.toString(w.width),
                Integer.toString(w.ordinal), Integer.toString(w.start),
                Integer.toString(w.end)
            });
        }
    }

    private void rankDualPreGap(Capture capA, Capture capB, List<Window> windows) {
        Map<String,Capture> captures = new HashMap<String,Capture>();
        captures.put(capA.label, capA);
        captures.put(capB.label, capB);

        Map<Long,Promoted> bestById = new LinkedHashMap<Long,Promoted>();

        for (int width : WINDOWS) {
            List<Window> targetWindows = new ArrayList<Window>();
            List<Window> controlWindows = new ArrayList<Window>();
            for (Window w : windows) {
                if (w.width != width) continue;
                if ("TARGET".equals(w.kind)) targetWindows.add(w);
                else controlWindows.add(w);
            }

            Map<String,SignatureStat> stats = new LinkedHashMap<String,SignatureStat>();

            for (Window w : targetWindows) {
                Capture cap = captures.get(w.capture);
                Map<String,Integer> nearest = signaturesInWindow(cap.records, w);
                for (Map.Entry<String,Integer> e : nearest.entrySet()) {
                    String key = e.getKey();
                    SignatureStat s = stats.get(key);
                    if (s == null) {
                        s = makeStat(key, width);
                        if (s == null) continue;
                        stats.put(key, s);
                    }
                    s.targetPresence++;
                    if ("R4".equals(w.capture)) s.nearestA = e.getValue().intValue();
                    if ("R5R1".equals(w.capture)) s.nearestB = e.getValue().intValue();
                }
            }

            for (Window w : controlWindows) {
                Capture cap = captures.get(w.capture);
                Set<String> present = signaturesInWindow(cap.records, w).keySet();
                for (SignatureStat s : stats.values()) s.controlTotal++;
                for (String key : present) {
                    SignatureStat s = stats.get(key);
                    if (s != null) s.controlPresence++;
                }
            }

            for (SignatureStat s : stats.values()) {
                int avgDist = 500;
                if (s.nearestA != Integer.MAX_VALUE && s.nearestB != Integer.MAX_VALUE)
                    avgDist = (s.nearestA + s.nearestB) / 2;
                double rate = s.controlTotal == 0 ? 1.0 :
                    ((double)s.controlPresence / (double)s.controlTotal);
                s.score = s.targetPresence * 1000 +
                    (s.controlTotal - s.controlPresence) * 40 +
                    Math.max(0, 300 - width) - avgDist * 2;

                boolean excluded = EXCLUDED_IDS.contains(Long.valueOf(s.id));
                boolean promote = s.targetPresence == 2 &&
                    s.controlTotal >= 2 && rate <= 0.25 && !excluded;

                rankingRows.add(new String[]{
                    hex(s.id), s.value, Integer.toString(width),
                    Integer.toString(s.targetPresence),
                    Integer.toString(s.controlPresence),
                    Integer.toString(s.controlTotal),
                    String.format(Locale.ROOT, "%.3f", rate),
                    s.nearestA == Integer.MAX_VALUE ? "" : Integer.toString(s.nearestA),
                    s.nearestB == Integer.MAX_VALUE ? "" : Integer.toString(s.nearestB),
                    Integer.toString(s.score), Boolean.toString(excluded),
                    Boolean.toString(promote)
                });

                if (!promote) continue;
                Promoted old = bestById.get(Long.valueOf(s.id));
                if (old == null || s.score > old.score) {
                    Promoted p = new Promoted();
                    p.id = s.id;
                    p.value = s.value;
                    p.width = width;
                    p.score = s.score;
                    p.controlPresence = s.controlPresence;
                    p.controlTotal = s.controlTotal;
                    p.nearestA = s.nearestA;
                    p.nearestB = s.nearestB;
                    bestById.put(Long.valueOf(p.id), p);
                }
            }
        }

        promoted.addAll(bestById.values());
        Collections.sort(promoted, new Comparator<Promoted>() {
            @Override public int compare(Promoted a, Promoted b) {
                int c = Integer.compare(b.score, a.score);
                if (c != 0) return c;
                return Long.compare(a.id, b.id);
            }
        });
        if (promoted.size() > MAX_PROMOTED_IDS)
            promoted.subList(MAX_PROMOTED_IDS, promoted.size()).clear();

        int rank = 0;
        for (Promoted p : promoted) {
            promotedRows.add(new String[]{
                Integer.toString(++rank), hex(p.id), p.value,
                Integer.toString(p.width), Integer.toString(p.score),
                Integer.toString(p.controlPresence), Integer.toString(p.controlTotal),
                Integer.toString(p.nearestA), Integer.toString(p.nearestB)
            });
        }
    }

    private Map<String,Integer> signaturesInWindow(List<LogRecord> records, Window w) {
        Map<String,Integer> out = new LinkedHashMap<String,Integer>();
        int start = Math.max(0, w.start);
        int end = Math.min(records.size() - 1, w.end);
        for (int i = start; i <= end; i++) {
            LogRecord r = records.get(i);
            if ((r.id & 0xF0000000L) != 0xD0000000L) continue;
            String value = bytesHex(r.value);
            String key = hex(r.id) + "|" + value;
            int distance = end - i;
            Integer old = out.get(key);
            if (old == null || distance < old.intValue())
                out.put(key, Integer.valueOf(distance));
        }
        return out;
    }

    private SignatureStat makeStat(String key, int width) {
        int bar = key.indexOf('|');
        if (bar <= 0) return null;
        SignatureStat s = new SignatureStat();
        try { s.id = Long.parseLong(key.substring(2, bar), 16) & 0xffffffffL; }
        catch (Throwable t) { return null; }
        s.value = key.substring(bar + 1);
        s.width = width;
        return s;
    }

    private void parseSignalTable() throws Exception {
        Set<Long> wanted = new HashSet<Long>();
        for (Promoted p : promoted) wanted.add(Long.valueOf(p.id));
        if (wanted.isEmpty()) return;

        for (long a = APP_START; a + SIGNAL_TUPLE_SIZE - 1 <= APP_END; a += 4) {
            long id = readU32(a);
            if (!wanted.contains(Long.valueOf(id))) continue;
            long backing = readU32(a + 4);
            long flags = readU32(a + 8);
            long g1 = readU32(a + 12);
            long g2 = readU32(a + 16);
            if (!isCodePtr(g1) || !isCodePtr(g2)) continue;
            SignalMap m = new SignalMap();
            m.record = a; m.id = id; m.backing = backing; m.flags = flags;
            m.getterA = normalizeCode(g1); m.getterB = normalizeCode(g2);
            signalMaps.add(m);
            mapRows.add(new String[]{
                hex(a), hex(id), hex(backing), hex(flags),
                hex(m.getterA), hex(m.getterB), "STRICT_20_BYTE_TUPLE"
            });
        }
    }

    private void recoverAndAnalyseGetters() {
        Set<Long> getters = new LinkedHashSet<Long>();
        for (SignalMap m : signalMaps) {
            getters.add(Long.valueOf(m.getterA));
            getters.add(Long.valueOf(m.getterB));
        }

        for (Long gv : getters) {
            long getter = gv.longValue();
            try {
                Function f = recoverFunction(getter);
                boolean recovered = f != null;
                String text = recovered ? decompile(f) : "";
                if (recovered) decompilation.put(Long.valueOf(getter), text);
                getterRows.add(new String[]{
                    hex(getter), recovered ? hex(f.getEntryPoint().getOffset()) : "",
                    recovered ? f.getName() : "", Boolean.toString(recovered),
                    Integer.toString(text == null ? 0 : text.length())
                });
                if (f != null) collectGetterSources(getter, f, text);
            }
            catch (Throwable t) {
                addError("getter_recovery", getter, t.toString());
            }
        }
    }

    private Function recoverFunction(long entry) throws Exception {
        Address a = addr(entry);
        Function f = functions.getFunctionAt(a);
        if (f == null) f = functions.getFunctionContaining(a);
        if (f != null) return f;

        long endValue = Math.min(APP_END, entry + 0x9eL);
        Address end = addr(endValue);
        try {
            clearListing(a, end);
            Register vle = currentProgram.getRegister("VLE");
            if (vle == null) vle = currentProgram.getRegister("vle");
            if (vle != null) {
                ProgramContext pc = currentProgram.getProgramContext();
                pc.setValue(vle, a, end, BigInteger.ONE);
            }
            PowerPCDisassembleCommand cmd =
                new PowerPCDisassembleCommand(a, new AddressSet(a, end), true);
            cmd.applyTo(currentProgram, monitor);
            f = functions.getFunctionAt(a);
            if (f == null) {
                try { createFunction(a, "TEMP_V576_GETTER_" + hexBare(entry)); }
                catch (Throwable ignored) {}
                f = functions.getFunctionAt(a);
            }
        }
        catch (Throwable t) {
            addError("temporary_vle_recovery", entry, t.toString());
        }
        return f;
    }

    private String decompile(Function f) {
        DecompInterface ifc = new DecompInterface();
        try {
            ifc.openProgram(currentProgram);
            DecompileResults r = ifc.decompileFunction(f, 30, monitor);
            if (r != null && r.decompileCompleted() && r.getDecompiledFunction() != null)
                return r.getDecompiledFunction().getC();
            return "";
        }
        catch (Throwable t) {
            addError("decompile", f.getEntryPoint().getOffset(), t.toString());
            return "";
        }
        finally {
            try { ifc.dispose(); } catch (Throwable ignored) {}
        }
    }

    private void collectGetterSources(long getter, Function f, String text) {
        Set<String> emitted = new LinkedHashSet<String>();
        Map<String,Long> regs = new HashMap<String,Long>();

        InstructionIterator it = listing.getInstructions(f.getBody(), true);
        while (it.hasNext()) {
            Instruction ins = it.next();
            long site = u32(ins.getAddress().getOffset());

            try {
                Reference[] rr = ins.getReferencesFrom();
                if (rr != null) {
                    for (Reference r : rr) {
                        long target = u32(r.getToAddress().getOffset());
                        if (inRam(target))
                            addSourceForGetter(getter, target, target,
                                "GHIDRA_REFERENCE@" + hex(site), emitted);
                    }
                }
            }
            catch (Throwable ignored) {}

            resolveInstructionMemory(ins, regs, new MemoryResolvedHandler() {
                @Override public void hit(long siteValue, long addressValue,
                        int width, boolean store, String evidence) {
                    if (!store && inRam(addressValue))
                        addSourceForGetter(getter, addressValue,
                            Math.min(RAM_END, addressValue + Math.max(1,width) - 1L),
                            "CONST_PROP@" + hex(siteValue), emitted);
                }
            });
        }

        if (text != null && text.length() > 0) {
            Matcher m = DAT_PATTERN.matcher(text);
            while (m.find()) {
                try {
                    long a = Long.parseLong(m.group(1), 16) & 0xffffffffL;
                    if (inRam(a))
                        addSourceForGetter(getter, a, a,
                            "DECOMPILER_DAT", emitted);
                }
                catch (Throwable ignored) {}
            }
        }
    }

    private void addSourceForGetter(long getter, long start, long end,
            String evidence, Set<String> emitted) {
        String key = hex(start) + ":" + hex(end);
        if (!emitted.add(key)) return;

        for (SignalMap map : signalMaps) {
            if (map.getterA != getter && map.getterB != getter) continue;
            SourceSpan s = new SourceSpan();
            s.signalId = map.id;
            s.getter = getter;
            s.start = start;
            s.end = end;
            s.evidence = evidence;
            sourceSpans.add(s);
            getterSourceRows.add(new String[]{
                hex(map.id), hex(getter), hex(map.backing),
                hex(start), hex(end), evidence,
                Boolean.toString(start == map.backing || end == map.backing)
            });
        }
    }

    private void buildCallGraph() {
        FunctionIterator fi = functions.getFunctions(true);
        while (fi.hasNext() && !monitor.isCancelled()) {
            Function f = fi.next();
            long caller = u32(f.getEntryPoint().getOffset());
            if (!inApp(caller)) continue;
            InstructionIterator ii = listing.getInstructions(f.getBody(), true);
            while (ii.hasNext()) {
                Instruction ins = ii.next();
                Long target = directCall(ins);
                if (target != null && inApp(target.longValue()))
                    addEdge(caller, target.longValue());
            }
        }
    }

    private void collectSourceAccesses() {
        if (sourceSpans.isEmpty()) return;
        Set<String> emitted = new LinkedHashSet<String>();

        for (SourceSpan s : sourceSpans) {
            for (long a = s.start; a <= s.end && a - s.start < 16; a++) {
                try {
                    ReferenceIterator it = references.getReferencesTo(addr(a));
                    while (it.hasNext()) {
                        Reference r = it.next();
                        long site = u32(r.getFromAddress().getOffset());
                        Instruction ins = listing.getInstructionContaining(addr(site));
                        Function owner = functionAt(site);
                        if (ins == null || owner == null) continue;
                        boolean store = isStore(ins);
                        String key = hex(s.signalId) + ":" + hex(site) + ":REF";
                        if (!emitted.add(key)) continue;
                        addAccessRow(s, site, owner, store, "GHIDRA_REFERENCE", ins.toString());
                    }
                }
                catch (Throwable t) {
                    addError("source_reference", a, t.toString());
                }
            }
        }

        FunctionIterator fi = functions.getFunctions(true);
        while (fi.hasNext() && !monitor.isCancelled()) {
            Function f = fi.next();
            long ownerEntry = u32(f.getEntryPoint().getOffset());
            if (!inApp(ownerEntry)) continue;
            final Function ownerFinal = f;
            final Set<String> emittedFinal = emitted;
            Map<String,Long> regs = new HashMap<String,Long>();
            InstructionIterator ii = listing.getInstructions(f.getBody(), true);
            while (ii.hasNext()) {
                Instruction ins = ii.next();
                final Instruction insFinal = ins;
                resolveInstructionMemory(ins, regs, new MemoryResolvedHandler() {
                    @Override public void hit(long site, long addressValue,
                            int width, boolean store, String evidence) {
                        long end = addressValue + Math.max(1,width) - 1L;
                        for (SourceSpan s : sourceSpans) {
                            if (!overlaps(addressValue, end, s.start, s.end)) continue;
                            String key = hex(s.signalId) + ":" + hex(site) + ":CP";
                            if (!emittedFinal.add(key)) continue;
                            addAccessRow(s, site, ownerFinal, store,
                                "LINEAR_CONST_PROP", insFinal.toString());
                        }
                    }
                });
            }
        }
    }

    private void addAccessRow(SourceSpan s, long site, Function owner,
            boolean store, String method, String instruction) {
        long entry = u32(owner.getEntryPoint().getOffset());
        sourceOwnerEntries.add(Long.valueOf(entry));
        accessRows.add(new String[]{
            hex(s.signalId), hex(s.start), hex(s.end),
            hex(site), hex(entry), owner.getName(),
            store ? "WRITE" : "READ", method, clean(instruction)
        });
    }

    private interface MemoryResolvedHandler {
        void hit(long site, long addressValue, int width,
            boolean store, String evidence);
    }

    private void resolveInstructionMemory(Instruction ins, Map<String,Long> regs,
            MemoryResolvedHandler handler) {
        String text = lower(ins.toString());
        String mnemonic = lower(ins.getMnemonicString());
        long site = u32(ins.getAddress().getOffset());

        Matcher mm = MEM_PATTERN.matcher(text);
        if (mm.find()) {
            String base = mm.group(2);
            Long bv = regs.get(base);
            if (bv != null) {
                try {
                    long disp = parseSignedToken(mm.group(1));
                    long address = u32(bv.longValue() + disp);
                    int width = memoryWidth(mnemonic);
                    boolean store = isStoreMnemonic(mnemonic);
                    if (isMemoryMnemonic(mnemonic))
                        handler.hit(site, address, width, store,
                            base + "=" + hex(bv.longValue()) + ",disp=" + disp);
                }
                catch (Throwable ignored) {}
            }
        }

        Matcher lm = LIS_PATTERN.matcher(text);
        if (lm.matches()) {
            try {
                long high = parseUnsignedToken(lm.group(2)) & 0xffffL;
                regs.put(lm.group(1), Long.valueOf(u32(high << 16)));
                return;
            }
            catch (Throwable ignored) {}
        }

        Matcher am = ADD_PATTERN.matcher(text);
        if (am.matches()) {
            Long base = regs.get(am.group(2));
            if (base != null) {
                try {
                    long imm = parseSignedToken(am.group(3));
                    regs.put(am.group(1), Long.valueOf(u32(base.longValue() + imm)));
                    return;
                }
                catch (Throwable ignored) {}
            }
            regs.remove(am.group(1));
            return;
        }

        Matcher om = ORI_PATTERN.matcher(text);
        if (om.matches()) {
            Long base = regs.get(om.group(2));
            if (base != null) {
                try {
                    long imm = parseUnsignedToken(om.group(3)) & 0xffffL;
                    regs.put(om.group(1), Long.valueOf(u32(base.longValue() | imm)));
                    return;
                }
                catch (Throwable ignored) {}
            }
            regs.remove(om.group(1));
            return;
        }

        Matcher osm = ORIS_PATTERN.matcher(text);
        if (osm.matches()) {
            Long base = regs.get(osm.group(2));
            if (base != null) {
                try {
                    long imm = (parseUnsignedToken(osm.group(3)) & 0xffffL) << 16;
                    regs.put(osm.group(1), Long.valueOf(u32(base.longValue() | imm)));
                    return;
                }
                catch (Throwable ignored) {}
            }
            regs.remove(osm.group(1));
            return;
        }

        String first = firstRegister(ins);
        if (first.length() > 0 && writesFirstRegister(ins))
            regs.remove(first);
    }

    private void scanReceiveDescriptors() throws Exception {
        Set<String> emitted = new LinkedHashSet<String>();
        for (long rec = APP_START; rec + 0x1f <= APP_END; rec += 4) {
            long primary = readU32(rec);
            long secondary = readU32(rec + 4);
            long idDlc = readU32(rec + 8);
            long callbackRaw = readU32(rec + 0x14);
            int canId = (int)((idDlc >>> 16) & 0xffffL);
            int dlc = (int)(idDlc & 0xffffL);
            long callback = normalizeCode(callbackRaw);
            if (canId < 0 || canId > 0x7ff || dlc < 1 || dlc > 8) continue;
            if (!isCodePtr(callbackRaw)) continue;
            boolean primaryRam = inRam(primary);
            boolean secondaryRam = inRam(secondary);
            if (!primaryRam && !secondaryRam) continue;

            for (SourceSpan s : sourceSpans) {
                boolean p = primaryRam && containsSpan(primary, dlc, s.start, s.end);
                boolean q = secondaryRam && containsSpan(secondary, dlc, s.start, s.end);
                if (!p && !q) continue;
                String key = hex(s.signalId) + ":" + hex(rec) + ":" + (p ? "P" : "S");
                if (!emitted.add(key)) continue;
                passiveSignalIds.add(Long.valueOf(s.signalId));
                descriptorRows.add(new String[]{
                    hex(s.signalId), hex(s.start), hex(s.end), hex(rec),
                    String.format(Locale.ROOT,"0x%03X",canId), Integer.toString(dlc),
                    hex(primary), hex(secondary), p ? "PRIMARY" : "SECONDARY",
                    hex(callback), functionName(callback)
                });
                sourceOwnerEntries.add(Long.valueOf(callback));
                Function cb = functionAt(callback);
                if (cb != null && !decompilation.containsKey(Long.valueOf(callback)))
                    decompilation.put(Long.valueOf(callback), decompile(cb));
            }
        }
    }

    private void collectFocusIntersections() {
        Set<Long> memoryFocusOwners = collectMemoryFocusOwners();
        Set<Long> preRoots = collectPreDispatchRoots();

        for (Long ov : sourceOwnerEntries) {
            long owner = ov.longValue();
            Function f = functionAt(owner);
            if (f == null) continue;
            long entry = u32(f.getEntryPoint().getOffset());

            boolean inDiag = bodyOverlaps(f, DIAGTASK_ENTRY, DIAGTASK_END);
            boolean inPre = bodyOverlaps(f, PRE_DISPATCH_START, PRE_DISPATCH_END);
            boolean preReach = inPre || pathFromAny(preRoots, entry, 4) != null;
            boolean cmd32 = entry == COMMAND32_ENTRY || bodyOverlaps(f, COMMAND32_ENTRY, COMMAND32_END) ||
                findPath(entry, COMMAND32_ENTRY, 4) != null ||
                findPath(COMMAND32_ENTRY, entry, 4) != null;
            boolean cfg = entry == CONFIG_CHECK ||
                findPath(entry, CONFIG_CHECK, 4) != null ||
                findPath(CONFIG_CHECK, entry, 4) != null;
            boolean ap = entry == AP_OWNER ||
                findPath(entry, AP_OWNER, 4) != null ||
                findPath(AP_OWNER, entry, 4) != null;
            boolean mem = memoryFocusOwners.contains(Long.valueOf(entry));

            String cls;
            if (preReach) {
                cls = "PRE_DISPATCH_INGRESS_REACHABLE";
                preDispatchOwners.add(Long.valueOf(entry));
            }
            else if (cmd32 || cfg || ap || mem || inDiag) {
                cls = "POST_OR_SHARED_FOCUS_RELATED";
                postFocusOwners.add(Long.valueOf(entry));
            }
            else cls = "NO_KNOWN_TEMPORAL_FOCUS_INTERSECTION";

            focusRows.add(new String[]{
                hex(entry), f.getName(), cls,
                Boolean.toString(inDiag), Boolean.toString(inPre),
                Boolean.toString(preReach), Boolean.toString(cmd32),
                Boolean.toString(cfg), Boolean.toString(ap), Boolean.toString(mem),
                pathText(pathFromAny(preRoots, entry, 4)),
                pathText(findPath(entry, COMMAND32_ENTRY, 4)),
                pathText(findPath(COMMAND32_ENTRY, entry, 4))
            });
        }
    }

    private Set<Long> collectMemoryFocusOwners() {
        Set<Long> out = new LinkedHashSet<Long>();
        collectOwnersForRange(CMD32_MEM_START, CMD32_MEM_END, out);
        collectOwnersForRange(PROCESSED_STATE, PROCESSED_STATE, out);
        collectOwnersForRange(CAN318_START, CAN318_END, out);
        return out;
    }

    private void collectOwnersForRange(long start, long end, Set<Long> out) {
        for (long a = start; a <= end; a++) {
            try {
                ReferenceIterator it = references.getReferencesTo(addr(a));
                while (it.hasNext()) {
                    Reference r = it.next();
                    Function f = functionAt(r.getFromAddress().getOffset());
                    if (f != null) out.add(Long.valueOf(u32(f.getEntryPoint().getOffset())));
                }
            }
            catch (Throwable ignored) {}
        }
    }

    private Set<Long> collectPreDispatchRoots() {
        Set<Long> roots = new LinkedHashSet<Long>();
        roots.add(Long.valueOf(DIAGTASK_ENTRY));
        InstructionIterator it = listing.getInstructions(
            new AddressSet(addr(PRE_DISPATCH_START), addr(PRE_DISPATCH_END)), true);
        while (it.hasNext()) {
            Long target = directCall(it.next());
            if (target != null && inApp(target.longValue()))
                roots.add(target);
        }
        return roots;
    }

    private List<Long> pathFromAny(Set<Long> roots, long target, int depth) {
        List<Long> best = null;
        for (Long r : roots) {
            List<Long> p = findPath(r.longValue(), target, depth);
            if (p != null && (best == null || p.size() < best.size())) best = p;
        }
        return best;
    }

    private List<Long> findPath(long start, long target, int maxDepth) {
        if (start == target) return new ArrayList<Long>(Arrays.asList(Long.valueOf(start)));
        Queue<List<Long>> q = new ArrayDeque<List<Long>>();
        Set<Long> seen = new HashSet<Long>();
        q.add(new ArrayList<Long>(Arrays.asList(Long.valueOf(start))));
        seen.add(Long.valueOf(start));
        while (!q.isEmpty()) {
            List<Long> p = q.remove();
            if (p.size() - 1 >= maxDepth) continue;
            long last = p.get(p.size()-1).longValue();
            Set<Long> next = outgoing.get(Long.valueOf(last));
            if (next == null) continue;
            for (Long n : next) {
                if (n.longValue() == target) {
                    List<Long> hit = new ArrayList<Long>(p);
                    hit.add(n);
                    return hit;
                }
                if (seen.add(n)) {
                    List<Long> np = new ArrayList<Long>(p);
                    np.add(n);
                    q.add(np);
                }
            }
        }
        return null;
    }

    private void writeOutputs(Capture capA, Capture capB) throws Exception {
        writeCsv(file("_source_contract.csv"),
            new String[]{"item","value","note"}, sourceRows);
        writeCsv(file("_gap_episodes.csv"),
            new String[]{"capture","gap_start_record","gap_end_record",
                "gap_start_time","gap_end_time","gap_seconds","startup_record",
                "reset_record","records_since_previous_startup","selection_score"},
            gapRows);
        writeCsv(file("_windows.csv"),
            new String[]{"capture","kind","width","ordinal","start_record","end_record"},
            windowRows);
        writeCsv(file("_pre_gap_signature_ranking.csv"),
            new String[]{"signal_id","value_hex","window","target_presence",
                "control_presence","control_total","control_rate","r4_nearest_distance",
                "r5r1_nearest_distance","score","excluded_prior_family","promoted"},
            rankingRows);
        writeCsv(file("_promoted_signals.csv"),
            new String[]{"rank","signal_id","value_hex","winning_window","score",
                "control_presence","control_total","r4_nearest_distance",
                "r5r1_nearest_distance"}, promotedRows);
        writeCsv(file("_signal_table_maps.csv"),
            new String[]{"record","signal_id","tuple_backing","flags",
                "getter_a","getter_b","classification"}, mapRows);
        writeCsv(file("_getter_recovery.csv"),
            new String[]{"getter","function_entry","function_name","recovered","decomp_length"},
            getterRows);
        writeCsv(file("_actual_getter_sources.csv"),
            new String[]{"signal_id","getter","tuple_backing","source_start","source_end",
                "evidence","tuple_backing_equals_source"}, getterSourceRows);
        writeCsv(file("_actual_source_accesses.csv"),
            new String[]{"signal_id","source_start","source_end","site","owner",
                "owner_name","access","method","instruction"}, accessRows);
        writeCsv(file("_source_can_descriptors.csv"),
            new String[]{"signal_id","source_start","source_end","descriptor","can_id","dlc",
                "primary","secondary","matched_buffer","callback","callback_name"},
            descriptorRows);
        writeCsv(file("_focus_intersections.csv"),
            new String[]{"owner","owner_name","classification","diagtask_body","predispatch_body",
                "predispatch_reachable","command32_related","configcheck_related","ap_owner_related",
                "focus_memory_owner","predispatch_path","owner_to_command32_path",
                "command32_to_owner_path"}, focusRows);
        writeCsv(file("_errors.csv"),
            new String[]{"phase","address","error"}, errorRows);

        writeDecompilation();
        writeSummary(capA, capB);
    }

    private void writeDecompilation() throws Exception {
        BufferedWriter w = writer(file("_selected_decompilation.txt"));
        try {
            for (Map.Entry<Long,String> e : decompilation.entrySet()) {
                long a = e.getKey().longValue();
                w.write("================================================================================\n");
                w.write(hex(a) + " " + functionName(a) + "\n");
                w.write("================================================================================\n");
                w.write(e.getValue() == null ? "" : e.getValue());
                w.write("\n\n");
            }
        }
        finally { w.close(); }
    }

    private void writeSummary(Capture a, Capture b) throws Exception {
        BufferedWriter w = writer(file("_summary.md"));
        try {
            w.write("# Tesla Gateway Software Check Dual Pre-Gap Signal / UDP Ingress Bridge V576\n\n");
            w.write("- Exact stock: `true`\n");
            w.write("- Base cache: `V448R2`\n");
            w.write("- Secondary recovery: `V461R1`\n");
            w.write("- R4 input SHA-256: `" + a.inputSha + "`\n");
            w.write("- R5R1 input SHA-256: `" + b.inputSha + "`\n");
            w.write("- R4 selected member/records: `" + a.memberName + " / " + a.records.size() + "`\n");
            w.write("- R5R1 selected member/records: `" + b.memberName + " / " + b.records.size() + "`\n");
            w.write("- R4 selected gap: `" + String.format(Locale.ROOT,"%.3f",a.target.gapMs/1000.0) + " s`\n");
            w.write("- R5R1 selected gap: `" + String.format(Locale.ROOT,"%.3f",b.target.gapMs/1000.0) + " s`\n");
            w.write("- Promoted dual-pre-gap signal IDs: `" + promoted.size() + "`\n");
            w.write("- Strict logger maps: `" + signalMaps.size() + "`\n");
            w.write("- Actual getter source spans: `" + sourceSpans.size() + "`\n");
            w.write("- Source CAN descriptor rows: `" + descriptorRows.size() + "`\n");
            w.write("- Pre-dispatch related owners: `" + preDispatchOwners.size() + "`\n");
            w.write("- Post/shared focus owners: `" + postFocusOwners.size() + "`\n");
            w.write("- Errors: `" + errorRows.size() + "`\n\n");
            w.write("## Overall classification\n\n`" + classification() + "`\n\n");
            w.write("## Interpretation\n\n");
            w.write("V576 deliberately ranks telemetry immediately before the logging discontinuity in two independent Software-page failures, rather than ranking early-boot records after WDRS. A PRE_DISPATCH result means the strongest repeatable marker can be reached from the established diagTask receive corridor before the computed handler dispatch at 0x788F6 and is therefore a credible earlier timing boundary for a future CAN318 temporal experiment. A post/shared-focus result says the marker is no earlier than the already-tested command32/config-check side. A CAN-descriptor-only result is treated as passive/external runtime context, not proof of an internal trigger.\n\n");
            w.write("## Scope guard\n\n");
            w.write("No comparator, CC1701, AP-trial, D008, NM, broad reset-sink, broad power/rail, or generic SWT search is repeated. D009016F is excluded from promotion because V575 proved its CAN 0x3EE receive provenance. No bench image is generated by V576.\n");
        }
        finally { w.close(); }
    }

    private String classification() {
        if (promoted.isEmpty())
            return "V576_NO_REPEATABLE_PRE_GAP_MARKER";
        if (!preDispatchOwners.isEmpty())
            return "V576_PRE_DISPATCH_INGRESS_BRIDGE";
        if (sourceSpans.isEmpty())
            return "V576_REPEATABLE_PRE_GAP_MARKERS_STATIC_SOURCE_UNRESOLVED";

        boolean allPassive = true;
        for (Promoted p : promoted) {
            if (!passiveSignalIds.contains(Long.valueOf(p.id))) {
                allPassive = false;
                break;
            }
        }
        if (allPassive || !postFocusOwners.isEmpty())
            return "V576_ONLY_POST_COMMAND32_OR_PASSIVE_MARKERS";
        return "V576_INDEPENDENT_PRE_GAP_MARKER";
    }

    private void zipOutputs() throws Exception {
        File zip = file("_bundle.zip");
        File[] files = outDir.listFiles();
        if (files == null) return;
        Arrays.sort(files, new Comparator<File>() {
            @Override public int compare(File a, File b) {
                return a.getName().compareTo(b.getName());
            }
        });
        ZipOutputStream out = new ZipOutputStream(new FileOutputStream(zip));
        try {
            byte[] buf = new byte[16384];
            for (File f : files) {
                if (!f.isFile() || !f.getName().startsWith(runStem) || f.equals(zip)) continue;
                out.putNextEntry(new ZipEntry(f.getName()));
                InputStream in = new BufferedInputStream(new FileInputStream(f));
                try {
                    int n;
                    while ((n = in.read(buf)) > 0) out.write(buf,0,n);
                }
                finally { in.close(); }
                out.closeEntry();
            }
        }
        finally { out.close(); }
    }

    private boolean looksZip(byte[] b) {
        return b != null && b.length >= 4 && b[0] == 'P' && b[1] == 'K';
    }

    private boolean containsSpan(long base, int len, long start, long end) {
        if (len <= 0) return false;
        long last = base + len - 1L;
        return start >= base && end <= last;
    }

    private boolean bodyOverlaps(Function f, long start, long end) {
        if (f == null || f.getBody() == null) return false;
        long a = u32(f.getBody().getMinAddress().getOffset());
        long b = u32(f.getBody().getMaxAddress().getOffset());
        return overlaps(a,b,start,end);
    }

    private boolean overlaps(long a0,long a1,long b0,long b1) {
        return Long.compareUnsigned(a0,b1) <= 0 && Long.compareUnsigned(b0,a1) <= 0;
    }

    private void addEdge(long from, long to) {
        Long f = Long.valueOf(from), t = Long.valueOf(to);
        Set<Long> set = outgoing.get(f);
        if (set == null) {
            set = new LinkedHashSet<Long>();
            outgoing.put(f,set);
        }
        set.add(t);
    }

    private Long directCall(Instruction i) {
        if (i == null || i.getFlowType() == null ||
            !i.getFlowType().isCall() || i.getFlowType().isComputed()) return null;
        Address[] flow = i.getFlows();
        if (flow == null || flow.length != 1 || flow[0] == null) return null;
        return Long.valueOf(u32(flow[0].getOffset()));
    }

    private boolean isMemoryMnemonic(String m) {
        String x = lower(m);
        return x.startsWith("lw") || x.startsWith("lb") || x.startsWith("lh") ||
            x.startsWith("st") || x.startsWith("e_lw") || x.startsWith("e_lb") ||
            x.startsWith("e_lh") || x.startsWith("e_st") || x.startsWith("se_lw") ||
            x.startsWith("se_lb") || x.startsWith("se_lh") || x.startsWith("se_st");
    }

    private boolean isStore(Instruction i) {
        return i != null && isStoreMnemonic(i.getMnemonicString());
    }

    private boolean isStoreMnemonic(String m) {
        String x = lower(m);
        return x.startsWith("st") || x.startsWith("e_st") || x.startsWith("se_st");
    }

    private int memoryWidth(String mnemonic) {
        String m = lower(mnemonic);
        if (m.contains("lbz") || m.contains("stb")) return 1;
        if (m.contains("lhz") || m.contains("lha") || m.contains("sth")) return 2;
        if (m.contains("ld") || m.contains("std")) return 8;
        return 4;
    }

    private String firstRegister(Instruction i) {
        try {
            if (i.getNumOperands() < 1) return "";
            Object[] objects = i.getOpObjects(0);
            if (objects != null) {
                for (Object o : objects)
                    if (o instanceof Register)
                        return ((Register)o).getName().toLowerCase(Locale.ROOT);
            }
        }
        catch (Throwable ignored) {}
        return "";
    }

    private boolean writesFirstRegister(Instruction i) {
        String m = lower(i.getMnemonicString());
        if (m.startsWith("st") || m.startsWith("e_st") || m.startsWith("se_st") ||
            m.contains("cmp") || m.contains("btst") || m.startsWith("b") ||
            m.startsWith("e_b") || m.startsWith("se_b")) return false;
        return firstRegister(i).length() > 0;
    }

    private Function functionAt(long a) {
        Function f = functions.getFunctionContaining(addr(a));
        if (f == null) f = functions.getFunctionAt(addr(a));
        return f;
    }

    private String functionName(long a) {
        Function f = functionAt(a);
        return f == null ? "" : f.getName();
    }

    private boolean isCodePtr(long v) {
        long n = normalizeCode(v);
        return inApp(n);
    }

    private long normalizeCode(long v) {
        return u32(v) & 0xfffffffeL;
    }

    private boolean inApp(long a) {
        long v = u32(a);
        return Long.compareUnsigned(v,APP_START) >= 0 &&
            Long.compareUnsigned(v,APP_END) <= 0;
    }

    private boolean inRam(long a) {
        long v = u32(a);
        return Long.compareUnsigned(v,RAM_START) >= 0 &&
            Long.compareUnsigned(v,RAM_END) <= 0;
    }

    private long readU32(long a) throws Exception {
        byte[] b = new byte[4];
        int got = memory.getBytes(addr(a), b);
        if (got != 4) throw new IllegalStateException("Short read at " + hex(a));
        return u32be(b,0);
    }

    private long u32be(byte[] b, int o) {
        return (((long)b[o] & 0xffL) << 24) |
               (((long)b[o+1] & 0xffL) << 16) |
               (((long)b[o+2] & 0xffL) << 8) |
               ((long)b[o+3] & 0xffL);
    }

    private long parseUnsignedToken(String s) {
        String x = s.trim().toLowerCase(Locale.ROOT);
        boolean neg = x.startsWith("-");
        if (neg) x = x.substring(1);
        int radix = 10;
        if (x.startsWith("0x")) { radix = 16; x = x.substring(2); }
        else if (x.matches(".*[a-f].*")) radix = 16;
        long v = Long.parseLong(x,radix);
        return neg ? -v : v;
    }

    private long parseSignedToken(String s) {
        String original = s.trim().toLowerCase(Locale.ROOT);
        boolean explicitNegative = original.startsWith("-");
        long v = parseUnsignedToken(original);
        if (explicitNegative) return v;
        if (v >= 0 && v <= 0xffffL && (v & 0x8000L) != 0)
            return v - 0x10000L;
        return v;
    }

    private byte[] readFile(File f) throws Exception {
        InputStream in = new BufferedInputStream(new FileInputStream(f));
        try { return readAll(in); }
        finally { in.close(); }
    }

    private byte[] readAll(InputStream in) throws Exception {
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        byte[] buf = new byte[16384];
        int n;
        while ((n = in.read(buf)) > 0) out.write(buf,0,n);
        return out.toByteArray();
    }

    private byte[] slice(byte[] b,int off,int len) {
        byte[] out = new byte[len];
        System.arraycopy(b,off,out,0,len);
        return out;
    }

    private String bytesHex(byte[] b) {
        if (b == null || b.length == 0) return "";
        StringBuilder s = new StringBuilder();
        for (byte x : b) s.append(String.format(Locale.ROOT,"%02X",x & 0xff));
        return s.toString();
    }

    private String sha256(byte[] b) throws Exception {
        MessageDigest d = MessageDigest.getInstance("SHA-256");
        d.update(b);
        return digestHex(d.digest());
    }

    private String sha256Program() throws Exception {
        MessageDigest d = MessageDigest.getInstance("SHA-256");
        for (long p = IMAGE_START; p <= IMAGE_END; ) {
            int n = (int)Math.min(0x4000L, IMAGE_END - p + 1L);
            byte[] b = new byte[n];
            int got = memory.getBytes(addr(p), b);
            if (got != n) throw new IllegalStateException("Short program read at " + hex(p));
            d.update(b);
            p += n;
        }
        return digestHex(d.digest());
    }

    private String digestHex(byte[] d) {
        StringBuilder s = new StringBuilder();
        for (byte x : d) s.append(String.format(Locale.ROOT,"%02x",x & 0xff));
        return s.toString();
    }

    private Address addr(long v) { return toAddr(u32(v)); }
    private long u32(long v) { return v & 0xffffffffL; }
    private String hex(long v) { return String.format(Locale.ROOT,"0x%08X",u32(v)); }
    private String hexBare(long v) { return String.format(Locale.ROOT,"%08X",u32(v)); }
    private String lower(String s) { return s == null ? "" : s.trim().toLowerCase(Locale.ROOT); }
    private String clean(String s) {
        return s == null ? "" : s.replace('\r',' ').replace('\n',' ').replace('\t',' ')
            .replaceAll("\\s+"," ").trim();
    }

    private String pathText(List<Long> path) {
        if (path == null || path.isEmpty()) return "";
        List<String> parts = new ArrayList<String>();
        for (Long v : path) parts.add(hex(v.longValue()) + ":" + functionName(v.longValue()));
        return join(parts," -> ");
    }

    private String join(List<String> values,String sep) {
        StringBuilder s = new StringBuilder();
        for (String v : values) {
            if (s.length() > 0) s.append(sep);
            s.append(v);
        }
        return s.toString();
    }

    private String formatTime(long ms) {
        if (ms <= 0) return "";
        SimpleDateFormat f = new SimpleDateFormat("yyyy-MM-dd HH:mm:ss.SSS",Locale.ROOT);
        f.setTimeZone(TimeZone.getTimeZone("Europe/London"));
        return f.format(new Date(ms));
    }

    private String timestamp() {
        SimpleDateFormat f = new SimpleDateFormat("yyyyMMdd_HHmmss",Locale.ROOT);
        f.setTimeZone(TimeZone.getTimeZone("UTC"));
        return f.format(new Date());
    }

    private void addError(String phase,long address,String error) {
        errorRows.add(new String[]{phase,address < 0 ? "" : hex(address),clean(error)});
    }

    private File file(String suffix) { return new File(outDir, runStem + suffix); }

    private BufferedWriter writer(File f) throws Exception {
        return new BufferedWriter(new OutputStreamWriter(
            new FileOutputStream(f), StandardCharsets.UTF_8));
    }

    private void writeCsv(File f,String[] headers,List<String[]> rows) throws Exception {
        BufferedWriter w = writer(f);
        try {
            for (int i=0;i<headers.length;i++) {
                if (i>0) w.write(',');
                w.write(csv(headers[i]));
            }
            w.write("\n");
            for (String[] row : rows) {
                for (int i=0;i<headers.length;i++) {
                    if (i>0) w.write(',');
                    w.write(csv(i < row.length ? row[i] : ""));
                }
                w.write("\n");
            }
        }
        finally { w.close(); }
    }

    private String csv(String s) {
        if (s == null) s = "";
        return "\"" + s.replace("\"","\"\"") + "\"";
    }
}
