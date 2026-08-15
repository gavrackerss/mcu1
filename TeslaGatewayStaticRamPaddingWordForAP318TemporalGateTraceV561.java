// TeslaGatewayStaticRamPaddingWordForAP318TemporalGateTraceV561.java
//
// Read-only follow-up after V560.
//
// V560 found no existing non-output RAM state shared between the command-0x32
// closure and the AP publication owner. Earlier V383/V386 work also means that
// neither the low-SRAM candidate nor the mapped high-SRAM task-stack pool may be
// silently promoted to patch scratch state.
//
// V561 therefore asks a different, bounded question: is there an aligned 32-bit
// hole inside a tightly bracketed, statically-addressed RAM object/field cluster
// which has no stock direct access, no raw pointer, no exact materialisation, no
// nearby indexed-alias evidence and no pointer+length call range covering it?
//
// A positive row is still a candidate, not a firmware patch. It is intended to
// select one exact word for a later target-local lifetime/bulk-owner closure pass.
// No BIN/S19 is generated here.
//
// No decompiler, no High P-code, no firmware modification and no persistent
// Ghidra database modification. Output directory need not be empty.
//
// @category TeslaGateway.Analysis
// @menupath Tools.Tesla.Trace Static RAM Padding Word for AP318 Temporal Gate V561

import ghidra.app.script.GhidraScript;
import ghidra.program.model.address.Address;
import ghidra.program.model.listing.Function;
import ghidra.program.model.listing.FunctionIterator;
import ghidra.program.model.listing.FunctionManager;
import ghidra.program.model.listing.Instruction;
import ghidra.program.model.listing.InstructionIterator;
import ghidra.program.model.listing.Listing;
import ghidra.program.model.mem.Memory;
import ghidra.program.model.symbol.Reference;
import ghidra.program.model.symbol.ReferenceIterator;
import ghidra.program.model.symbol.ReferenceManager;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.InputStream;
import java.io.OutputStreamWriter;
import java.nio.charset.StandardCharsets;
import java.security.MessageDigest;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.zip.ZipEntry;
import java.util.zip.ZipOutputStream;

public class TeslaGatewayStaticRamPaddingWordForAP318TemporalGateTraceV561 extends GhidraScript {
    private static final String PREFIX =
        "TeslaGatewayStaticRamPaddingWordForAP318TemporalGateTraceV561";

    private static final String EXPECTED_LANGUAGE = "PowerPC:BE:64:VLE-32addr";
    private static final String EXPECTED_SHA256 =
        "889ab36ae6d17bb897587df85db6201f32cb33f01ba101962979f765ef0ee3fe";

    private static final long IMAGE_START = 0x00000000L;
    private static final long IMAGE_END   = 0x001FFFFFL;
    private static final long APP_START   = 0x00020000L;
    private static final long APP_END     = 0x00149299L;

    // V383/V386 boundary: this pass searches the ordinary statically-addressed
    // RAM envelope below the proven dynamic task-stack pool only.
    private static final long RAM_START = 0x40000000L;
    private static final long RAM_STATIC_END = 0x4006BFFFL;
    private static final long TASK_STACK_START = 0x4006C000L;
    private static final long TASK_STACK_END   = 0x40093FFFL;

    private static final int MAX_GAP_BYTES = 0x10;
    private static final int CLUSTER_JOIN_GAP = 0x20;
    private static final int LOCAL_WINDOW = 0x20;
    private static final int INDEX_ALIAS_RADIUS = 0x100;
    private static final long MAX_POINTER_LENGTH = 0x20000L;

    private static final Pattern MEM = Pattern.compile(
        "^\\s*([a-zA-Z0-9_\\.]+)\\s+(r[0-9]+)\\s*,\\s*([^\\s,(]+)\\s*\\((r[0-9]+)\\).*$");
    private static final Pattern LIS = Pattern.compile(
        "^(?:e_|se_)?lis\\s+(r[0-9]+)\\s*,\\s*([^,\\s]+).*$", Pattern.CASE_INSENSITIVE);
    private static final Pattern LI = Pattern.compile(
        "^(?:e_|se_)?li\\s+(r[0-9]+)\\s*,\\s*([^,\\s]+).*$", Pattern.CASE_INSENSITIVE);
    private static final Pattern ADDI = Pattern.compile(
        "^(?:e_|se_)?(?:add16i|addi)\\s+(r[0-9]+)\\s*,\\s*(r[0-9]+)\\s*,\\s*([^,\\s]+).*$",
        Pattern.CASE_INSENSITIVE);
    private static final Pattern ORI = Pattern.compile(
        "^(?:e_|se_)?ori\\s+(r[0-9]+)\\s*,\\s*(r[0-9]+)\\s*,\\s*([^,\\s]+).*$",
        Pattern.CASE_INSENSITIVE);
    private static final Pattern OR2I = Pattern.compile(
        "^(?:e_|se_)?or2i\\s+(r[0-9]+)\\s*,\\s*([^,\\s]+).*$", Pattern.CASE_INSENSITIVE);
    private static final Pattern MR = Pattern.compile(
        "^(?:e_|se_)?mr\\s+(r[0-9]+)\\s*,\\s*(r[0-9]+).*$", Pattern.CASE_INSENSITIVE);
    private static final Pattern INDEXED = Pattern.compile(
        "^\\s*([a-zA-Z0-9_\\.]*?(?:lbzx|lhzx|lhax|lwzx|ldx|stbx|sthx|stwx|stdx))\\s+" +
        "(r[0-9]+)\\s*,\\s*(r[0-9]+)\\s*,\\s*(r[0-9]+).*$", Pattern.CASE_INSENSITIVE);

    private Listing listing;
    private Memory memory;
    private FunctionManager functions;
    private ReferenceManager refs;
    private File outDir;
    private byte[] image;
    private String sha;

    private final List<Access> accesses = new ArrayList<Access>();
    private final List<IndexedRisk> indexedRisks = new ArrayList<IndexedRisk>();
    private final List<CallRange> callRanges = new ArrayList<CallRange>();
    private final List<Coverage> coverage = new ArrayList<Coverage>();
    private final List<Cluster> clusters = new ArrayList<Cluster>();
    private final List<Candidate> candidates = new ArrayList<Candidate>();
    private final Map<Long,Integer> materialisations = new HashMap<Long,Integer>();
    private final List<String[]> sourceRows = new ArrayList<String[]>();
    private final List<String[]> exclusionRows = new ArrayList<String[]>();
    private final List<String[]> assessmentRows = new ArrayList<String[]>();
    private final List<String[]> patchRows = new ArrayList<String[]>();
    private final List<String[]> errorRows = new ArrayList<String[]>();
    private final Set<String> accessDedup = new HashSet<String>();

    private static class Range {
        long start, end; String label, reason;
        Range(long s,long e,String l,String r){start=s;end=e;label=l;reason=r;}
        boolean overlaps(long s,long e){return s<=end && e>=start;}
    }

    private static final Range[] EXCLUDED = new Range[] {
        new Range(0x40000000L,0x40003FFFL,"LOW_SRAM_UNPROVEN_LIFETIME",
            "V383 proved addressability, not runtime lifetime/overwrite safety"),
        new Range(0x40013080L,0x400131A0L,"QUEUE_ACTION_CONTROL",
            "event/queue handles and post-check action/synchronisation block"),
        new Range(0x400149C0L,0x400149C3L,"HANDSHAKE_FLAGS",
            "known timed-handshake flags"),
        new Range(0x40016840L,0x40016847L,"CAN359_COMMAND32_STATE",
            "known command32/CAN359 state"),
        new Range(0x40019F80L,0x40019FA7L,"HANDSHAKE_TIMERS",
            "known timed-handshake timer words"),
        new Range(0x4001A200L,0x4001A23FL,"DESCRIPTOR_RUNTIME_STATE",
            "active descriptor table/timestamp bookkeeping"),
        new Range(0x40046F00L,0x40046FFFL,"CONFIG_RUNTIME_BYTES",
            "dense configuration/runtime status byte block"),
        new Range(0x40047CA8L,0x40047CAFL,"CAN318_PAYLOAD",
            "CAN 0x318 payload including AP field"),
        new Range(0x40049DA0L,0x40049DA7L,"CAN398_PAYLOAD",
            "CAN 0x398 payload including AP field"),
        new Range(0x4004A2B8L,0x4004A2BFL,"VEHICLE_PACKED_STATE",
            "known config-check input/output surface"),
        new Range(0x4004AA18L,0x4004AA3FL,"CAN42E_CAN368_PAYLOADS",
            "known AP/handshake and CAN 0x368 payload surfaces"),
        new Range(0x4004AC60L,0x4004AE3FL,"NM_OBJECT_FAMILY",
            "known 0x48-stride NM timer/object family"),
        new Range(0x4004BC1CL,0x4004BCD0L,"SOFTWARE_TIMER_TABLE",
            "known 15-slot software timer table"),
        new Range(TASK_STACK_START,TASK_STACK_END,"DYNAMIC_TASK_STACK_POOL",
            "V386-proven sequential task-stack pool")
    };

    private static class Access {
        long start,end,owner,site; int width; String kind,instruction,evidence;
        Access(long s,int w,long o,long p,String k,String i,String e){
            start=s; width=w; end=s+w-1L; owner=o; site=p; kind=k; instruction=i; evidence=e;
        }
    }
    private static class Coverage {
        long start,end; List<Access> members=new ArrayList<Access>();
        Coverage(long s,long e){start=s;end=e;}
    }
    private static class Cluster {
        long start,end; int accesses,writes,owners;
    }
    private static class IndexedRisk {
        long base,owner,site; String instruction;
        IndexedRisk(long b,long o,long s,String i){base=b;owner=o;site=s;instruction=i;}
    }
    private static class CallRange {
        long start,end,caller,site,length; String form,instruction;
        CallRange(long s,long len,long c,long p,String f,String i){
            start=s; length=len; end=s+len-1L; caller=c; site=p; form=f; instruction=i;
        }
        boolean covers(long p){return p>=start && p<=end;}
    }
    private static class Candidate {
        long address,gapStart,gapEnd; int gapBytes;
        Access left,right; Cluster cluster;
        int nearAccesses,nearWrites,nearOwners;
        int exactRefs,rawPointers,materialised,indexedRiskCount,callRangeRiskCount;
        int score; String classification,exclusion;
    }

    @Override
    protected void run() throws Exception {
        if (currentProgram == null) throw new IllegalStateException("No Ghidra program is open.");
        listing = currentProgram.getListing();
        memory = currentProgram.getMemory();
        functions = currentProgram.getFunctionManager();
        refs = currentProgram.getReferenceManager();

        validateSource();
        outDir = askDirectory("Select V561 output folder (need not be empty)", "Select");
        if (outDir == null) return;
        if (!outDir.exists() && !outDir.mkdirs())
            throw new IllegalStateException("Could not create output folder.");

        buildExclusionRows();
        scanRamAccessesAndAliases();
        buildCoverage();
        buildClusters();
        buildCandidates();
        auditCandidates();
        buildAssessment();
        writeOutputs();
        zipOutputs();

        println(PREFIX + " complete.");
        println("Resolved static-RAM accesses: " + accesses.size());
        println("Coverage intervals: " + coverage.size());
        println("Tight clusters: " + clusters.size());
        println("Padding-word candidates: " + candidates.size());
        println("Errors: " + errorRows.size());
    }

    private void validateSource() throws Exception {
        String language = currentProgram.getLanguageID().toString();
        if (!EXPECTED_LANGUAGE.equals(language))
            throw new IllegalStateException("Expected " + EXPECTED_LANGUAGE + " but found " + language);
        image = new byte[(int)(IMAGE_END-IMAGE_START+1L)];
        int got = memory.getBytes(addr(IMAGE_START), image);
        if (got != image.length) throw new IllegalStateException("Short initialized-image read: " + got + "/" + image.length);
        sha = sha256(image);
        if (!EXPECTED_SHA256.equalsIgnoreCase(sha))
            throw new IllegalStateException("Unexpected initialized-memory SHA-256. Expected " + EXPECTED_SHA256 + " found " + sha);
        sourceRows.add(row("language",language,"true"));
        sourceRows.add(row("initialized_sha256",sha,"true"));
        sourceRows.add(row("decompiler_invoked","NO","true"));
        sourceRows.add(row("high_pcode_invoked","NO","true"));
        sourceRows.add(row("firmware_modified","NO","true"));
        sourceRows.add(row("ghidra_database_modified","NO","true"));
        sourceRows.add(row("search_ram_envelope",hex(RAM_START)+".."+hex(RAM_STATIC_END),"true"));
        sourceRows.add(row("v386_dynamic_stack_pool",hex(TASK_STACK_START)+".."+hex(TASK_STACK_END),"excluded"));
    }

    private void buildExclusionRows() {
        for (Range r : EXCLUDED)
            exclusionRows.add(new String[]{r.label,hex(r.start),hex(r.end),r.reason});
    }

    private void scanRamAccessesAndAliases() {
        FunctionIterator fi = functions.getFunctions(true);
        int fn = 0;
        while (fi.hasNext() && !monitor.isCancelled()) {
            Function f = fi.next();
            long owner = u32(f.getEntryPoint().getOffset());
            if (owner < APP_START || owner > APP_END) continue;
            fn++;
            if ((fn & 0x3f) == 0) monitor.setMessage("V561 RAM access scan: function " + fn);
            try { scanFunction(f); }
            catch (Throwable t) { addError("scan_function",owner,t); }
        }
    }

    private void scanFunction(Function f) {
        long owner = u32(f.getEntryPoint().getOffset());
        Map<String,Long> regs = new HashMap<String,Long>();
        InstructionIterator it = listing.getInstructions(f.getBody(), true);
        while (it.hasNext() && !monitor.isCancelled()) {
            Instruction ins = it.next();
            long site = u32(ins.getAddress().getOffset());
            String text = norm(ins.toString());
            String mnemonic = stripPrefix(ins.getMnemonicString());

            // Existing Ghidra references are the strongest direct evidence.
            try {
                for (Reference r : ins.getReferencesFrom()) {
                    long target = u32(r.getToAddress().getOffset());
                    if (!inStaticRam(target)) continue;
                    int width = memoryWidth(mnemonic);
                    String kind = isStoreMnemonic(mnemonic) ? "WRITE" : (isLoadMnemonic(mnemonic) ? "READ" : "REFERENCE");
                    addAccess(target,width,owner,site,kind,ins.toString(),"GHIDRA_REFERENCE");
                }
            } catch (Throwable t) { addError("instruction_references",site,t); }

            Matcher mm = MEM.matcher(text);
            if (mm.matches()) {
                String op = stripPrefix(mm.group(1));
                String valueReg = mm.group(2).toLowerCase(Locale.ROOT);
                Long disp = parseImm(mm.group(3));
                String baseReg = mm.group(4).toLowerCase(Locale.ROOT);
                Long base = regs.get(baseReg);
                if (disp != null && base != null) {
                    long target = u32(base.longValue() + signExtend16(disp.longValue()));
                    if (inStaticRam(target)) {
                        addAccess(target,memoryWidth(op),owner,site,
                            isStoreMnemonic(op)?"WRITE":(isLoadMnemonic(op)?"READ":"MEMORY"),
                            ins.toString(),"RESOLVED_BASE_PLUS_DISP");
                    }
                }
                if (isLoadMnemonic(op)) regs.remove(valueReg);
            }

            Matcher ix = INDEXED.matcher(text);
            if (ix.matches()) {
                String ra = ix.group(3).toLowerCase(Locale.ROOT);
                String rb = ix.group(4).toLowerCase(Locale.ROOT);
                Long a = regs.get(ra), b = regs.get(rb);
                if (a != null && inStaticRam(a.longValue()))
                    indexedRisks.add(new IndexedRisk(u32(a.longValue()),owner,site,ins.toString()));
                if (b != null && inStaticRam(b.longValue()))
                    indexedRisks.add(new IndexedRisk(u32(b.longValue()),owner,site,ins.toString()));
                // Exact indexed address if both operands are known.
                if (a != null && b != null) {
                    long target=u32(a.longValue()+b.longValue());
                    if (inStaticRam(target)) {
                        String op=stripPrefix(ix.group(1));
                        addAccess(target,memoryWidth(op),owner,site,
                            isStoreMnemonic(op)?"WRITE":"READ",ins.toString(),"RESOLVED_INDEXED_EXACT");
                    }
                }
                if (isLoadMnemonic(stripPrefix(ix.group(1)))) regs.remove(ix.group(2).toLowerCase(Locale.ROOT));
            }

            if (ins.getFlowType()!=null && ins.getFlowType().isCall()) {
                capturePointerLengthRanges(regs,owner,site,ins.toString());
                clearVolatile(regs);
                continue;
            }

            updateState(text,regs,site);

            if (ins.getFlowType()!=null &&
                (ins.getFlowType().isJump() || ins.getFlowType().isTerminal())) {
                // Block-local discipline: never carry guessed constants through branches.
                regs.clear();
            }
        }
    }

    private void capturePointerLengthRanges(Map<String,Long> regs,long owner,long site,String instruction) {
        Long r3=regs.get("r3"), r4=regs.get("r4"), r5=regs.get("r5");
        if (r3!=null && inStaticRam(r3.longValue())) {
            if (plausibleLength(r5)) addCallRange(r3.longValue(),r5.longValue(),owner,site,"r3_pointer_r5_length",instruction);
            if (plausibleLength(r4)) addCallRange(r3.longValue(),r4.longValue(),owner,site,"r3_pointer_r4_length",instruction);
        }
        if (r4!=null && inStaticRam(r4.longValue()) && plausibleLength(r5))
            addCallRange(r4.longValue(),r5.longValue(),owner,site,"r4_pointer_r5_length",instruction);
    }

    private boolean plausibleLength(Long x) {
        if (x==null) return false;
        long v=u32(x.longValue());
        return v>=8 && v<=MAX_POINTER_LENGTH;
    }

    private void addCallRange(long start,long len,long owner,long site,String form,String instruction) {
        start=u32(start); len=u32(len);
        if (!inStaticRam(start) || len==0 || start+len-1L>RAM_STATIC_END) return;
        callRanges.add(new CallRange(start,len,owner,site,form,instruction));
    }

    private void updateState(String text,Map<String,Long> regs,long site) {
        Matcher m=LIS.matcher(text);
        if (m.matches()) {
            Long imm=parseImm(m.group(2));
            if (imm==null) regs.remove(m.group(1).toLowerCase(Locale.ROOT));
            else setReg(regs,m.group(1),u32((imm.longValue()&0xffffL)<<16),site);
            return;
        }
        m=LI.matcher(text);
        if (m.matches()) {
            Long imm=parseImm(m.group(2));
            if (imm==null) regs.remove(m.group(1).toLowerCase(Locale.ROOT));
            else setReg(regs,m.group(1),u32(signExtend16(imm.longValue())),site);
            return;
        }
        m=ADDI.matcher(text);
        if (m.matches()) {
            String d=m.group(1).toLowerCase(Locale.ROOT), s=m.group(2).toLowerCase(Locale.ROOT);
            Long base=regs.get(s), imm=parseImm(m.group(3));
            if (base!=null && imm!=null) setReg(regs,d,u32(base.longValue()+signExtend16(imm.longValue())),site);
            else regs.remove(d);
            return;
        }
        m=ORI.matcher(text);
        if (m.matches()) {
            String d=m.group(1).toLowerCase(Locale.ROOT), s=m.group(2).toLowerCase(Locale.ROOT);
            Long base=regs.get(s), imm=parseImm(m.group(3));
            if (base!=null && imm!=null) setReg(regs,d,u32(base.longValue()|(imm.longValue()&0xffffL)),site);
            else regs.remove(d);
            return;
        }
        m=OR2I.matcher(text);
        if (m.matches()) {
            String d=m.group(1).toLowerCase(Locale.ROOT); Long base=regs.get(d), imm=parseImm(m.group(2));
            if (base!=null && imm!=null) setReg(regs,d,u32(base.longValue()|(imm.longValue()&0xffffL)),site);
            else regs.remove(d);
            return;
        }
        m=MR.matcher(text);
        if (m.matches()) {
            String d=m.group(1).toLowerCase(Locale.ROOT), s=m.group(2).toLowerCase(Locale.ROOT);
            Long v=regs.get(s); if (v==null) regs.remove(d); else setReg(regs,d,v.longValue(),site);
            return;
        }

        // Conservative destination-register kill for common arithmetic/loads not modelled above.
        String[] parts=text.split("[\\s,]+",3);
        if (parts.length>=2 && parts[1].matches("r[0-9]+")) {
            String op=stripPrefix(parts[0]);
            if (isLoadMnemonic(op) || op.startsWith("add") || op.startsWith("sub") ||
                op.startsWith("and") || op.startsWith("xor") || op.startsWith("rlw") ||
                op.startsWith("rot") || op.startsWith("ext")) regs.remove(parts[1]);
        }
    }

    private void setReg(Map<String,Long> regs,String reg,long value,long site) {
        String r=reg.toLowerCase(Locale.ROOT); long v=u32(value); regs.put(r,Long.valueOf(v));
        if (inStaticRam(v)) {
            Integer n=materialisations.get(Long.valueOf(v));
            materialisations.put(Long.valueOf(v),Integer.valueOf(n==null?1:n.intValue()+1));
        }
    }

    private void clearVolatile(Map<String,Long> regs) {
        for (int i=0;i<=12;i++) regs.remove("r"+i);
    }

    private void addAccess(long target,int width,long owner,long site,String kind,String instruction,String evidence) {
        target=u32(target); if (width<=0) width=4;
        long end=target+width-1L;
        if (target<RAM_START || end>RAM_STATIC_END) return;
        String key=hex(site)+":"+hex(target)+":"+width+":"+kind;
        if (!accessDedup.add(key)) return;
        accesses.add(new Access(target,width,owner,site,kind,instruction,evidence));
    }

    private void buildCoverage() {
        List<Access> sorted=new ArrayList<Access>(accesses);
        Collections.sort(sorted,new Comparator<Access>(){
            public int compare(Access a,Access b){int c=Long.compare(a.start,b.start);return c!=0?c:Long.compare(a.end,b.end);} });
        Coverage cur=null;
        for (Access a:sorted) {
            if (cur==null || a.start>cur.end+1L) {
                cur=new Coverage(a.start,a.end); coverage.add(cur);
            } else if (a.end>cur.end) cur.end=a.end;
            cur.members.add(a);
        }
    }

    private void buildClusters() {
        Cluster cur=null; Set<Long> owners=new LinkedHashSet<Long>();
        for (Coverage c:coverage) {
            if (cur==null || c.start>cur.end+CLUSTER_JOIN_GAP) {
                if (cur!=null) {cur.owners=owners.size(); clusters.add(cur);} 
                cur=new Cluster(); cur.start=c.start; cur.end=c.end; owners=new LinkedHashSet<Long>();
            } else if (c.end>cur.end) cur.end=c.end;
            for (Access a:c.members) {cur.accesses++; if ("WRITE".equals(a.kind)) cur.writes++; owners.add(Long.valueOf(a.owner));}
        }
        if (cur!=null) {cur.owners=owners.size(); clusters.add(cur);}
    }

    private void buildCandidates() {
        for (int i=0;i+1<coverage.size();i++) {
            Coverage left=coverage.get(i), right=coverage.get(i+1);
            long gs=left.end+1L, ge=right.start-1L;
            if (ge<gs) continue;
            int gap=(int)(ge-gs+1L);
            if (gap<4 || gap>MAX_GAP_BYTES) continue;
            Cluster cluster=clusterContaining(left.start,right.end);
            if (cluster==null || cluster.accesses<3) continue;
            for (long p=(gs+3L)&~3L;p+3L<=ge;p+=4L) {
                Candidate c=new Candidate();
                c.address=p; c.gapStart=gs; c.gapEnd=ge; c.gapBytes=gap;
                c.left=nearestAccess(left,true); c.right=nearestAccess(right,false); c.cluster=cluster;
                Range ex=exclusionFor(p,p+3L); c.exclusion=ex==null?"":ex.label;
                if (ex!=null) continue;
                fillNearCounts(c);
                if (c.nearAccesses<3) continue;
                candidates.add(c);
            }
        }
    }

    private Cluster clusterContaining(long start,long end) {
        for (Cluster c:clusters) if (start>=c.start && end<=c.end) return c;
        return null;
    }

    private Access nearestAccess(Coverage c,boolean rightEdge) {
        Access best=null;
        for (Access a:c.members) {
            if (best==null) best=a;
            else if (rightEdge && a.end>best.end) best=a;
            else if (!rightEdge && a.start<best.start) best=a;
        }
        return best;
    }

    private void fillNearCounts(Candidate c) {
        Set<Long> owners=new LinkedHashSet<Long>();
        long lo=c.address-LOCAL_WINDOW, hi=c.address+3L+LOCAL_WINDOW;
        for (Access a:accesses) {
            if (a.end<lo || a.start>hi) continue;
            c.nearAccesses++; if ("WRITE".equals(a.kind)) c.nearWrites++; owners.add(Long.valueOf(a.owner));
        }
        c.nearOwners=owners.size();
    }

    private void auditCandidates() {
        if (candidates.isEmpty()) return;
        Map<Long,Candidate> byAddr=new LinkedHashMap<Long,Candidate>();
        for (Candidate c:candidates) byAddr.put(Long.valueOf(c.address),c);

        // Sliding raw-pointer scan over initialized flash, once for every candidate.
        for (int i=0;i+3<image.length;i++) {
            long v=((long)(image[i]&0xff)<<24)|((long)(image[i+1]&0xff)<<16)|
                   ((long)(image[i+2]&0xff)<<8)|((long)(image[i+3]&0xff));
            Candidate c=byAddr.get(Long.valueOf(v&0xffffffffL));
            if (c!=null) c.rawPointers++;
        }

        for (Candidate c:candidates) {
            try {
                ReferenceIterator ri=refs.getReferencesTo(addr(c.address));
                while (ri.hasNext()) {ri.next(); c.exactRefs++;}
            } catch (Throwable t) { addError("candidate_xrefs",c.address,t); }
            Integer m=materialisations.get(Long.valueOf(c.address)); c.materialised=m==null?0:m.intValue();
            for (IndexedRisk r:indexedRisks)
                if (Math.abs((long)c.address-(long)r.base)<=INDEX_ALIAS_RADIUS) c.indexedRiskCount++;
            for (CallRange r:callRanges) if (r.covers(c.address) || r.covers(c.address+3L)) c.callRangeRiskCount++;
            classifyCandidate(c);
        }
        Collections.sort(candidates,new Comparator<Candidate>(){
            public int compare(Candidate a,Candidate b){int c=Integer.compare(b.score,a.score);return c!=0?c:Long.compare(a.address,b.address);} });
    }

    private void classifyCandidate(Candidate c) {
        int s=50;
        if (c.gapBytes==4) s+=30; else if (c.gapBytes<=8) s+=15;
        if (c.left!=null && c.right!=null && c.left.owner==c.right.owner) s+=10;
        if (c.nearWrites>0) s+=10;
        s+=Math.min(20,c.nearAccesses*2);
        if (c.exactRefs>0) s-=60;
        if (c.rawPointers>0) s-=60;
        if (c.materialised>0) s-=50;
        if (c.indexedRiskCount>0) s-=40;
        if (c.callRangeRiskCount>0) s-=40;
        c.score=s;
        if (c.exactRefs==0 && c.rawPointers==0 && c.materialised==0 &&
            c.indexedRiskCount==0 && c.callRangeRiskCount==0 && c.gapBytes==4 && c.nearAccesses>=4)
            c.classification="STATIC_PADDING_WORD_STRONG_CANDIDATE_TARGETED_RUNTIME_VALIDATION_REQUIRED";
        else if (c.exactRefs==0 && c.rawPointers==0 && c.materialised==0 &&
                 c.indexedRiskCount==0 && c.callRangeRiskCount==0)
            c.classification="STATIC_PADDING_WORD_CANDIDATE";
        else
            c.classification="REJECT_ALIAS_OR_OWNERSHIP_RISK";
    }

    private void buildAssessment() {
        int strong=0, viable=0, rejected=0;
        for (Candidate c:candidates) {
            if (c.classification.startsWith("STATIC_PADDING_WORD_STRONG")) strong++;
            else if (c.classification.equals("STATIC_PADDING_WORD_CANDIDATE")) viable++;
            else rejected++;
        }
        String cls,next;
        if (strong>0) {
            cls="STATIC_RAM_PADDING_STRONG_CANDIDATE_FOUND_REQUIRES_ONE_TARGETED_LIFETIME_CLOSURE";
            next="Run a target-local closure on the highest-ranked word before any bench builder: prove startup/bulk/indexed ownership and stable runtime lifetime, then use it only as patch-owned temporal state if that pass is clean.";
        } else if (viable>0) {
            cls="STATIC_RAM_PADDING_CANDIDATES_FOUND_NONE_STRONG_ENOUGH_FOR_PATCH";
            next="Review candidate and alias-risk rows; select at most one exact word for a deeper target-local ownership pass. Do not build a temporal AP gate yet.";
        } else {
            cls="NO_SAFE_STATIC_RAM_PADDING_WORD_CANDIDATE_RECOVERED";
            next="Static padding is exhausted by this evidence. Do not repurpose production globals or the V386 task-stack pool; the remaining discriminator would need a separately validated runtime state mechanism.";
        }
        assessmentRows.add(row("overall_classification",cls));
        assessmentRows.add(row("baseline_sha256",sha));
        assessmentRows.add(row("resolved_static_ram_accesses",Integer.toString(accesses.size())));
        assessmentRows.add(row("coverage_intervals",Integer.toString(coverage.size())));
        assessmentRows.add(row("tight_clusters",Integer.toString(clusters.size())));
        assessmentRows.add(row("candidate_words",Integer.toString(candidates.size())));
        assessmentRows.add(row("strong_candidates",Integer.toString(strong)));
        assessmentRows.add(row("other_viable_candidates",Integer.toString(viable)));
        assessmentRows.add(row("rejected_candidates",Integer.toString(rejected)));
        assessmentRows.add(row("indexed_alias_rows",Integer.toString(indexedRisks.size())));
        assessmentRows.add(row("pointer_length_call_ranges",Integer.toString(callRanges.size())));
        assessmentRows.add(row("v386_fixed_stack_pool_reuse_safe","false"));
        assessmentRows.add(row("firmware_or_database_modified","NO/NO"));
        assessmentRows.add(row("next_decision",next));

        patchRows.add(new String[]{"CAN_0x318_TRANSMISSION","UNCHANGED","Frame continues transmitting normally; only AP field may be changed in a later bench build."});
        patchRows.add(new String[]{"NORMAL_STATE","AP2","Runtime AP source remains 2 and 0x318 AP field remains AP2 outside the bounded interval."});
        patchRows.add(new String[]{"TEMPORAL_STATE_STORAGE","V561_CANDIDATE_ONLY","No word from this pass is authorized for patch use until a target-local lifetime closure succeeds."});
        patchRows.add(new String[]{"BOUNDED_INTERVAL","AP0_FIELD_ONLY","Later concept may force only 0x318 AP field to AP0 while patch-owned gate state is active."});
        patchRows.add(new String[]{"RESTORE","AP2","Later concept must restore 0x318 AP field automatically after the finite interval."});
        patchRows.add(new String[]{"CAN_0x368_CAN_0x398","AP2_UNCHANGED","No temporal modification proposed for 0x368 or 0x398."});
    }

    private void writeOutputs() throws Exception {
        writeCsv("_source_contract.csv",new String[]{"item","value","status"},sourceRows);
        writeCsv("_excluded_ranges.csv",new String[]{"label","start","end","reason"},exclusionRows);

        List<String[]> ar=new ArrayList<String[]>();
        for (Access a:accesses) ar.add(new String[]{hex(a.start),hex(a.end),Integer.toString(a.width),a.kind,
            hex(a.owner),functionName(a.owner),hex(a.site),a.evidence,a.instruction});
        writeCsv("_static_ram_accesses.csv",new String[]{"start","end","width","access","owner","owner_name","site","evidence","instruction"},ar);

        List<String[]> cr=new ArrayList<String[]>();
        for (Cluster c:clusters) cr.add(new String[]{hex(c.start),hex(c.end),Long.toString(c.end-c.start+1L),
            Integer.toString(c.accesses),Integer.toString(c.writes),Integer.toString(c.owners)});
        writeCsv("_static_object_clusters.csv",new String[]{"start","end","span_bytes","accesses","writes","distinct_owners"},cr);

        List<String[]> ir=new ArrayList<String[]>();
        for (IndexedRisk r:indexedRisks) ir.add(new String[]{hex(r.base),hex(r.owner),functionName(r.owner),hex(r.site),r.instruction});
        writeCsv("_indexed_access_risks.csv",new String[]{"resolved_base","owner","owner_name","site","instruction"},ir);

        List<String[]> br=new ArrayList<String[]>();
        for (CallRange r:callRanges) br.add(new String[]{hex(r.start),hex(r.end),Long.toString(r.length),r.form,
            hex(r.caller),functionName(r.caller),hex(r.site),r.instruction});
        writeCsv("_pointer_length_call_ranges.csv",new String[]{"start","end","length","form","caller","caller_name","site","instruction"},br);

        List<String[]> cand=new ArrayList<String[]>();
        List<String[]> audit=new ArrayList<String[]>();
        for (Candidate c:candidates) {
            cand.add(new String[]{Integer.toString(c.score),hex(c.address),hex(c.gapStart),hex(c.gapEnd),Integer.toString(c.gapBytes),
                c.cluster==null?"":hex(c.cluster.start),c.cluster==null?"":hex(c.cluster.end),
                c.left==null?"":hex(c.left.site),c.left==null?"":hex(c.left.owner),
                c.right==null?"":hex(c.right.site),c.right==null?"":hex(c.right.owner),
                Integer.toString(c.nearAccesses),Integer.toString(c.nearWrites),Integer.toString(c.nearOwners),c.classification});
            audit.add(new String[]{hex(c.address),Integer.toString(c.exactRefs),Integer.toString(c.rawPointers),
                Integer.toString(c.materialised),Integer.toString(c.indexedRiskCount),Integer.toString(c.callRangeRiskCount),
                c.exclusion,c.classification});
        }
        writeCsv("_candidate_padding_words.csv",new String[]{"score","address","gap_start","gap_end","gap_bytes","cluster_start","cluster_end",
            "left_site","left_owner","right_site","right_owner","near_accesses","near_writes","near_owners","classification"},cand);
        writeCsv("_candidate_access_audit.csv",new String[]{"address","exact_xrefs","raw_pointer_occurrences","exact_materialisations",
            "near_indexed_alias_risks","pointer_length_range_risks","excluded_by","classification"},audit);

        writeCsv("_ap318_patch_access_contract.csv",new String[]{"item","value","detail"},patchRows);
        writeCsv("_assessment.csv",new String[]{"item","value","detail"},padAssessmentRows());
        writeCsv("_errors.csv",new String[]{"phase","address","error"},errorRows);

        BufferedWriter w=writer(output("_summary.md"));
        try {
            w.write("# Tesla Gateway Static RAM Padding Word for AP318 Temporal Gate Trace V561\n\n");
            w.write("- Exact stock SHA-256: `"+sha+"`\n");
            w.write("- Decompiler invoked: `NO`\n- High P-code invoked: `NO`\n");
            w.write("- Static RAM accesses: `"+accesses.size()+"`\n");
            w.write("- Candidate words: `"+candidates.size()+"`\n");
            w.write("- Errors: `"+errorRows.size()+"`\n");
            w.write("- Classification: `"+assessmentRows.get(0)[1]+"`\n\n");
            w.write("## Why this is the next pass\n\n");
            w.write("V560 exhausted native shared-state reuse. V386 already prohibits fixed allocation inside 0x4006C000..0x40093FFF because that region is the dynamic task-stack pool. V561 therefore looks only for a four-byte hole bracketed by real static RAM fields and rejects candidates with direct, pointer, materialisation, indexed-alias or pointer+length ownership evidence.\n\n");
            w.write("A strong result is deliberately **not** patch authorization. It selects one exact word for a final target-local runtime/startup/bulk-ownership closure.\n\n");
            w.write("The later bench concept keeps CAN 0x318 transmitting normally and would change only its AP field during a finite interval; 0x368/0x398 and runtime AP2 remain unchanged.\n");
        } finally { w.close(); }
    }

    private List<String[]> padAssessmentRows() {
        List<String[]> out=new ArrayList<String[]>();
        for (String[] r:assessmentRows) {
            if (r.length==3) out.add(r);
            else if (r.length==2) out.add(new String[]{r[0],r[1],""});
            else out.add(new String[]{r.length>0?r[0]:"",r.length>1?r[1]:"",r.length>2?r[2]:""});
        }
        return out;
    }

    private void zipOutputs() throws Exception {
        String[] suffixes=new String[]{"_source_contract.csv","_excluded_ranges.csv","_static_ram_accesses.csv",
            "_static_object_clusters.csv","_indexed_access_risks.csv","_pointer_length_call_ranges.csv",
            "_candidate_padding_words.csv","_candidate_access_audit.csv","_ap318_patch_access_contract.csv",
            "_assessment.csv","_errors.csv","_summary.md"};
        File zip=output("_bundle.zip");
        ZipOutputStream z=new ZipOutputStream(new FileOutputStream(zip));
        try {
            byte[] buf=new byte[8192];
            for (String s:suffixes) {
                File f=output(s); if (!f.exists()) continue;
                z.putNextEntry(new ZipEntry(f.getName()));
                InputStream in=new FileInputStream(f);
                try {int n; while ((n=in.read(buf))>0) z.write(buf,0,n);} finally {in.close();}
                z.closeEntry();
            }
        } finally {z.close();}
    }

    private Range exclusionFor(long s,long e) {
        for (Range r:EXCLUDED) if (r.overlaps(s,e)) return r;
        return null;
    }

    private boolean inStaticRam(long v) {
        v=u32(v); return v>=RAM_START && v<=RAM_STATIC_END;
    }

    private int memoryWidth(String op) {
        op=stripPrefix(op);
        if (op.startsWith("lbz") || op.startsWith("stb")) return 1;
        if (op.startsWith("lhz") || op.startsWith("lha") || op.startsWith("sth")) return 2;
        if (op.startsWith("ld") || op.startsWith("std")) return 8;
        return 4;
    }

    private boolean isStoreMnemonic(String op) {op=stripPrefix(op); return op.startsWith("st");}
    private boolean isLoadMnemonic(String op) {op=stripPrefix(op); return op.startsWith("lbz")||op.startsWith("lhz")||op.startsWith("lha")||op.startsWith("lwz")||op.startsWith("ld");}
    private String stripPrefix(String op) {
        if (op==null) return ""; op=op.toLowerCase(Locale.ROOT);
        if (op.startsWith("se_")) return op.substring(3);
        if (op.startsWith("e_")) return op.substring(2);
        return op;
    }

    private Long parseImm(String s) {
        if (s==null) return null;
        try {
            s=s.trim().toLowerCase(Locale.ROOT).replace("+","");
            boolean neg=s.startsWith("-"); if (neg) s=s.substring(1);
            long v;
            if (s.startsWith("0x")) v=Long.parseLong(s.substring(2),16);
            else v=Long.parseLong(s,10);
            return Long.valueOf(neg?-v:v);
        } catch (Throwable t) {return null;}
    }

    private long signExtend16(long v) {v&=0xffffL; return (v&0x8000L)!=0 ? v|0xffffffffffff0000L : v;}
    private long u32(long v) {return v&0xffffffffL;}
    private Address addr(long v) {return currentProgram.getAddressFactory().getDefaultAddressSpace().getAddress(u32(v));}
    private String hex(long v) {return String.format(Locale.ROOT,"0x%08X",u32(v));}
    private String norm(String s) {return s==null?"":s.toLowerCase(Locale.ROOT).replace('\t',' ').replaceAll("\\s+"," ").trim();}
    private String clean(String s) {return s==null?"":s.replace('\r',' ').replace('\n',' ').replace('\t',' ').replaceAll("\\s+"," ").trim();}
    private String functionName(long entry) {Function f=functions.getFunctionAt(addr(entry)); if (f==null) f=functions.getFunctionContaining(addr(entry)); return f==null?"":f.getName();}

    private String sha256(byte[] data) throws Exception {
        MessageDigest d=MessageDigest.getInstance("SHA-256"); byte[] h=d.digest(data); StringBuilder b=new StringBuilder();
        for (byte x:h) b.append(String.format(Locale.ROOT,"%02x",x&0xff)); return b.toString();
    }

    private void addError(String phase,long address,Throwable t) {
        errorRows.add(new String[]{phase,hex(address),clean(t==null?"":t.toString())});
    }

    private File output(String suffix) {return new File(outDir,PREFIX+suffix);}
    private BufferedWriter writer(File f) throws Exception {return new BufferedWriter(new OutputStreamWriter(new FileOutputStream(f),StandardCharsets.UTF_8));}
    private String[] row(String a,String b) {return new String[]{a,b,""};}
    private String[] row(String a,String b,String c) {return new String[]{a,b,c};}
    private void writeCsv(String suffix,String[] header,List<String[]> rows) throws Exception {
        BufferedWriter w=writer(output(suffix));
        try {w.write(csvLine(header));w.write("\r\n");for(String[] r:rows){w.write(csvLine(r));w.write("\r\n");}}
        finally {w.close();}
    }
    private String csvLine(String[] r) {StringBuilder b=new StringBuilder();for(int i=0;i<r.length;i++){if(i>0)b.append(',');b.append('"').append((r[i]==null?"":r[i]).replace("\"","\"\"")).append('"');}return b.toString();}
}
