// TeslaGatewayV497R1AP318StartupWakeMin300SerializedReconciliationBenchBuilderV617R2R2.java
//
// BENCH/STATIONARY ONLY. Direct image synthesis; active Ghidra program is not
// committed or modified.
//
// Static prerequisites closed by V618 / V619R1
// --------------------------------------------
// * F7380/F73A8 is a proven nest-aware interrupt critical pair: wrteei 0/1,
//   per-context nesting counter, no calls, no waits, no backward flow, no token.
// * exact command32 0x77226 -> 0x88340 is a clean current reconciliation-episode
//   marker with no external callsite entry.
// * process_vehicle_config_check can set conditional ACTION subsets: 0x800,
//   0x800+0x100000, or 0x800+0x400000+0x100000. Full 0x00500800 is therefore
//   not a universal discriminator.
// * the complete apply_autopilot_config publication corridor 0x87128..0x8713C
//   has six instructions and zero external interior references, so it can be
//   replayed under the critical pair through the final CAN318 store.
//
// V617R2R2 state machine at scratch 0x40014E2C
// ------------------------------------------
// bits  0..8 : countdown 0..300
// bit      9 : CLEAR_BASELINE observed after this re-arm
// bit     10 : CMD32_EPISODE marked by exact 0x77226 call after baseline
// bit     11 : observed ACTION 0x00000800 during that episode
// bit     12 : observed ACTION 0x00100000 during that episode
// bit     13 : observed ACTION 0x00400000 during that episode
// bit     14 : MINIMUM_ELAPSED
// terminal sentinel: DONE = 0x7FFF
//
// Re-arm (first AP publication or each observed V585 A47EA falling-edge event)
// starts countdown=300, clears episode/seen/elapsed/done, establishes baseline
// immediately only if all exact ACTION bits are clear, and forces only CAN318 AP0.
//
// The command32 wrapper marks the exact episode only after a clear baseline. It
// calls stock 0x88340 exactly once, then immediately samples the conditional
// ACTION subset. The oneHz pre-body helper also accumulates the exact subset
// before stock oneHz can reach 0x7150E -> A31E4, closing the preemption window.
//
// Release condition:
//   minimum_elapsed
//   && clear_baseline
//   && cmd32_episode
//   && observed_subset != 0
//   && (ACTION_WORD & 0x00500800) == 0
//
// All state writers and all direct AP-byte transitions use F7380/F73A8. The
// apply_autopilot_config decision, all three AP inserts, and all three stores are
// replayed under that same critical pair through CAN318 store 0x8713C. Therefore
// a newer re-arm cannot leak a stale AP2 publication from that corridor.
//
// CAN368, CAN398 and runtime AP2 remain AP2. Stock process_vehicle_config_check,
// command32 response handling, reset/watchdog logic and V596R1 observer conclusion
// are unchanged. The 0x77226 call instruction is detoured only to add episode
// bookkeeping; the wrapper still invokes stock 0x88340 exactly once.
//
// Input: exact V497R1 2 MiB BIN. Output directory MUST be new/empty. Emits
// patched BIN/S19, exact rollback BIN/S19, report and hashes. Application CRC
// remains stock 0x38C63335 via the established 0x00125800 compensation word.
//
// @category TeslaGateway.Bench
// @menupath Tools.Tesla.Build V497R1 AP318 Serialized Reconciliation V617R2R2

import ghidra.app.plugin.assembler.Assembler;
import ghidra.app.plugin.assembler.Assemblers;
import ghidra.app.script.GhidraScript;
import ghidra.program.model.address.Address;
import ghidra.program.model.address.AddressSpace;
import ghidra.program.model.listing.Function;
import ghidra.program.model.listing.Instruction;
import ghidra.program.model.mem.Memory;
import ghidra.program.model.symbol.Reference;
import ghidra.program.model.symbol.ReferenceIterator;

import java.io.*;
import java.nio.charset.StandardCharsets;
import java.security.MessageDigest;
import java.util.*;
import java.util.zip.CRC32;

public class TeslaGatewayV497R1AP318StartupWakeMin300SerializedReconciliationBenchBuilderV617R2R2
        extends GhidraScript {

    private static final String PREFIX =
        "TeslaGatewayV497R1AP318StartupWakeMin300SerializedReconciliationBenchBuilderV617R2R2";

    private static final String STOCK_SHA256 =
        "889ab36ae6d17bb897587df85db6201f32cb33f01ba101962979f765ef0ee3fe";
    private static final String V497R1_INPUT_SHA256 =
        "e4848144acb4331fe4737560c834951f08e0c5798584b2f724855d76fb5327b9";
    private static final String EXPECTED_LANGUAGE = "PowerPC:BE:64:VLE-32addr";

    private static final int IMAGE_SIZE = 0x00200000;
    private static final int SREC_DATA_LENGTH = 16;
    private static final long APP_START = 0x00020000L;
    private static final int EXPECTED_APP_SIZE = 0x0012929A;
    private static final long EXPECTED_APP_SIZE_INV = 0xFFED6D65L;
    private static final long APP_CRC_ADDRESS = 0x00020000L;
    private static final long APP_SIZE_ADDRESS = 0x00020004L;
    private static final long APP_SIZE_INV_ADDRESS = 0x00020008L;
    private static final long STOCK_APP_CRC = 0x38C63335L;
    private static final long COMPENSATION_ADDRESS = 0x00125800L;

    // V619R1-approved compact session state. Assembly uses these constants
    // via formatter helpers; no duplicate state literals are authoritative.
    private static final long SCRATCH_WORD = 0x40014E2CL;
    private static final int WINDOW_TICKS = 300;
    private static final int COUNT_MASK = 0x01FF;
    private static final int CLEAR_BASELINE = 0x0200;
    private static final int CMD32_EPISODE = 0x0400;
    private static final int SEEN_0800 = 0x0800;
    private static final int SEEN_100000 = 0x1000;
    private static final int SEEN_400000 = 0x2000;
    private static final int MINIMUM_ELAPSED = 0x4000;
    private static final int DONE_STATE = 0x7FFF;
    private static final int SEEN_MASK = SEEN_0800 | SEEN_100000 | SEEN_400000;

    // Exact V609/V619R1 process-config/A31E4 surface.
    private static final long ACTION_WORD = 0x4001314CL;
    private static final long ACTION_0800 = 0x00000800L;
    private static final long ACTION_100000 = 0x00100000L;
    private static final long ACTION_400000 = 0x00400000L;
    private static final long ACTION_FULL_MASK = 0x00500800L;
    private static final long CRITICAL_ENTER = 0x000F7380L;
    private static final long CRITICAL_EXIT  = 0x000F73A8L;
    private static final long CRITICAL_EXIT_ENABLE = 0x000F73DEL;

    // apply_autopilot_config publication sequence.
    private static final long AP_OWNER = 0x000870F0L;
    private static final long INSERT_368 = 0x00087128L;
    private static final long INSERT_318 = 0x0008712CL;
    private static final long INSERT_398 = 0x00087130L;
    private static final long STORE_368 = 0x00087134L;
    private static final long STORE_398 = 0x00087138L;
    private static final long STORE_318 = 0x0008713CL;
    private static final long PUBLICATION_REJOIN = 0x0008713EL;
    private static final long AP_WORD_368 = 0x4004AA38L;
    private static final long AP_WORD_318 = 0x40047CACL;
    private static final long AP_WORD_398 = 0x40049DA4L;
    private static final long AP318_BYTE = 0x40047CAFL;

    // oneHzThings timer owner.
    private static final long ONE_HZ = 0x0006F99CL;

    // Native A47EA falling-wake-edge producer recovered by V584/V585.
    private static final long WAKE_EDGE_SEND_CALL = 0x000A4ADAL;
    private static final long EVENT_SEND = 0x000F7942L;

    // Verified-zero padding family. Boundaries are contiguous and fail-closed.
    private static final long AP_WRAPPER = 0x00125A00L;
    private static final int AP_WRAPPER_RESERVED = 0x140;
    private static final long ONEHZ_WRAPPER = 0x00125B40L;
    private static final int ONEHZ_WRAPPER_RESERVED = 0x140;
    private static final long WAKE_WRAPPER = 0x00125C80L;
    private static final int WAKE_WRAPPER_RESERVED = 0x100;
    private static final long STATE_HELPER = 0x00125D80L;
    private static final int STATE_HELPER_RESERVED = 0x180;
    private static final long CMD32_WRAPPER = 0x00125F00L;
    private static final int CMD32_WRAPPER_RESERVED = 0x0FC; // 0x125FFC is stock data

    // V497R1 lineage guards.
    private static final long STORED_AUTOPILOT_BYTE = 0x0001CDBDL;
    private static final long RUNTIME_FORCE = 0x00087110L;
    private static final long PREPSLEEP_PATCH = 0x0006C808L;
    private static final long COMMAND33_SIGNATURE = 0x00125980L;
    private static final long A2BC_BRANCH = 0x00088438L;
    private static final long PENDING_PRIMARY = 0x00095402L;
    private static final long PENDING_MIRROR = 0x00095406L;
    private static final long EVENT19D_CALL = 0x0009541AL;
    private static final long APTRIAL_GODOWN_CALL = 0x0006F534L;
    private static final long APTRIAL_CLEANUP = 0x0006F91CL;
    private static final long CC1701_SELECTOR = 0x00071752L;

    // Explicitly prove command32/check remain untouched relative to V497R1.
    private static final long COMMAND32_HANDLER = 0x000771B4L;
    private static final long COMMAND32_CHECK_CALL = 0x00077226L;
    private static final long VEHICLE_CONFIG_CHECK = 0x00088340L;
    private static final long SELECTOR_ENABLE_LOAD = 0x00088396L;

    // V619R1 exact episode marker hook.
    private static final long CMD32_EPISODE_CALL = COMMAND32_CHECK_CALL;

    private static final byte[] NOP4 = bytes(0x44,0x00,0x44,0x00);
    private static final byte[] COMMAND33_MARKER =
        bytes(0x43,0x33,0x33,0x53,0x59,0x4E,0x30,0x00); // C33SYN0\0

    private Memory memory;
    private AddressSpace space;

    private static class Contract {
        byte[] insert368;
        byte[] insert318;
        byte[] insert398;
        byte[] store368;
        byte[] store398;
        byte[] store318;
        byte[] command32Entry;
        byte[] command32CheckCall;
        byte[] command32Hook;
        byte[] selectorEnableLoad;
        byte[] apHook;
        byte[] oneHzOriginal;
        byte[] oneHzHook;
        int oneHzSpan;
        long oneHzRejoin;
        byte[] wakeEdgeOriginal;
        byte[] wakeEdgeHook;
        byte[] apWrapper;
        byte[] oneHzWrapper;
        byte[] wakeWrapper;
        byte[] stateHelper;
        byte[] cmd32Wrapper;
        String oneHzRelocatedListing;
    }

    @Override
    protected void run() throws Exception {
        if(currentProgram==null)
            throw new IllegalStateException("No Ghidra program is open.");

        memory=currentProgram.getMemory();
        space=currentProgram.getAddressFactory().getDefaultAddressSpace();

        String language=currentProgram.getLanguageID().toString();
        if(!EXPECTED_LANGUAGE.equals(language))
            throw new IllegalStateException("Unexpected Ghidra language: "+language);

        String stockSha=sha256CurrentProgram();
        if(!STOCK_SHA256.equalsIgnoreCase(stockSha))
            throw new IllegalStateException(
                "V617R2R2 requires the exact stock analysed Ghidra project. SHA256="+stockSha);

        Contract c=validateAndBuildStockContract();

        File input=askFile("Select exact V497R1 2 MiB BIN","Open");
        if(input==null)return;
        File outDir=askDirectory("Select NEW EMPTY V617R2R2 output folder","Select");
        if(outDir==null)return;
        requireEmptyDirectory(outDir);

        byte[] baseline=readWholeFile(input);
        validateV497R1Baseline(baseline,c);

        byte[] patched=baseline.clone();

        // Four bounded hooks: AP publication, oneHz pre-body, observed A47EA event,
        // and exact command32 process-config callsite.
        putBytes(patched,INSERT_368,c.apHook);
        putBytes(patched,ONE_HZ,c.oneHzHook);
        putBytes(patched,WAKE_EDGE_SEND_CALL,c.wakeEdgeHook);
        putBytes(patched,AP_WRAPPER,c.apWrapper);
        putBytes(patched,ONEHZ_WRAPPER,c.oneHzWrapper);
        putBytes(patched,WAKE_WRAPPER,c.wakeWrapper);
        putBytes(patched,STATE_HELPER,c.stateHelper);
        putBytes(patched,CMD32_EPISODE_CALL,c.command32Hook);
        putBytes(patched,CMD32_WRAPPER,c.cmd32Wrapper);

        // Re-solve the established four-byte CRC-neutral compensation slot.
        putBytes(patched,COMPENSATION_ADDRESS,new byte[]{0,0,0,0});
        byte[] app=slice(patched,APP_START,EXPECTED_APP_SIZE);
        int compOffset=(int)(COMPENSATION_ADDRESS-APP_START);
        byte[] compensation=solveFourBytePatch(app,compOffset,STOCK_APP_CRC);
        if(compensation==null)
            throw new IllegalStateException("V617R2R2 CRC-neutral compensation solver failed.");
        putBytes(patched,COMPENSATION_ADDRESS,compensation);

        validateOutput(baseline,patched,c,compensation);

        String stem=
            "Tesla_MCU1_V497R1_AP318SerializedReconciliation_V617R2R2_CRCNeutral";
        File bin=new File(outDir,stem+".bin");
        File s19=new File(outDir,stem+".S19");
        File rollbackBin=new File(outDir,"ROLLBACK_V497R1_exact.bin");
        File rollbackS19=new File(outDir,"ROLLBACK_V497R1_exact.S19");
        File report=new File(outDir,stem+"_report.txt");
        File hashes=new File(outDir,stem+"_hashes.txt");

        writeBinary(bin,patched);
        writeS19(s19,patched);
        writeBinary(rollbackBin,baseline);
        writeS19(rollbackS19,baseline);
        writeReport(report,input,stockSha,baseline,patched,c,compensation);

        try(BufferedWriter w=new BufferedWriter(
                new OutputStreamWriter(new FileOutputStream(hashes),StandardCharsets.UTF_8))){
            w.write("Input V497R1 SHA256: "+sha256(baseline)+"\r\n");
            w.write("Output BIN SHA256:    "+sha256File(bin)+"\r\n");
            w.write("Output S19 SHA256:    "+sha256File(s19)+"\r\n");
            w.write("Rollback BIN SHA256:  "+sha256File(rollbackBin)+"\r\n");
            w.write("Rollback S19 SHA256:  "+sha256File(rollbackS19)+"\r\n");
        }
        popup(
            "V617R2R2 complete.\n\n"+
            "Release requires: post-rearm clear baseline + exact command32 episode + nonzero observed conditional ACTION subset + later all-clear + >=300 oneHz samples.\n"+
            "The 0x87128..0x8713C AP publication corridor is serialized through the final CAN318 store.\n"+
            "Observed A47EA re-arms, oneHz state transitions and direct AP-byte transitions use the proven F7380/F73A8 critical pair.\n"+
            "Stock 0x88340 is still called exactly once by the command32 wrapper.\n\n"+
            "Do not flash yet: upload all generated artifacts for independent validation first.\n"+
            "BENCH/STATIONARY ONLY. Keep rollback immediately available.");
    }

    private Contract validateAndBuildStockContract() throws Exception {
        Contract c=new Contract();

        Function ap=currentProgram.getFunctionManager().getFunctionContaining(addr(INSERT_368));
        if(ap==null || (ap.getEntryPoint().getOffset()&0xffffffffL)!=AP_OWNER)
            throw new IllegalStateException(
                "0x87128 is not inside expected apply_autopilot_config owner 0x870F0.");

        Instruction i368=getInstructionAt(addr(INSERT_368));
        Instruction i318=getInstructionAt(addr(INSERT_318));
        Instruction i398=getInstructionAt(addr(INSERT_398));
        requireRelocatableInsert(i368,INSERT_368);
        requireRelocatableInsert(i318,INSERT_318);
        requireRelocatableInsert(i398,INSERT_398);
        c.insert368=readCurrentBytes(addr(INSERT_368),4);
        c.insert318=readCurrentBytes(addr(INSERT_318),4);
        c.insert398=readCurrentBytes(addr(INSERT_398),4);
        c.store368=readCurrentBytes(addr(STORE_368),4);
        c.store398=readCurrentBytes(addr(STORE_398),4);
        c.store318=readCurrentBytes(addr(STORE_318),2);

        requireStoreTarget(STORE_368,AP_WORD_368);
        requireStoreTarget(STORE_318,AP_WORD_318);
        requireStoreTarget(STORE_398,AP_WORD_398);

        c.command32Entry=readCurrentBytes(addr(COMMAND32_HANDLER),4);
        c.command32CheckCall=readCurrentBytes(addr(COMMAND32_CHECK_CALL),4);
        c.selectorEnableLoad=readCurrentBytes(addr(SELECTOR_ENABLE_LOAD),4);
        Instruction cmdCall=getInstructionAt(addr(COMMAND32_CHECK_CALL));
        if(cmdCall==null || cmdCall.getLength()!=4 ||
           directCallTarget(cmdCall)!=VEHICLE_CONFIG_CHECK)
            throw new IllegalStateException(
                "0x77226 is not the stock 4-byte call to process_vehicle_config_check 0x88340.");
        c.command32Hook=assembleLine(addr(CMD32_EPISODE_CALL),
            "e_bl "+hex(CMD32_WRAPPER),4);

        // Recover a complete 4- or 6-byte relocatable prefix at oneHz entry.
        Function oneHz=currentProgram.getFunctionManager().getFunctionAt(addr(ONE_HZ));
        if(oneHz==null)
            oneHz=currentProgram.getFunctionManager().getFunctionContaining(addr(ONE_HZ));
        if(oneHz==null || (oneHz.getEntryPoint().getOffset()&0xffffffffL)!=ONE_HZ)
            throw new IllegalStateException("oneHzThings 0x6F99C is not defined as expected.");

        ByteArrayOutputStream relocated=new ByteArrayOutputStream();
        StringBuilder relocatedText=new StringBuilder();
        long cursor=ONE_HZ;
        int total=0;
        while(total<4){
            Instruction ins=getInstructionAt(addr(cursor));
            if(ins==null)
                throw new IllegalStateException(
                    "No instruction at oneHz hook prefix "+hex(cursor)+".");
            if(ins.getLength()!=2 && ins.getLength()!=4)
                throw new IllegalStateException(
                    "Unsupported oneHz prefix instruction length at "+hex(cursor)+": "+ins.getLength());
            if(ins.getFlowType()!=null &&
               (ins.getFlowType().isCall() || ins.getFlowType().isJump() ||
                ins.getFlowType().isTerminal()))
                throw new IllegalStateException(
                    "oneHz hook prefix contains flow instruction at "+hex(cursor)+": "+ins);
            Reference[] rr=ins.getReferencesFrom();
            if(rr!=null && rr.length!=0 && !isSafeOneHzRelocatedReference(ins,cursor))
                throw new IllegalStateException(
                    "oneHz hook prefix contains unsafe reference-bearing instruction at "+
                    hex(cursor)+": "+ins);
            byte[] raw=readCurrentBytes(ins.getAddress(),ins.getLength());
            relocated.write(raw,0,raw.length);
            if(relocatedText.length()!=0)relocatedText.append(" | ");
            relocatedText.append(ins.getAddress()).append(": ").append(ins.toString());
            total+=ins.getLength();
            cursor+=ins.getLength();
            if(total>6)
                throw new IllegalStateException(
                    "oneHz relocatable hook span exceeded 6 bytes; refusing entry detour.");
        }
        if(total!=4 && total!=6)
            throw new IllegalStateException(
                "oneHz hook prefix is not a supported 4/6-byte span: "+total);

        if(total==6){
            Instruction first=getInstructionAt(addr(ONE_HZ));
            Instruction second=first==null?null:
                getInstructionAt(addr(ONE_HZ+first.getLength()));
            if(second!=null && second.getAddress().getOffset()!=ONE_HZ){
                ReferenceIterator rit=currentProgram.getReferenceManager().getReferencesTo(second.getAddress());
                while(rit.hasNext()){
                    Reference r=rit.next();
                    long from=r.getFromAddress().getOffset()&0xffffffffL;
                    if(from<ONE_HZ || from>=ONE_HZ+total)
                        throw new IllegalStateException(
                            "External reference enters relocated oneHz prefix at "+
                            second.getAddress()+" from "+r.getFromAddress()+".");
                }
            }
        }

        c.oneHzOriginal=relocated.toByteArray();
        c.oneHzSpan=total;
        c.oneHzRejoin=ONE_HZ+total;
        c.oneHzRelocatedListing=relocatedText.toString();

        byte[] oneHzBranch=assembleLine(addr(ONE_HZ),
            "e_b "+hex(ONEHZ_WRAPPER),4);
        if(total==4){
            c.oneHzHook=oneHzBranch;
        }
        else {
            byte[] nop=assembleLine(addr(ONE_HZ+4),"se_nop",2);
            c.oneHzHook=new byte[6];
            System.arraycopy(oneHzBranch,0,c.oneHzHook,0,4);
            System.arraycopy(nop,0,c.oneHzHook,4,2);
        }

        c.apHook=assembleLine(addr(INSERT_368),"e_b "+hex(AP_WRAPPER),4);
        requireNoExternalPublicationInteriorReferences();

        Instruction wakeCall=getInstructionAt(addr(WAKE_EDGE_SEND_CALL));
        if(wakeCall==null || wakeCall.getLength()!=4 ||
           wakeCall.getFlowType()==null || !wakeCall.getFlowType().isCall() ||
           wakeCall.getFlowType().isComputed())
            throw new IllegalStateException(
                "V617R2R2 expected direct 4-byte A47EA event-send call at "+hex(WAKE_EDGE_SEND_CALL)+".");
        Address[] wakeFlows=wakeCall.getFlows();
        if(wakeFlows==null || wakeFlows.length!=1 ||
           (wakeFlows[0].getOffset()&0xffffffffL)!=EVENT_SEND)
            throw new IllegalStateException(
                "V617R2R2 A47EA wake-edge call does not target F7942.");
        c.wakeEdgeOriginal=readCurrentBytes(addr(WAKE_EDGE_SEND_CALL),4);
        c.wakeEdgeHook=assembleLine(addr(WAKE_EDGE_SEND_CALL),
            "e_bl "+hex(WAKE_WRAPPER),4);

        Function critEnter=currentProgram.getFunctionManager().getFunctionAt(addr(CRITICAL_ENTER));
        Function critExit=currentProgram.getFunctionManager().getFunctionAt(addr(CRITICAL_EXIT));
        if(critEnter==null || (critEnter.getEntryPoint().getOffset()&0xffffffffL)!=CRITICAL_ENTER)
            throw new IllegalStateException("V617R2R2 critical-enter 0xF7380 is not defined as expected.");
        if(critExit==null || (critExit.getEntryPoint().getOffset()&0xffffffffL)!=CRITICAL_EXIT)
            throw new IllegalStateException("V617R2R2 critical-exit 0xF73A8 is not defined as expected.");
        requireInstructionText(CRITICAL_ENTER,"wrteei 0x0","critical enter disables external interrupts");
        requireInstructionText(CRITICAL_EXIT_ENABLE,"wrteei 0x1","critical exit re-enables at nesting zero");

        c.apWrapper=buildApWrapper(c);
        c.oneHzWrapper=buildOneHzWrapper(c);
        c.wakeWrapper=buildWakeWrapper(c);
        c.stateHelper=buildStateHelper();
        c.cmd32Wrapper=buildCmd32Wrapper();

        if(c.apWrapper.length>AP_WRAPPER_RESERVED)
            throw new IllegalStateException(
                "V617R2R2 AP wrapper exceeds reserved cave: "+c.apWrapper.length);
        if(c.oneHzWrapper.length>ONEHZ_WRAPPER_RESERVED)
            throw new IllegalStateException(
                "V617R2R2 oneHz wrapper exceeds reserved cave: "+c.oneHzWrapper.length);
        if(c.wakeWrapper.length>WAKE_WRAPPER_RESERVED)
            throw new IllegalStateException(
                "V617R2R2 wake wrapper exceeds reserved cave: "+c.wakeWrapper.length);
        if(c.stateHelper.length>STATE_HELPER_RESERVED)
            throw new IllegalStateException(
                "V617R2R2 state helper exceeds reserved cave: "+c.stateHelper.length);
        if(c.cmd32Wrapper.length>CMD32_WRAPPER_RESERVED)
            throw new IllegalStateException(
                "V617R2R2 command32 wrapper exceeds reserved cave: "+c.cmd32Wrapper.length);

        return c;
    }

    private boolean isSafeOneHzRelocatedReference(Instruction ins,long site) {
        if(ins==null || site!=ONE_HZ)return false;
        String mnemonic=lower(ins.getMnemonicString());
        return "e_stwu".equals(mnemonic);
    }

    private void requireRelocatableInsert(Instruction i,long site) {
        if(i==null || i.getLength()!=4)
            throw new IllegalStateException(
                "Expected 4-byte AP insertion instruction at "+hex(site)+".");
        if(i.getFlowType()!=null &&
           (i.getFlowType().isCall() || i.getFlowType().isJump() ||
            i.getFlowType().isTerminal()))
            throw new IllegalStateException(
                "AP insertion site is a flow instruction at "+hex(site)+": "+i);
        String mnemonic=i.getMnemonicString()==null?"":i.getMnemonicString();
        if(mnemonic.endsWith("."))
            throw new IllegalStateException(
                "AP insertion site updates condition state and is not safely relocatable at "+
                hex(site)+": "+i);
        Reference[] rr=i.getReferencesFrom();
        if(rr!=null && rr.length!=0)
            throw new IllegalStateException(
                "AP insertion site carries references and is not safely relocatable at "+
                hex(site)+": "+i);
    }

    private byte[] buildApWrapper(Contract c) throws Exception {
        // V619R1 proved there are no external entries to 0x8712C..0x8713C.
        // Replay the full six-instruction corridor while interrupts are disabled.
        return assembleBlock(AP_WRAPPER,
            ins("e_stwu r1,-48(r1)",4),
            ins("e_stw r0,4(r1)",4),
            ins("e_stw r6,8(r1)",4),
            ins("e_stw r7,12(r1)",4),
            ins("e_stw r8,16(r1)",4),
            ins("e_stw r9,20(r1)",4),
            ins("e_stw r10,24(r1)",4),
            ins("e_stw r11,28(r1)",4),
            ins("e_stw r12,32(r1)",4),
            ins("mfcr r12",4),
            ins("e_stw r12,36(r1)",4),
            ins("e_bl "+hex(CRITICAL_ENTER),4),

            // Initialize only on the first successful AP publication of a session.
            ins("e_lis r11,"+hi16(SCRATCH_WORD),4),
            ins("e_add16i r11,r11,"+lo16(SCRATCH_WORD),4),
            ins("e_lwz r12,0(r11)",4),
            ins("e_cmp16i. r12,0x0",4),
            br("e_bne cr0,","STATE_READY",4),
            ins("e_li r12,"+imm16(WINDOW_TICKS),4),
            ins("e_lis r10,"+hi16(ACTION_WORD),4),
            ins("e_add16i r10,r10,"+lo16(ACTION_WORD),4),
            ins("e_lwz r0,0(r10)",4),
            ins("e_rlwinm r7,r0,0x0,"+bitCrPos(ACTION_0800)+","+bitCrPos(ACTION_0800),4),

            ins("se_cmpi r7,0x0",2),
            br("e_bne cr0,","INIT_STORE",4),
            ins("e_rlwinm r7,r0,0x0,"+bitCrPos(ACTION_100000)+","+bitCrPos(ACTION_100000),4),

            ins("se_cmpi r7,0x0",2),
            br("e_bne cr0,","INIT_STORE",4),
            ins("e_rlwinm r7,r0,0x0,"+bitCrPos(ACTION_400000)+","+bitCrPos(ACTION_400000),4),

            ins("se_cmpi r7,0x0",2),
            br("e_bne cr0,","INIT_STORE",4),
            ins("e_li r7,"+imm16(CLEAR_BASELINE),4),

            ins("or r12,r12,r7",4),
            mark("INIT_STORE"),
            ins("e_stw r12,0(r11)",4),

            mark("STATE_READY"),
            // DONE is the exact 0x7FFF sentinel. Active states never use that full value.
            ins("e_li r8,0x1",4),
            ins("e_cmpl16i. r12,"+imm16(DONE_STATE),4),
            br("e_bne cr0,","RESTORE_CORRIDOR_REGS",4),
            ins("e_li r8,0x0",4),

            mark("RESTORE_CORRIDOR_REGS"),
            ins("e_lwz r0,4(r1)",4),
            ins("e_lwz r6,8(r1)",4),
            ins("e_lwz r7,12(r1)",4),
            ins("e_lwz r10,24(r1)",4),
            ins("e_lwz r11,28(r1)",4),

            raw(c.insert368),
            ins("e_cmp16i. r8,0x0",4),
            br("e_beq cr0,","INSERT_318",4),
            ins("se_li r0,0x0",2),
            mark("INSERT_318"),
            raw(c.insert318),
            // CAN398 always receives stock AP2 source from the saved r0.
            ins("e_lwz r0,4(r1)",4),
            raw(c.insert398),
            raw(c.store368),
            raw(c.store398),
            raw(c.store318),

            // Preserve stock post-corridor r6/r7 across critical-exit clobbers.
            ins("e_stw r6,8(r1)",4),
            ins("e_stw r7,12(r1)",4),
            ins("e_bl "+hex(CRITICAL_EXIT),4),
            ins("e_lwz r6,8(r1)",4),
            ins("e_lwz r7,12(r1)",4),
            ins("e_lwz r8,16(r1)",4),
            ins("e_lwz r9,20(r1)",4),
            ins("e_lwz r12,32(r1)",4),
            ins("e_lwz r0,36(r1)",4),
            ins("mtcrf 0xff,r0",4),
            ins("e_add16i r1,r1,48",4),
            ins("e_b "+hex(PUBLICATION_REJOIN),4)
        );
    }

    private byte[] buildOneHzWrapper(Contract c) throws Exception {
        ByteArrayOutputStream out=new ByteArrayOutputStream();
        Address p=addr(ONEHZ_WRAPPER);
        p=emitRaw(out,p,c.oneHzOriginal);

        // We call an injected helper before rejoining stock oneHz. Preserve every
        // volatile GPR we touch/could lose across the helper, plus LR and CR.
        p=emit(out,p,"e_stwu r1,-64(r1)",4);
        p=emit(out,p,"e_stw r0,4(r1)",4);
        p=emit(out,p,"e_stw r3,8(r1)",4);
        p=emit(out,p,"e_stw r4,12(r1)",4);
        p=emit(out,p,"e_stw r5,16(r1)",4);
        p=emit(out,p,"e_stw r6,20(r1)",4);
        p=emit(out,p,"e_stw r7,24(r1)",4);
        p=emit(out,p,"e_stw r8,28(r1)",4);
        p=emit(out,p,"e_stw r9,32(r1)",4);
        p=emit(out,p,"e_stw r10,36(r1)",4);
        p=emit(out,p,"e_stw r11,40(r1)",4);
        p=emit(out,p,"e_stw r12,44(r1)",4);
        p=emit(out,p,"se_mflr r0",2);
        p=emit(out,p,"e_stw r0,48(r1)",4);
        p=emit(out,p,"mfcr r0",4);
        p=emit(out,p,"e_stw r0,52(r1)",4);

        p=emit(out,p,"e_bl "+hex(STATE_HELPER),4);

        p=emit(out,p,"e_lwz r0,52(r1)",4);
        p=emit(out,p,"mtcrf 0xff,r0",4);
        p=emit(out,p,"e_lwz r0,48(r1)",4);
        p=emit(out,p,"se_mtlr r0",2);
        p=emit(out,p,"e_lwz r12,44(r1)",4);
        p=emit(out,p,"e_lwz r11,40(r1)",4);
        p=emit(out,p,"e_lwz r10,36(r1)",4);
        p=emit(out,p,"e_lwz r9,32(r1)",4);
        p=emit(out,p,"e_lwz r8,28(r1)",4);
        p=emit(out,p,"e_lwz r7,24(r1)",4);
        p=emit(out,p,"e_lwz r6,20(r1)",4);
        p=emit(out,p,"e_lwz r5,16(r1)",4);
        p=emit(out,p,"e_lwz r4,12(r1)",4);
        p=emit(out,p,"e_lwz r3,8(r1)",4);
        p=emit(out,p,"e_lwz r0,4(r1)",4);
        p=emit(out,p,"e_add16i r1,r1,64",4);
        p=emit(out,p,"e_b "+hex(c.oneHzRejoin),4);
        return out.toByteArray();
    }

    private byte[] buildWakeWrapper(Contract c) throws Exception {
        ByteArrayOutputStream out=new ByteArrayOutputStream();
        Address p=addr(WAKE_WRAPPER);

        p=emit(out,p,"e_stwu r1,-64(r1)",4);
        p=emit(out,p,"e_stw r0,4(r1)",4);
        p=emit(out,p,"e_stw r3,8(r1)",4);
        p=emit(out,p,"e_stw r4,12(r1)",4);
        p=emit(out,p,"e_stw r5,16(r1)",4);
        p=emit(out,p,"e_stw r6,20(r1)",4);
        p=emit(out,p,"e_stw r11,24(r1)",4);
        p=emit(out,p,"e_stw r12,28(r1)",4);
        p=emit(out,p,"se_mflr r0",2);
        p=emit(out,p,"e_stw r0,32(r1)",4);
        p=emit(out,p,"mfcr r0",4);
        p=emit(out,p,"e_stw r0,36(r1)",4);

        p=emit(out,p,"e_bl "+hex(CRITICAL_ENTER),4);
        p=emit(out,p,"e_li r12,"+imm16(WINDOW_TICKS),4);
        p=emit(out,p,"e_lis r11,"+hi16(ACTION_WORD),4);
        p=emit(out,p,"e_add16i r11,r11,"+lo16(ACTION_WORD),4);
        p=emit(out,p,"e_lwz r0,0(r11)",4);
        long storeState=WAKE_WRAPPER+0x68L;
        p=emit(out,p,"e_rlwinm r7,r0,0x0,"+bitCrPos(ACTION_0800)+","+bitCrPos(ACTION_0800),4);

        p=emit(out,p,"se_cmpi r7,0x0",2);
        p=emit(out,p,"e_bne cr0,"+hex(storeState),4);
        p=emit(out,p,"e_rlwinm r7,r0,0x0,"+bitCrPos(ACTION_100000)+","+bitCrPos(ACTION_100000),4);

        p=emit(out,p,"se_cmpi r7,0x0",2);
        p=emit(out,p,"e_bne cr0,"+hex(storeState),4);
        p=emit(out,p,"e_rlwinm r7,r0,0x0,"+bitCrPos(ACTION_400000)+","+bitCrPos(ACTION_400000),4);

        p=emit(out,p,"se_cmpi r7,0x0",2);
        p=emit(out,p,"e_bne cr0,"+hex(storeState),4);
        p=emit(out,p,"e_li r7,"+imm16(CLEAR_BASELINE),4);

        p=emit(out,p,"or r12,r12,r7",4);
        if((p.getOffset()&0xffffffffL)!=storeState)
            throw new IllegalStateException("V617R2R2 wake store-state label drifted: "+p+" expected "+hex(storeState));
        p=emit(out,p,"e_lis r11,"+hi16(SCRATCH_WORD),4);
        p=emit(out,p,"e_add16i r11,r11,"+lo16(SCRATCH_WORD),4);
        p=emit(out,p,"e_stw r12,0(r11)",4);

        p=emit(out,p,"e_lis r11,"+hi16(AP318_BYTE),4);
        p=emit(out,p,"e_add16i r11,r11,"+lo16(AP318_BYTE),4);
        p=emit(out,p,"e_lbz r12,0(r11)",4);
        p=emit(out,p,"e_and2i. r12,0x1f",4);
        p=emit(out,p,"e_stb r12,0(r11)",4);
        p=emit(out,p,"e_bl "+hex(CRITICAL_EXIT),4);

        p=emit(out,p,"e_lwz r0,36(r1)",4);
        p=emit(out,p,"mtcrf 0xff,r0",4);
        p=emit(out,p,"e_lwz r3,8(r1)",4);
        p=emit(out,p,"e_lwz r4,12(r1)",4);
        p=emit(out,p,"e_lwz r5,16(r1)",4);
        p=emit(out,p,"e_lwz r6,20(r1)",4);
        p=emit(out,p,"e_bl "+hex(EVENT_SEND),4);

        p=emit(out,p,"e_lwz r0,32(r1)",4);
        p=emit(out,p,"se_mtlr r0",2);
        p=emit(out,p,"e_lwz r12,28(r1)",4);
        p=emit(out,p,"e_lwz r11,24(r1)",4);
        p=emit(out,p,"e_lwz r0,4(r1)",4);
        p=emit(out,p,"e_add16i r1,r1,64",4);
        p=emit(out,p,"se_blr",2);
        return out.toByteArray();
    }

    private static class BlockOp {
        String label;
        String line;
        String target;
        byte[] raw;
        int len;
        BlockOp(String label,String line,String target,byte[] raw,int len){
            this.label=label;this.line=line;this.target=target;this.raw=raw;this.len=len;
        }
    }

    private BlockOp mark(String label){return new BlockOp(label,null,null,null,0);}
    private BlockOp ins(String line,int len){return new BlockOp(null,line,null,null,len);}
    private BlockOp br(String prefix,String target,int len){return new BlockOp(null,prefix,target,null,len);}
    private BlockOp raw(byte[] bytes){return new BlockOp(null,null,null,bytes,bytes==null?0:bytes.length);}

    private byte[] assembleBlock(long base,BlockOp... ops) throws Exception {
        LinkedHashMap<String,Long> labels=new LinkedHashMap<String,Long>();
        long cursor=base;
        for(BlockOp op:ops){
            if(op.label!=null){
                if(labels.put(op.label,Long.valueOf(cursor))!=null)
                    throw new IllegalStateException("Duplicate block label: "+op.label);
            }
            else cursor+=op.len;
        }
        ByteArrayOutputStream out=new ByteArrayOutputStream();
        Address p=addr(base);
        for(BlockOp op:ops){
            if(op.label!=null)continue;
            if(op.raw!=null){
                p=emitRaw(out,p,op.raw);
                continue;
            }
            String line=op.line;
            if(op.target!=null){
                Long t=labels.get(op.target);
                if(t==null)throw new IllegalStateException("Missing block label: "+op.target);
                line=line+hex(t.longValue());
            }
            p=emit(out,p,line,op.len);
        }
        return out.toByteArray();
    }

    private byte[] buildStateHelper() throws Exception {
        return assembleBlock(STATE_HELPER,
            ins("e_stwu r1,-16(r1)",4),
            ins("se_mflr r0",2),
            ins("e_stw r0,12(r1)",4),
            ins("e_bl "+hex(CRITICAL_ENTER),4),

            ins("e_lis r11,"+hi16(SCRATCH_WORD),4),
            ins("e_add16i r11,r11,"+lo16(SCRATCH_WORD),4),
            ins("e_lwz r12,0(r11)",4),
            ins("e_cmp16i. r12,0x0",4),
            br("e_beq cr0,","UNLOCK",4),
            ins("e_cmpl16i. r12,"+imm16(DONE_STATE),4),
            br("e_beq cr0,","UNLOCK",4),

            ins("e_lis r10,"+hi16(ACTION_WORD),4),
            ins("e_add16i r10,r10,"+lo16(ACTION_WORD),4),
            ins("e_lwz r0,0(r10)",4),

            ins("e_rlwinm r7,r12,0x0,"+bitCrPos(CLEAR_BASELINE)+","+bitCrPos(CLEAR_BASELINE),4),


            ins("se_cmpi r7,0x0",2),
            br("e_bne cr0,","CHECK_EPISODE",4),
            ins("e_rlwinm r7,r0,0x0,"+bitCrPos(ACTION_0800)+","+bitCrPos(ACTION_0800),4),

            ins("se_cmpi r7,0x0",2),
            br("e_bne cr0,","COUNTDOWN",4),
            ins("e_rlwinm r7,r0,0x0,"+bitCrPos(ACTION_100000)+","+bitCrPos(ACTION_100000),4),

            ins("se_cmpi r7,0x0",2),
            br("e_bne cr0,","COUNTDOWN",4),
            ins("e_rlwinm r7,r0,0x0,"+bitCrPos(ACTION_400000)+","+bitCrPos(ACTION_400000),4),

            ins("se_cmpi r7,0x0",2),
            br("e_bne cr0,","COUNTDOWN",4),
            ins("e_li r7,"+imm16(CLEAR_BASELINE),4),

            ins("or r12,r12,r7",4),

            mark("CHECK_EPISODE"),
            ins("e_rlwinm r7,r12,0x0,"+bitCrPos(CMD32_EPISODE)+","+bitCrPos(CMD32_EPISODE),4),

            ins("se_cmpi r7,0x0",2),
            br("e_beq cr0,","COUNTDOWN",4),
            ins("e_rlwinm r7,r0,0x0,"+bitCrPos(ACTION_0800)+","+bitCrPos(ACTION_0800),4),

            ins("se_cmpi r7,0x0",2),
            br("e_beq cr0,","SEEN_100000_TEST",4),
            ins("e_li r7,"+imm16(SEEN_0800),4),

            ins("or r12,r12,r7",4),
            mark("SEEN_100000_TEST"),
            ins("e_rlwinm r7,r0,0x0,"+bitCrPos(ACTION_100000)+","+bitCrPos(ACTION_100000),4),

            ins("se_cmpi r7,0x0",2),
            br("e_beq cr0,","SEEN_400000_TEST",4),
            ins("e_li r7,"+imm16(SEEN_100000),4),

            ins("or r12,r12,r7",4),
            mark("SEEN_400000_TEST"),
            ins("e_rlwinm r7,r0,0x0,"+bitCrPos(ACTION_400000)+","+bitCrPos(ACTION_400000),4),

            ins("se_cmpi r7,0x0",2),
            br("e_beq cr0,","COUNTDOWN",4),
            ins("e_li r7,"+imm16(SEEN_400000),4),

            ins("or r12,r12,r7",4),

            mark("COUNTDOWN"),
            ins("e_rlwinm r8,r12,0x0,0x17,0x1f",4),
            ins("e_cmp16i. r8,0x0",4),
            br("e_beq cr0,","ELAPSED",4),
            ins("e_add16i r8,r8,-1",4),
            ins("e_rlwinm r12,r12,0x0,0x0,0x16",4),
            ins("or r12,r12,r8",4),
            ins("e_cmp16i. r8,0x0",4),
            br("e_bne cr0,","COMMIT",4),

            mark("ELAPSED"),
            ins("e_li r7,"+imm16(MINIMUM_ELAPSED),4),

            ins("or r12,r12,r7",4),
            ins("e_rlwinm r7,r12,0x0,"+bitCrPos(CLEAR_BASELINE)+","+bitCrPos(CLEAR_BASELINE),4),

            ins("se_cmpi r7,0x0",2),
            br("e_beq cr0,","COMMIT",4),
            ins("e_rlwinm r7,r12,0x0,"+bitCrPos(CMD32_EPISODE)+","+bitCrPos(CMD32_EPISODE),4),

            ins("se_cmpi r7,0x0",2),
            br("e_beq cr0,","COMMIT",4),
            // Nonzero observed subset: any of state bits11..13 qualifies.
            ins("e_rlwinm r7,r12,0x0,"+bitCrPos(SEEN_0800)+","+bitCrPos(SEEN_0800),4),

            ins("se_cmpi r7,0x0",2),
            br("e_bne cr0,","SEEN_ANY",4),
            ins("e_rlwinm r7,r12,0x0,"+bitCrPos(SEEN_100000)+","+bitCrPos(SEEN_100000),4),

            ins("se_cmpi r7,0x0",2),
            br("e_bne cr0,","SEEN_ANY",4),
            ins("e_rlwinm r7,r12,0x0,"+bitCrPos(SEEN_400000)+","+bitCrPos(SEEN_400000),4),

            ins("se_cmpi r7,0x0",2),
            br("e_beq cr0,","COMMIT",4),

            mark("SEEN_ANY"),
            ins("e_rlwinm r7,r0,0x0,"+bitCrPos(ACTION_0800)+","+bitCrPos(ACTION_0800),4),

            ins("se_cmpi r7,0x0",2),
            br("e_bne cr0,","COMMIT",4),
            ins("e_rlwinm r7,r0,0x0,"+bitCrPos(ACTION_100000)+","+bitCrPos(ACTION_100000),4),

            ins("se_cmpi r7,0x0",2),
            br("e_bne cr0,","COMMIT",4),
            ins("e_rlwinm r7,r0,0x0,"+bitCrPos(ACTION_400000)+","+bitCrPos(ACTION_400000),4),

            ins("se_cmpi r7,0x0",2),
            br("e_bne cr0,","COMMIT",4),

            // Exact terminal write without any high immediate encoding.
            ins("e_li r12,"+imm16(DONE_STATE),4),
            ins("e_stw r12,0(r11)",4),
            ins("e_lis r6,"+hi16(AP318_BYTE),4),
            ins("e_add16i r6,r6,"+lo16(AP318_BYTE),4),
            ins("e_lbz r5,0(r6)",4),
            ins("e_and2i. r5,0x1f",4),
            ins("e_or2i r5,0x40",4),
            ins("e_stb r5,0(r6)",4),
            br("e_b ","UNLOCK",4),

            mark("COMMIT"),
            ins("e_stw r12,0(r11)",4),
            mark("UNLOCK"),
            ins("e_bl "+hex(CRITICAL_EXIT),4),
            ins("e_lwz r0,12(r1)",4),
            ins("se_mtlr r0",2),
            ins("e_add16i r1,r1,16",4),
            ins("se_blr",2)
        );
    }

    private byte[] buildCmd32Wrapper() throws Exception {
        return assembleBlock(CMD32_WRAPPER,
            ins("e_stwu r1,-32(r1)",4),
            ins("se_mflr r0",2),
            ins("e_stw r0,28(r1)",4),
            ins("e_bl "+hex(CRITICAL_ENTER),4),
            ins("e_lis r11,"+hi16(SCRATCH_WORD),4),
            ins("e_add16i r11,r11,"+lo16(SCRATCH_WORD),4),
            ins("e_lwz r12,0(r11)",4),
            ins("e_cmp16i. r12,0x0",4),
            br("e_beq cr0,","PRE_UNLOCK",4),
            ins("e_cmpl16i. r12,"+imm16(DONE_STATE),4),
            br("e_beq cr0,","PRE_UNLOCK",4),

            ins("e_rlwinm r7,r12,0x0,"+bitCrPos(CLEAR_BASELINE)+","+bitCrPos(CLEAR_BASELINE),4),


            ins("se_cmpi r7,0x0",2),
            br("e_bne cr0,","MARK_EPISODE",4),
            ins("e_lis r10,"+hi16(ACTION_WORD),4),
            ins("e_add16i r10,r10,"+lo16(ACTION_WORD),4),
            ins("e_lwz r0,0(r10)",4),
            ins("e_rlwinm r7,r0,0x0,"+bitCrPos(ACTION_0800)+","+bitCrPos(ACTION_0800),4),

            ins("se_cmpi r7,0x0",2),
            br("e_bne cr0,","PRE_UNLOCK",4),
            ins("e_rlwinm r7,r0,0x0,"+bitCrPos(ACTION_100000)+","+bitCrPos(ACTION_100000),4),

            ins("se_cmpi r7,0x0",2),
            br("e_bne cr0,","PRE_UNLOCK",4),
            ins("e_rlwinm r7,r0,0x0,"+bitCrPos(ACTION_400000)+","+bitCrPos(ACTION_400000),4),

            ins("se_cmpi r7,0x0",2),
            br("e_bne cr0,","PRE_UNLOCK",4),
            ins("e_li r7,"+imm16(CLEAR_BASELINE),4),

            ins("or r12,r12,r7",4),

            mark("MARK_EPISODE"),
            ins("e_rlwinm r7,r12,0x0,"+bitCrPos(CMD32_EPISODE)+","+bitCrPos(CMD32_EPISODE),4),

            ins("se_cmpi r7,0x0",2),
            br("e_bne cr0,","PRE_STORE",4),
            ins("e_li r7,"+imm16(CMD32_EPISODE),4),

            ins("or r12,r12,r7",4),
            mark("PRE_STORE"),
            ins("e_stw r12,0(r11)",4),

            mark("PRE_UNLOCK"),
            ins("e_bl "+hex(CRITICAL_EXIT),4),
            ins("e_bl "+hex(VEHICLE_CONFIG_CHECK),4),
            ins("e_bl "+hex(CRITICAL_ENTER),4),
            ins("e_lis r11,"+hi16(SCRATCH_WORD),4),
            ins("e_add16i r11,r11,"+lo16(SCRATCH_WORD),4),
            ins("e_lwz r12,0(r11)",4),
            ins("e_rlwinm r7,r12,0x0,"+bitCrPos(CMD32_EPISODE)+","+bitCrPos(CMD32_EPISODE),4),

            ins("se_cmpi r7,0x0",2),
            br("e_beq cr0,","POST_UNLOCK",4),
            ins("e_cmpl16i. r12,"+imm16(DONE_STATE),4),
            br("e_beq cr0,","POST_UNLOCK",4),
            ins("e_lis r10,"+hi16(ACTION_WORD),4),
            ins("e_add16i r10,r10,"+lo16(ACTION_WORD),4),
            ins("e_lwz r0,0(r10)",4),
            ins("e_rlwinm r7,r0,0x0,"+bitCrPos(ACTION_0800)+","+bitCrPos(ACTION_0800),4),

            ins("se_cmpi r7,0x0",2),
            br("e_beq cr0,","POST_100000",4),
            ins("e_li r7,"+imm16(SEEN_0800),4),

            ins("or r12,r12,r7",4),
            mark("POST_100000"),
            ins("e_rlwinm r7,r0,0x0,"+bitCrPos(ACTION_100000)+","+bitCrPos(ACTION_100000),4),

            ins("se_cmpi r7,0x0",2),
            br("e_beq cr0,","POST_400000",4),
            ins("e_li r7,"+imm16(SEEN_100000),4),

            ins("or r12,r12,r7",4),
            mark("POST_400000"),
            ins("e_rlwinm r7,r0,0x0,"+bitCrPos(ACTION_400000)+","+bitCrPos(ACTION_400000),4),

            ins("se_cmpi r7,0x0",2),
            br("e_beq cr0,","POST_STORE",4),
            ins("e_li r7,"+imm16(SEEN_400000),4),

            ins("or r12,r12,r7",4),
            mark("POST_STORE"),
            ins("e_stw r12,0(r11)",4),

            mark("POST_UNLOCK"),
            ins("e_bl "+hex(CRITICAL_EXIT),4),
            ins("e_lwz r0,28(r1)",4),
            ins("se_mtlr r0",2),
            ins("e_add16i r1,r1,32",4),
            ins("se_blr",2)
        );
    }

    private Address emit(ByteArrayOutputStream out,Address p,String line,int expected)
            throws Exception {
        byte[] b=assembleLine(p,line,expected);
        out.write(b,0,b.length);
        return p.add(b.length);
    }

    private Address emitRaw(ByteArrayOutputStream out,Address p,byte[] b)
            throws Exception {
        if(b==null || b.length==0)
            throw new IllegalStateException("Attempt to emit empty raw block at "+p);
        out.write(b,0,b.length);
        return p.add(b.length);
    }

    private void validateV497R1Baseline(byte[] image,Contract c) throws Exception {
        if(image.length!=IMAGE_SIZE)
            throw new IllegalStateException(
                "Input length is "+image.length+"; expected exact 2 MiB.");
        String sha=sha256(image);
        if(!V497R1_INPUT_SHA256.equalsIgnoreCase(sha))
            throw new IllegalStateException(
                "V617R2R2 requires exact V497R1 input BIN. SHA256="+sha);

        long appSize=getU32BE(image,APP_SIZE_ADDRESS);
        long appInv=getU32BE(image,APP_SIZE_INV_ADDRESS);
        if(appSize!=EXPECTED_APP_SIZE || appInv!=EXPECTED_APP_SIZE_INV ||
           appInv!=((~appSize)&0xffffffffL))
            throw new IllegalStateException(
                "V497R1 application header size/complement contract failed.");
        long stored=getU32BE(image,APP_CRC_ADDRESS);
        long calculated=calculateApplicationCrc(
            slice(image,APP_START,EXPECTED_APP_SIZE));
        if(stored!=STOCK_APP_CRC || calculated!=STOCK_APP_CRC)
            throw new IllegalStateException(String.format(Locale.ROOT,
                "V497R1 CRC contract failed. stored=0x%08X calculated=0x%08X",
                stored,calculated));

        requireBytes(image,STORED_AUTOPILOT_BYTE,bytes(0x30),
            "stored internal.dat autopilot remains ASCII 0");
        requireBytes(image,RUNTIME_FORCE,bytes(0x48,0x20),
            "V497R1 runtime AP2 force");
        requireBytes(image,PREPSLEEP_PATCH,bytes(0x00,0x04,0x44,0x00),
            "V497R1 PrepSleep suppression");
        requireBytes(image,COMMAND33_SIGNATURE,COMMAND33_MARKER,
            "V497R1 command33 marker");
        requireBytes(image,PENDING_PRIMARY,NOP4,
            "V497R1 pending primary suppression");
        requireBytes(image,PENDING_MIRROR,NOP4,
            "V497R1 pending mirror suppression");
        requireBytes(image,EVENT19D_CALL,NOP4,
            "V497R1 event19D suppression");
        requireBytes(image,CC1701_SELECTOR,NOP4,
            "V497R1 CC1701 final selector suppression");

        byte[] apTrialBranch=assembleLine(addr(APTRIAL_GODOWN_CALL),
            "e_b "+hex(APTRIAL_CLEANUP),4);
        requireBytes(image,APTRIAL_GODOWN_CALL,apTrialBranch,
            "V493/V497R1 AP-trial cleanup branch");
        if(equalsBytes(slice(image,A2BC_BRANCH,2),bytes(0xE6,0x34)))
            throw new IllegalStateException(
                "A2BC 0x88438 unexpectedly reverted to stock branch.");

        requireBytes(image,INSERT_368,c.insert368,"stock CAN368 AP insert");
        requireBytes(image,INSERT_318,c.insert318,"stock CAN318 AP insert");
        requireBytes(image,INSERT_398,c.insert398,"stock CAN398 AP insert");
        requireBytes(image,STORE_368,c.store368,"stock CAN368 AP store");
        requireBytes(image,STORE_398,c.store398,"stock CAN398 AP store");
        requireBytes(image,STORE_318,c.store318,"stock CAN318 AP store");
        requireBytes(image,ONE_HZ,c.oneHzOriginal,"stock oneHz prefix");
        requireBytes(image,WAKE_EDGE_SEND_CALL,c.wakeEdgeOriginal,
            "stock A47EA falling-edge F7942 call");
        requireBytes(image,COMMAND32_HANDLER,c.command32Entry,
            "stock command32 handler entry retained in V497R1");
        requireBytes(image,COMMAND32_CHECK_CALL,c.command32CheckCall,
            "stock command32 -> 0x88340 call retained in V497R1");
        requireBytes(image,SELECTOR_ENABLE_LOAD,c.selectorEnableLoad,
            "stock 0x88396 selector-enable load retained in V497R1");

        requireZeroRange(image,AP_WRAPPER,AP_WRAPPER_RESERVED,
            "V617R2R2 AP wrapper cave");
        requireZeroRange(image,ONEHZ_WRAPPER,ONEHZ_WRAPPER_RESERVED,
            "V617R2R2 oneHz wrapper cave");
        requireZeroRange(image,WAKE_WRAPPER,WAKE_WRAPPER_RESERVED,
            "V617R2R2 wake wrapper cave");
        requireZeroRange(image,STATE_HELPER,STATE_HELPER_RESERVED,
            "V617R2R2 state helper cave");
        requireZeroRange(image,CMD32_WRAPPER,CMD32_WRAPPER_RESERVED,
            "V617R2R2 command32 wrapper cave");
    }

    private void validateOutput(byte[] baseline,byte[] patched,Contract c,
            byte[] compensation) {
        requireBytes(patched,INSERT_368,c.apHook,
            "V617R2R2 AP publication detour");
        requireBytes(patched,ONE_HZ,c.oneHzHook,
            "V617R2R2 oneHz countdown detour");
        requireBytes(patched,WAKE_EDGE_SEND_CALL,c.wakeEdgeHook,
            "V617R2R2 A47EA falling-edge wake detour");
        requireBytes(patched,AP_WRAPPER,c.apWrapper,"V617R2R2 AP wrapper");
        requireBytes(patched,ONEHZ_WRAPPER,c.oneHzWrapper,
            "V617R2R2 oneHz wrapper");
        requireBytes(patched,WAKE_WRAPPER,c.wakeWrapper,
            "V617R2R2 wake wrapper");
        requireBytes(patched,STATE_HELPER,c.stateHelper,
            "V617R2R2 state helper");
        requireBytes(patched,CMD32_EPISODE_CALL,c.command32Hook,
            "V617R2R2 command32 episode detour");
        requireBytes(patched,CMD32_WRAPPER,c.cmd32Wrapper,
            "V617R2R2 command32 wrapper");
        requireBytes(patched,COMPENSATION_ADDRESS,compensation,
            "V617R2R2 CRC compensation");

        // Preserve command32 handler/selector while validating only the exact episode-call detour.
        requireBytes(patched,COMMAND32_HANDLER,
            slice(baseline,COMMAND32_HANDLER,c.command32Entry.length),
            "V617R2R2 command32 handler unchanged");
        requireBytes(patched,COMMAND32_CHECK_CALL,c.command32Hook,
            "V617R2R2 command32 callsite detoured to episode wrapper");
        requireBytes(patched,SELECTOR_ENABLE_LOAD,
            slice(baseline,SELECTOR_ENABLE_LOAD,c.selectorEnableLoad.length),
            "V617R2R2 selector-enable load unchanged");

        for(long[] g:new long[][]{
                {STORED_AUTOPILOT_BYTE,1},{RUNTIME_FORCE,2},{PREPSLEEP_PATCH,4},
                {COMMAND33_SIGNATURE,8},{A2BC_BRANCH,2},{PENDING_PRIMARY,4},
                {PENDING_MIRROR,4},{EVENT19D_CALL,4},{APTRIAL_GODOWN_CALL,4},
                {CC1701_SELECTOR,4},{STORE_368,4},{STORE_398,4},{STORE_318,4}}){
            requireBytes(patched,g[0],slice(baseline,g[0],(int)g[1]),
                "preserved V497R1 guard "+hex(g[0]));
        }

        long stored=getU32BE(patched,APP_CRC_ADDRESS);
        long calculated=calculateApplicationCrc(
            slice(patched,APP_START,EXPECTED_APP_SIZE));
        if(stored!=STOCK_APP_CRC || calculated!=STOCK_APP_CRC)
            throw new IllegalStateException(String.format(Locale.ROOT,
                "V617R2R2 CRC mismatch. stored=0x%08X calculated=0x%08X",
                stored,calculated));

        for(int i=0;i<IMAGE_SIZE;i++){
            if(baseline[i]==patched[i])continue;
            long a=i&0xffffffffL;
            boolean allowed=
                inRange(a,COMPENSATION_ADDRESS,4) ||
                inRange(a,INSERT_368,4) ||
                inRange(a,ONE_HZ,c.oneHzSpan) ||
                inRange(a,AP_WRAPPER,AP_WRAPPER_RESERVED) ||
                inRange(a,ONEHZ_WRAPPER,ONEHZ_WRAPPER_RESERVED) ||
                inRange(a,WAKE_WRAPPER,WAKE_WRAPPER_RESERVED) ||
                inRange(a,STATE_HELPER,STATE_HELPER_RESERVED) ||
                inRange(a,CMD32_EPISODE_CALL,4) ||
                inRange(a,CMD32_WRAPPER,CMD32_WRAPPER_RESERVED) ||
                inRange(a,WAKE_EDGE_SEND_CALL,4);
            if(!allowed)
                throw new IllegalStateException(
                    "Unexpected V617R2R2 changed byte at "+hex(a)+".");
        }
    }

    private void writeReport(File report,File input,String stockSha,
            byte[] baseline,byte[] patched,Contract c,byte[] compensation)
            throws Exception {
        int changed=0; List<String> ranges=new ArrayList<String>(); int start=-1,last=-1;
        for(int i=0;i<IMAGE_SIZE;i++){
            if(baseline[i]==patched[i])continue; changed++;
            if(start<0){start=last=i;} else if(i==last+1)last=i;
            else {ranges.add(hex(start)+".."+hex(last));start=last=i;}
        }
        if(start>=0)ranges.add(hex(start)+".."+hex(last));

        try(BufferedWriter w=new BufferedWriter(new OutputStreamWriter(
                new FileOutputStream(report),StandardCharsets.UTF_8))){
            w.write("Tesla Gateway V497R1 AP318 Serialized Reconciliation V617R2R2\r\n");
            w.write("=============================================================\r\n\r\n");
            w.write("BENCH/STATIONARY ONLY. NOT FOR ROAD USE.\r\n");
            w.write("Keep rollback image immediately available.\r\n\r\n");

            w.write("Static basis\r\n------------\r\n");
            w.write("V618: F7380/F73A8 proven nest-aware interrupt critical pair with no calls/waits/token.\r\n");
            w.write("V619R1: 0x77226 -> 0x88340 is a clean episode marker; ACTION sets conditional subsets; AP publication corridor 0x87128..0x8713C has zero external interior entries.\r\n\r\n");

            w.write("State encoding @0x40014E2C\r\n---------------------------\r\n");
            w.write("bits0..8 countdown; bit9 CLEAR_BASELINE; bit10 CMD32_EPISODE; bits11..13 observed ACTION 0x800/0x100000/0x400000; bit14 MINIMUM_ELAPSED; DONE uses exact terminal sentinel 0x7FFF.\r\n");
            w.write("Release = elapsed && baseline && episode && observed_subset!=0 && all exact ACTION bits now clear.\r\n");
            w.write("Full 0x00500800 is NOT required to have been set concurrently; the observed conditional subset is accumulated dynamically.\r\n\r\n");

            w.write("Concurrency\r\n-----------\r\n");
            w.write("All session-state writers and direct CAN318 AP-byte transitions use F7380/F73A8.\r\n");
            w.write("apply_autopilot_config 0x87128..0x8713C is replayed under the same critical pair through the final CAN318 store before rejoin at 0x8713E.\r\n");
            w.write("The command32 wrapper releases the critical section before calling stock 0x88340, then re-enters only for immediate ACTION subset capture.\r\n\r\n");

            w.write("Hooks/wrappers\r\n--------------\r\n");
            w.write("0x00087128 -> "+hex(AP_WRAPPER)+" serialized six-instruction AP publication corridor\r\n");
            w.write("0x0006F99C -> "+hex(ONEHZ_WRAPPER)+" oneHz pre-body state helper; span="+c.oneHzSpan+" bytes\r\n");
            w.write("0x000A4ADA -> "+hex(WAKE_WRAPPER)+" observed A47EA falling-edge re-arm wrapper\r\n");
            w.write("0x00077226 -> "+hex(CMD32_WRAPPER)+" command32 episode wrapper; stock 0x88340 called exactly once\r\n");
            w.write("state helper @"+hex(STATE_HELPER)+" length="+c.stateHelper.length+" bytes\r\n");
            w.write("AP wrapper length="+c.apWrapper.length+"; oneHz="+c.oneHzWrapper.length+"; wake="+c.wakeWrapper.length+"; cmd32="+c.cmd32Wrapper.length+"\r\n");
            w.write("CRC compensation @0x00125800: "+toHex(compensation)+"\r\n\r\n");

            w.write("Explicit non-changes\r\n--------------------\r\n");
            w.write("- Runtime AP2 force retained; CAN368/CAN398 AP2 retained.\r\n");
            w.write("- command32 handler logic retained except exact 0x77226 call detour.\r\n");
            w.write("- stock process_vehicle_config_check 0x88340 body unchanged and called once.\r\n");
            w.write("- command32 reply, reset/watchdog and V596R1 observer result unchanged.\r\n\r\n");

            w.write("Validation\r\n----------\r\n");
            w.write("Input: "+input.getAbsolutePath()+"\r\n");
            w.write("Stock Ghidra SHA256: "+stockSha+"\r\n");
            w.write("Input V497R1 SHA256: "+sha256(baseline)+"\r\n");
            w.write("Changed byte count: "+changed+"\r\n");
            w.write("Changed ranges: "+String.join(", ",ranges)+"\r\n");
            w.write(String.format(Locale.ROOT,"Stored/calculated app CRC: 0x%08X / 0x%08X\r\n",
                getU32BE(patched,APP_CRC_ADDRESS),calculateApplicationCrc(slice(patched,APP_START,EXPECTED_APP_SIZE))));
            w.write("Patched SHA256: "+sha256(patched)+"\r\n\r\n");

            w.write("Stationary test order\r\n---------------------\r\n");
            w.write("1. Do not flash until these generated artifacts have been independently validated.\r\n");
            w.write("2. On initial boot, confirm CAN318 AP0 phase (visible AP2 may be absent as in V580). While AP0 remains active, initiate Software Check.\r\n");
            w.write("3. AP2 cannot be released until >=300 oneHz samples, a post-session clear baseline, the exact command32 episode, a nonzero conditional ACTION subset, and later all-clear have all occurred.\r\n");
            w.write("4. Record AP2 return/no-return and reboot/no-reboot; preserve SD logs.\r\n");
            w.write("5. Then allow a genuine rest period. After wake, treat the test as covered only if the observed A47EA re-arm produces the AP0 phase. While that AP0 phase is active, initiate Software Check again.\r\n");
            w.write("6. If an observed wake does not show AP0 re-arm, classify A47EA coverage as unproven for that wake; do not count it as a negative experiment.\r\n\r\n");

            w.write("Interpretation\r\n--------------\r\n");
            w.write("AP2 returns after qualified session reconciliation and no later reboot occurs: supports a session-scoped CAN318 publication/reconciliation window; it does not identify either V596R1-blinded local powerRails observer as causal.\r\n");
            w.write("Qualified AP0 re-arm + AP2 return + reboot persists: this combined window is causally negative; do not widen it again without new evidence.\r\n");
            w.write("AP2 never returns: the required baseline/episode/action/completion contract did not complete; inspect logs/state evidence rather than treating timing as insufficient.\r\n");
        }
    }

    private String imm16(long v){return String.format(Locale.ROOT,"0x%X",v&0xffffL);}
    private String hi16(long v){return String.format(Locale.ROOT,"0x%X",(v>>>16)&0xffffL);}
    private String lo16(long v){return String.format(Locale.ROOT,"0x%X",v&0xffffL);}
    private String bitCrPos(long oneBitMask){
        if(oneBitMask==0 || (oneBitMask&(oneBitMask-1))!=0)
            throw new IllegalArgumentException("Mask is not one bit: "+Long.toHexString(oneBitMask));
        int logical=Long.numberOfTrailingZeros(oneBitMask);
        return String.format(Locale.ROOT,"0x%X",31-logical);
    }

    private void requireInstructionText(long site,String expected,String label){
        Instruction i=getInstructionAt(addr(site));
        String actual=i==null?"":i.toString().trim().toLowerCase(Locale.ROOT);
        if(!actual.equals(expected.toLowerCase(Locale.ROOT)))
            throw new IllegalStateException(label+" contract failed @"+hex(site)+": "+actual);
    }

    private void requireNoExternalPublicationInteriorReferences(){
        for(long a=INSERT_318;a<=STORE_318;){
            Instruction i=getInstructionAt(addr(a));
            if(i==null)throw new IllegalStateException("Missing publication instruction @"+hex(a));
            ReferenceIterator it=currentProgram.getReferenceManager().getReferencesTo(i.getAddress());
            while(it.hasNext()){
                Reference r=it.next();
                long from=r.getFromAddress().getOffset()&0xffffffffL;
                if(from<INSERT_368 || from>STORE_318)
                    throw new IllegalStateException(
                        "External reference enters serialized AP publication corridor @"+
                        hex(a)+" from "+hex(from)+" ("+r.getReferenceType()+")");
            }
            a+=i.getLength();
        }
    }

    private void requireStoreTarget(long site,long target) {
        Instruction i=getInstructionAt(addr(site));
        if(i==null || !isStore(i) || !referencesTarget(i,target))
            throw new IllegalStateException(
                "Store target contract failed at "+hex(site)+" -> "+hex(target)+": "+
                (i==null?"<none>":i.toString()));
    }

    private void requireZeroRange(byte[] image,long start,int len,String label) {
        for(int i=0;i<len;i++)
            if(image[(int)start+i]!=0)
                throw new IllegalStateException(
                    label+" is not zero at "+hex(start+i)+"; refusing cave reuse.");
    }

    private boolean referencesTarget(Instruction ins,long target) {
        try {
            Reference[] rr=ins.getReferencesFrom();
            if(rr!=null)for(Reference r:rr)
                if((r.getToAddress().getOffset()&0xffffffffL)==
                   (target&0xffffffffL))return true;
        }
        catch(Throwable ignored) {}
        return false;
    }

    private boolean isStore(Instruction i) {
        String m=lower(i.getMnemonicString());
        return m.startsWith("st")||m.startsWith("e_st")||m.startsWith("se_st");
    }

    private long directCallTarget(Instruction i) {
        try {
            if(i==null||i.getFlowType()==null||!i.getFlowType().isCall()||
               i.getFlowType().isComputed())return -1;
            Address[] f=i.getFlows();
            return f!=null&&f.length==1?
                (f[0].getOffset()&0xffffffffL):-1;
        }
        catch(Throwable ignored) {return -1;}
    }

    private byte[] assembleVariableLine(Address at,String line) throws Exception {
        Assembler languageAssembler=Assemblers.getAssembler(currentProgram.getLanguage());
        Assembler programAssembler=Assemblers.getAssembler(currentProgram);
        Exception languageFailure=null,programFailure=null;
        try {
            byte[] b=languageAssembler.assembleLine(at,line);
            if(b!=null&&b.length>0)return b;
        }
        catch(Exception ex){languageFailure=ex;}
        try {
            byte[] b=programAssembler.assembleLine(at,line);
            if(b!=null&&b.length>0)return b;
        }
        catch(Exception ex){programFailure=ex;}
        byte[] recovered=recoverAnyConcreteResolutionBytes(programFailure);
        if(recovered==null)recovered=recoverAnyConcreteResolutionBytes(languageFailure);
        if(recovered!=null)return recovered;
        throw new IllegalStateException(
            "Could not assemble at "+at+" line '"+line+"'.\nLanguage: "+
            safeMessage(languageFailure)+"\nProgram: "+safeMessage(programFailure));
    }

    private byte[] assembleLine(Address at,String line,int expected) throws Exception {
        byte[] b=assembleVariableLine(at,line);
        if(b.length!=expected)
            throw new IllegalStateException(
                "Assembled '"+line+"' to "+b.length+" bytes; expected "+expected+".");
        return b;
    }

    private byte[] recoverAnyConcreteResolutionBytes(Exception failure) {
        if(failure==null)return null;
        String message=safeMessage(failure);
        Set<String> candidates=new LinkedHashSet<String>();
        int searchFrom=0;
        while(true) {
            int marker=message.indexOf("ins:",searchFrom);
            if(marker<0)break;
            int cursor=marker+4;
            StringBuilder compact=new StringBuilder();
            while(cursor<message.length()) {
                char c=message.charAt(cursor);
                if(Character.digit(c,16)>=0)compact.append(c);
                else if(Character.isWhitespace(c)||c==':'||c=='['||c==']'){}
                else break;
                cursor++;
            }
            if(compact.length()>=4 && (compact.length()&1)==0)
                candidates.add(compact.toString());
            searchFrom=marker+4;
        }
        for(String value:candidates) {
            try {
                byte[] b=new byte[value.length()/2];
                for(int i=0;i<b.length;i++)
                    b[i]=(byte)Integer.parseInt(
                        value.substring(i*2,i*2+2),16);
                if(b.length>0)return b;
            }
            catch(Throwable ignored){}
        }
        return null;
    }

    private String safeMessage(Throwable t) {
        if(t==null)return "";
        String m=t.getMessage();
        return m==null||m.length()==0?t.toString():m;
    }

    private byte[] readWholeFile(File f) throws Exception {
        if(f.length()!=IMAGE_SIZE)
            throw new IllegalStateException("Selected BIN is not exactly 2 MiB.");
        byte[] b=new byte[IMAGE_SIZE];
        try(BufferedInputStream in=new BufferedInputStream(new FileInputStream(f))) {
            int offset=0;
            while(offset<b.length) {
                int n=in.read(b,offset,b.length-offset);
                if(n<0)break;
                offset+=n;
            }
            if(offset!=b.length)
                throw new IllegalStateException("Short read from selected BIN.");
        }
        return b;
    }

    private void writeBinary(File f,byte[] b) throws Exception {
        try(BufferedOutputStream out=new BufferedOutputStream(new FileOutputStream(f))) {
            out.write(b);
        }
        if(f.length()!=IMAGE_SIZE)
            throw new IllegalStateException("Written BIN size mismatch.");
    }

    private void writeS19(File f,byte[] image) throws Exception {
        try(BufferedWriter w=new BufferedWriter(new OutputStreamWriter(
                new FileOutputStream(f),StandardCharsets.US_ASCII))) {
            for(int a=0;a<image.length;a+=SREC_DATA_LENGTH) {
                int l=Math.min(SREC_DATA_LENGTH,image.length-a);
                w.write(makeSRecord(a,image,a,l));
                w.write("\r\n");
            }
        }
    }

    private String makeSRecord(int a,byte[] image,int off,int len) {
        int addressBytes=a<=0xffff?2:3;
        char type=addressBytes==2?'1':'2';
        int count=addressBytes+len+1;
        int sum=count;
        StringBuilder b=new StringBuilder();
        b.append('S').append(type); appendHexByte(b,count);
        for(int shift=(addressBytes-1)*8;shift>=0;shift-=8) {
            int v=(a>>>shift)&0xff; appendHexByte(b,v); sum+=v;
        }
        for(int i=0;i<len;i++) {
            int v=image[off+i]&0xff;appendHexByte(b,v);sum+=v;
        }
        appendHexByte(b,(~sum)&0xff);
        return b.toString();
    }

    private void appendHexByte(StringBuilder b,int v) {
        b.append(String.format(Locale.ROOT,"%02X",v&0xff));
    }

    private void requireEmptyDirectory(File d) {
        if(!d.exists()&&!d.mkdirs())
            throw new IllegalStateException("Could not create output directory.");
        File[] f=d.listFiles();
        if(f!=null&&f.length!=0)
            throw new IllegalStateException(
                "V617R2R2 BIN/S19 builder requires a NEW EMPTY output directory.");
    }

    private byte[] solveFourBytePatch(byte[] source,int offset,long target) {
        byte[] work=source.clone();
        work[0]=0;work[1]=0;work[2]=0;work[3]=0;
        for(int i=0;i<4;i++)work[offset+i]=0;
        long base=rawCrc(work);
        long rhs=(target^base)&0xffffffffL;
        long[] basisVector=new long[32];
        int[] basisMask=new int[32];
        for(int variable=0;variable<32;variable++) {
            int byteIndex=variable/8;
            int bitInByte=7-(variable%8);
            work[offset+byteIndex]=(byte)(1<<bitInByte);
            long vector=(rawCrc(work)^base)&0xffffffffL;
            int mask=1<<variable;
            work[offset+byteIndex]=0;
            for(int bit=31;bit>=0;bit--) {
                long q=1L<<bit;
                if((vector&q)==0)continue;
                if(basisVector[bit]==0) {
                    basisVector[bit]=vector;
                    basisMask[bit]=mask;
                    vector=0;
                    break;
                }
                vector^=basisVector[bit];
                mask^=basisMask[bit];
            }
            if(vector!=0)return null;
        }
        int solution=0;
        long remaining=rhs;
        for(int bit=31;bit>=0;bit--) {
            long q=1L<<bit;
            if((remaining&q)==0)continue;
            if(basisVector[bit]==0)return null;
            remaining^=basisVector[bit];
            solution^=basisMask[bit];
        }
        if(remaining!=0)return null;
        byte[] patch=new byte[4];
        for(int variable=0;variable<32;variable++) {
            if((solution&(1<<variable))==0)continue;
            int byteIndex=variable/8;
            int bitInByte=7-(variable%8);
            patch[byteIndex]|=(byte)(1<<bitInByte);
        }
        byte[] verify=source.clone();
        verify[0]=0;verify[1]=0;verify[2]=0;verify[3]=0;
        System.arraycopy(patch,0,verify,offset,4);
        return rawCrc(verify)==target?patch:null;
    }

    private long calculateApplicationCrc(byte[] app) {
        byte[] work=app.clone();
        work[0]=0;work[1]=0;work[2]=0;work[3]=0;
        return rawCrc(work);
    }

    private long rawCrc(byte[] b) {
        CRC32 c=new CRC32();c.update(b);return c.getValue()&0xffffffffL;
    }

    private long getU32BE(byte[] image,long a) {
        int o=(int)a;
        return ((long)(image[o]&0xff)<<24)|
               ((long)(image[o+1]&0xff)<<16)|
               ((long)(image[o+2]&0xff)<<8)|(image[o+3]&0xffL);
    }

    private byte[] slice(byte[] source,long a,int length) {
        int o=(int)a;
        if(o<0||length<0||o+length>source.length)
            throw new IllegalArgumentException("Invalid slice.");
        byte[] result=new byte[length];
        System.arraycopy(source,o,result,0,length);
        return result;
    }

    private void putBytes(byte[] target,long a,byte[] values) {
        int o=(int)a;
        if(o<0||o+values.length>target.length)
            throw new IllegalArgumentException("Invalid write.");
        System.arraycopy(values,0,target,o,values.length);
    }

    private void requireBytes(byte[] image,long a,byte[] expected,String role) {
        byte[] actual=slice(image,a,expected.length);
        if(!equalsBytes(actual,expected))
            throw new IllegalStateException(
                role+" mismatch at "+hex(a)+". Expected "+
                toHex(expected)+" found "+toHex(actual));
    }

    private boolean equalsBytes(byte[] a,byte[] b) {
        return Arrays.equals(a,b);
    }

    private boolean inRange(long a,long start,int length) {
        return a>=start&&a<start+length;
    }

    private byte[] readCurrentBytes(Address a,int n) throws Exception {
        byte[] b=new byte[n];
        int got=memory.getBytes(a,b);
        if(got!=n)
            throw new IllegalStateException("Short stock read at "+a);
        return b;
    }

    private String sha256CurrentProgram() throws Exception {
        MessageDigest d=MessageDigest.getInstance("SHA-256");
        for(long p=0;p<IMAGE_SIZE;) {
            int n=(int)Math.min(0x4000L,IMAGE_SIZE-p);
            byte[] b=new byte[n];
            int got=memory.getBytes(addr(p),b);
            if(got!=n)
                throw new IllegalStateException("Short stock read at "+hex(p));
            d.update(b);p+=n;
        }
        return toHexCompact(d.digest());
    }

    private String sha256(byte[] b) throws Exception {
        MessageDigest d=MessageDigest.getInstance("SHA-256");
        d.update(b);return toHexCompact(d.digest());
    }

    private String sha256File(File f) throws Exception {
        MessageDigest d=MessageDigest.getInstance("SHA-256");
        try(BufferedInputStream in=new BufferedInputStream(new FileInputStream(f))) {
            byte[] b=new byte[65536];int n;
            while((n=in.read(b))>=0)if(n>0)d.update(b,0,n);
        }
        return toHexCompact(d.digest());
    }

    private String toHexCompact(byte[] b) {
        StringBuilder s=new StringBuilder();
        for(byte x:b)s.append(String.format(Locale.ROOT,"%02x",x&0xff));
        return s.toString();
    }

    private String toHex(byte[] b) {
        StringBuilder s=new StringBuilder();
        for(byte x:b){
            if(s.length()>0)s.append(' ');
            s.append(String.format(Locale.ROOT,"%02X",x&0xff));
        }
        return s.toString();
    }

    private static byte[] bytes(int... values) {
        byte[] b=new byte[values.length];
        for(int i=0;i<values.length;i++)b[i]=(byte)values[i];
        return b;
    }

    private String lower(String s) {
        return s==null?"":s.toLowerCase(Locale.ROOT);
    }

    private Address addr(long v) {
        return space.getAddress(v&0xffffffffL);
    }

    private String hex(long v) {
        return String.format(Locale.ROOT,"0x%08X",v&0xffffffffL);
    }
}
