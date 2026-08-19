// TeslaGatewayV497R1AP318StartupAndWakeMin300SecA31E4CompletionBenchBuilderV617R1.java
//
// BENCH/STATIONARY ONLY. Direct image synthesis; active Ghidra program is not
// committed or modified.
//
// V617R1 corrects the two blockers found in the V617 review:
//   1. release requires an exact current-session set-then-clear lifecycle on the
//      V609 ACTION_WORD trio, not merely "bits happen to be clear";
//   2. wake re-arm and oneHz state/AP-byte transitions are serialized with the
//      stock F7380/F73A8 critical-section pair, preventing a stale oneHz commit
//      from overwriting a newer wake re-arm.
//
// Evidence carried forward
// ------------------------
// * V580: CAN318 AP0 for the first 300 oneHz ticks, with CAN368/CAN398/runtime
//   still AP2, produced the only demonstrated temporary good AP2 session.
// * V585: A47EA falling edge -> F7942(0x40013150) is a proven native event source
//   capable of waking powerRails and causing same-iteration CAN318 re-sampling.
//   It is NOT assumed to occur once for every vehicle wake.
// * V586R4: a five-second A47EA gate was too short; reboot behavior was unchanged.
// * V596R1: both known local powerRails CAN318 AP observers were causally negative.
// * V609: process_vehicle_config_check sets ACTION_WORD bits 0x00000800,
//   0x00100000 and 0x00400000; oneHz -> A31E4 conditionally clears that exact
//   trio, giving a finite asynchronous completion surface.
// * V614: no non-retired local exact CAN318 AP-field consumer remains.
// * V616: no AP-family CAN registration owner is re-entered from lifecycle roots.
//
// V617R1 state machine (scratch 0x40014E2C)
// ------------------------------------------------
// low 9 bits  : countdown 0..300
// bit 12      : SAW_ACTION_SET in this session
// bit 13      : minimum 300-tick interval elapsed
// 0x4000      : DONE (exact terminal state)
//
// First AP publication starts countdown=300 and publishes CAN318 AP0 only.
// Each observed V585 A47EA falling-edge event re-arms countdown=300, clears the
// SAW/ELAPSED flags, clears only CAN318 AP bits, then performs the original F7942.
// The oneHz wrapper samples the exact ACTION bits BEFORE stock oneHz can reach
// A31E4, so an action that is cleared later in that same stock oneHz iteration is
// still latched as observed.
//
// Release condition is exactly:
//   minimum_elapsed && SAW_ACTION_SET && action_bits_now_clear
//
// CAN368, CAN398 and runtime AP2 are untouched. command32/0x88340/reset logic
// are untouched. Success supports a session-scoped CAN318 publication /
// reconciliation window; it does not rehabilitate either V596R1-blinded local
// powerRails observer.
//
// Input: exact V497R1 2 MiB BIN. Output directory MUST be new/empty. Emits
// patched BIN/S19, exact rollback BIN/S19, report and hashes. Application CRC
// remains stock 0x38C63335 using the established compensation word.
//
// @category TeslaGateway.Bench
// @menupath Tools.Tesla.Build V497R1 AP318 Startup Wake Min300 SetClear V617R1

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

public class TeslaGatewayV497R1AP318StartupAndWakeMin300SecA31E4CompletionBenchBuilderV617R1
        extends GhidraScript {

    private static final String PREFIX =
        "TeslaGatewayV497R1AP318StartupAndWakeMin300SecA31E4CompletionBenchBuilderV617R1";

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

    // Proven V580 scratch word reused as the session state.
    private static final long SCRATCH_WORD = 0x40014E2CL;
    private static final int WINDOW_TICKS = 300;
    private static final int COUNT_MASK = 0x01FF;
    private static final int SAW_ACTION_SET = 0x1000;
    private static final int MINIMUM_ELAPSED = 0x2000;
    private static final int DONE_STATE = 0x4000;

    // Exact V609 process-config/A31E4 finite-completion surface.
    private static final long ACTION_WORD = 0x4001314CL;
    private static final long CRITICAL_ENTER = 0x000F7380L;
    private static final long CRITICAL_EXIT  = 0x000F73A8L;

    // apply_autopilot_config publication sequence.
    private static final long AP_OWNER = 0x000870F0L;
    private static final long INSERT_368 = 0x00087128L;
    private static final long INSERT_318 = 0x0008712CL;
    private static final long INSERT_398 = 0x00087130L;
    private static final long STORE_368 = 0x00087134L;
    private static final long STORE_398 = 0x00087138L;
    private static final long STORE_318 = 0x0008713CL;
    private static final long AP_WORD_368 = 0x4004AA38L;
    private static final long AP_WORD_318 = 0x40047CACL;
    private static final long AP_WORD_398 = 0x40049DA4L;
    private static final long AP318_BYTE = 0x40047CAFL;

    // oneHzThings timer owner.
    private static final long ONE_HZ = 0x0006F99CL;

    // Native A47EA falling-wake-edge producer recovered by V584/V585.
    private static final long WAKE_EDGE_SEND_CALL = 0x000A4ADAL;
    private static final long EVENT_SEND = 0x000F7942L;

    // Verified-zero padding family. The new helper occupies a separate bounded
    // zero cave so the oneHz entry wrapper stays ABI-clean and small.
    private static final long AP_WRAPPER = 0x00125A00L;
    private static final int AP_WRAPPER_RESERVED = 0x80;
    private static final long ONEHZ_WRAPPER = 0x00125B40L;
    private static final int ONEHZ_WRAPPER_RESERVED = 0x140;
    private static final long WAKE_WRAPPER = 0x00125C80L;
    private static final int WAKE_WRAPPER_RESERVED = 0x100;
    private static final long STATE_HELPER = 0x00125D80L;
    private static final int STATE_HELPER_RESERVED = 0x180;

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

    private static final byte[] NOP4 = bytes(0x44,0x00,0x44,0x00);
    private static final byte[] COMMAND33_MARKER =
        bytes(0x43,0x33,0x33,0x53,0x59,0x4E,0x30,0x00); // C33SYN0\0

    private Memory memory;
    private AddressSpace space;

    private static class Contract {
        byte[] insert368;
        byte[] insert318;
        byte[] insert398;
        byte[] command32Entry;
        byte[] command32CheckCall;
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
                "V617R1 requires the exact stock analysed Ghidra project. SHA256="+stockSha);

        Contract c=validateAndBuildStockContract();

        File input=askFile("Select exact V497R1 2 MiB BIN","Open");
        if(input==null)return;
        File outDir=askDirectory("Select NEW EMPTY V617R1 output folder","Select");
        if(outDir==null)return;
        requireEmptyDirectory(outDir);

        byte[] baseline=readWholeFile(input);
        validateV497R1Baseline(baseline,c);

        byte[] patched=baseline.clone();

        // V617R1 adds no command32/check hook.
        putBytes(patched,INSERT_368,c.apHook);
        putBytes(patched,ONE_HZ,c.oneHzHook);
        putBytes(patched,WAKE_EDGE_SEND_CALL,c.wakeEdgeHook);
        putBytes(patched,AP_WRAPPER,c.apWrapper);
        putBytes(patched,ONEHZ_WRAPPER,c.oneHzWrapper);
        putBytes(patched,WAKE_WRAPPER,c.wakeWrapper);
        putBytes(patched,STATE_HELPER,c.stateHelper);

        // Re-solve the established four-byte CRC-neutral compensation slot.
        putBytes(patched,COMPENSATION_ADDRESS,new byte[]{0,0,0,0});
        byte[] app=slice(patched,APP_START,EXPECTED_APP_SIZE);
        int compOffset=(int)(COMPENSATION_ADDRESS-APP_START);
        byte[] compensation=solveFourBytePatch(app,compOffset,STOCK_APP_CRC);
        if(compensation==null)
            throw new IllegalStateException("V617R1 CRC-neutral compensation solver failed.");
        putBytes(patched,COMPENSATION_ADDRESS,compensation);

        validateOutput(baseline,patched,c,compensation);

        String stem=
            "Tesla_MCU1_V497R1_AP318StartupWakeMin300SetClear_V617R1_CRCNeutral";
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
            "V617R1 complete.\n\n"+
            "Release now requires a current-session ACTION set-then-clear after at least 300 oneHz ticks.\n"+
            "Wake re-arm and oneHz completion are serialized with stock F7380/F73A8.\n"+
            "A47EA is described only as each observed falling-edge event, not every vehicle wake.\n"+
            "CAN368/CAN398/runtime AP2 and command32/0x88340 remain untouched.\n\n"+
            "Do not flash yet: upload the generated BIN/S19/report/hashes/rollback artifacts for independent validation first.\n"+
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

        Instruction wakeCall=getInstructionAt(addr(WAKE_EDGE_SEND_CALL));
        if(wakeCall==null || wakeCall.getLength()!=4 ||
           wakeCall.getFlowType()==null || !wakeCall.getFlowType().isCall() ||
           wakeCall.getFlowType().isComputed())
            throw new IllegalStateException(
                "V617R1 expected direct 4-byte A47EA event-send call at "+hex(WAKE_EDGE_SEND_CALL)+".");
        Address[] wakeFlows=wakeCall.getFlows();
        if(wakeFlows==null || wakeFlows.length!=1 ||
           (wakeFlows[0].getOffset()&0xffffffffL)!=EVENT_SEND)
            throw new IllegalStateException(
                "V617R1 A47EA wake-edge call does not target F7942.");
        c.wakeEdgeOriginal=readCurrentBytes(addr(WAKE_EDGE_SEND_CALL),4);
        c.wakeEdgeHook=assembleLine(addr(WAKE_EDGE_SEND_CALL),
            "e_bl "+hex(WAKE_WRAPPER),4);

        Function critEnter=currentProgram.getFunctionManager().getFunctionAt(addr(CRITICAL_ENTER));
        Function critExit=currentProgram.getFunctionManager().getFunctionAt(addr(CRITICAL_EXIT));
        if(critEnter==null || (critEnter.getEntryPoint().getOffset()&0xffffffffL)!=CRITICAL_ENTER)
            throw new IllegalStateException("V617R1 critical-enter 0xF7380 is not defined as expected.");
        if(critExit==null || (critExit.getEntryPoint().getOffset()&0xffffffffL)!=CRITICAL_EXIT)
            throw new IllegalStateException("V617R1 critical-exit 0xF73A8 is not defined as expected.");

        c.apWrapper=buildApWrapper(c);
        c.oneHzWrapper=buildOneHzWrapper(c);
        c.wakeWrapper=buildWakeWrapper(c);
        c.stateHelper=buildStateHelper();

        if(c.apWrapper.length>AP_WRAPPER_RESERVED)
            throw new IllegalStateException(
                "V617R1 AP wrapper exceeds reserved cave: "+c.apWrapper.length);
        if(c.oneHzWrapper.length>ONEHZ_WRAPPER_RESERVED)
            throw new IllegalStateException(
                "V617R1 oneHz wrapper exceeds reserved cave: "+c.oneHzWrapper.length);
        if(c.wakeWrapper.length>WAKE_WRAPPER_RESERVED)
            throw new IllegalStateException(
                "V617R1 wake wrapper exceeds reserved cave: "+c.wakeWrapper.length);
        if(c.stateHelper.length>STATE_HELPER_RESERVED)
            throw new IllegalStateException(
                "V617R1 state helper exceeds reserved cave: "+c.stateHelper.length);

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
        ByteArrayOutputStream out=new ByteArrayOutputStream();
        Address p=addr(AP_WRAPPER);

        // Replay stock CAN368 insertion first. r0 is stock AP2.
        p=emitRaw(out,p,c.insert368);

        p=emit(out,p,"e_stwu r1,-16(r1)",4);
        p=emit(out,p,"e_stw r11,4(r1)",4);
        p=emit(out,p,"e_stw r12,8(r1)",4);
        p=emit(out,p,"mfcr r11",4);
        p=emit(out,p,"e_stw r11,12(r1)",4);
        p=emit(out,p,"e_lis r11,0x4001",4);
        p=emit(out,p,"e_add16i r11,r11,0x4e2c",4);
        p=emit(out,p,"e_lwz r12,0(r11)",4);

        long active=AP_WRAPPER+0x34L;
        long start=AP_WRAPPER+0x3AL;
        long common=AP_WRAPPER+0x44L;

        // DONE is the only AP2 publication state. Any other nonzero state is AP0.
        p=emit(out,p,"e_cmpl16i. r12,0x4000",4);
        p=emit(out,p,"e_beq cr0,"+hex(common),4);
        p=emit(out,p,"e_cmp16i. r12,0x0",4);
        p=emit(out,p,"e_beq cr0,"+hex(start),4);

        if((p.getOffset()&0xffffffffL)!=active)
            throw new IllegalStateException("V617R1 AP active label drifted: "+p+" expected "+hex(active));
        p=emit(out,p,"se_li r0,0x0",2);
        p=emit(out,p,"e_b "+hex(common),4);

        if((p.getOffset()&0xffffffffL)!=start)
            throw new IllegalStateException("V617R1 AP start label drifted: "+p+" expected "+hex(start));
        // First-publication initialization is the only zero->active transition.
        // Cross-session re-arms are performed by the serialized wake wrapper.
        p=emit(out,p,"e_li r12,0x12c",4);
        p=emit(out,p,"e_stw r12,0(r11)",4);
        p=emit(out,p,"se_li r0,0x0",2);

        if((p.getOffset()&0xffffffffL)!=common)
            throw new IllegalStateException("V617R1 AP common label drifted: "+p+" expected "+hex(common));

        p=emitRaw(out,p,c.insert318);
        p=emit(out,p,"se_li r0,0x2",2);
        p=emit(out,p,"e_lwz r11,12(r1)",4);
        p=emit(out,p,"mtcrf 0xff,r11",4);
        p=emit(out,p,"e_lwz r12,8(r1)",4);
        p=emit(out,p,"e_lwz r11,4(r1)",4);
        p=emit(out,p,"e_add16i r1,r1,16",4);
        p=emit(out,p,"e_b "+hex(INSERT_398),4);
        return out.toByteArray();
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

        // Preserve original F7942 arguments across the critical-section calls.
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

        // Serialize re-arm + AP-byte clear against the oneHz completion helper.
        p=emit(out,p,"e_bl "+hex(CRITICAL_ENTER),4);
        p=emit(out,p,"e_lis r11,0x4001",4);
        p=emit(out,p,"e_add16i r11,r11,0x4e2c",4);
        p=emit(out,p,"e_li r12,0x12c",4);
        p=emit(out,p,"e_stw r12,0(r11)",4);

        // Clear ONLY CAN318 AP bits before the original wake-event send.
        p=emit(out,p,"e_lis r11,0x4004",4);
        p=emit(out,p,"e_add16i r11,r11,0x7caf",4);
        p=emit(out,p,"e_lbz r12,0(r11)",4);
        p=emit(out,p,"e_and2i. r12,0x1f",4);
        p=emit(out,p,"e_stb r12,0(r11)",4);
        p=emit(out,p,"e_bl "+hex(CRITICAL_EXIT),4);

        // Reconstruct the exact call-site state that stock F7942 would have seen.
        p=emit(out,p,"e_lwz r0,36(r1)",4);
        p=emit(out,p,"mtcrf 0xff,r0",4);
        p=emit(out,p,"e_lwz r3,8(r1)",4);
        p=emit(out,p,"e_lwz r4,12(r1)",4);
        p=emit(out,p,"e_lwz r5,16(r1)",4);
        p=emit(out,p,"e_lwz r6,20(r1)",4);
        p=emit(out,p,"e_bl "+hex(EVENT_SEND),4);

        // Return exactly to A47EA after the replaced call.
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
        int len;
        BlockOp(String label,String line,String target,int len){
            this.label=label;this.line=line;this.target=target;this.len=len;
        }
    }

    private BlockOp mark(String label){return new BlockOp(label,null,null,0);}
    private BlockOp ins(String line,int len){return new BlockOp(null,line,null,len);}
    private BlockOp br(String prefix,String target,int len){return new BlockOp(null,prefix,target,len);}

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
        // This helper runs before stock oneHz body. It samples ACTION_WORD before
        // stock oneHz can reach 0x7150E -> A31E4 and therefore cannot miss an
        // action merely because A31E4 clears it later in the same iteration.
        return assembleBlock(STATE_HELPER,
            ins("e_stwu r1,-16(r1)",4),
            ins("se_mflr r0",2),
            ins("e_stw r0,12(r1)",4),
            ins("e_bl "+hex(CRITICAL_ENTER),4),

            ins("e_lis r11,0x4001",4),
            ins("e_add16i r11,r11,0x4e2c",4),
            ins("e_lwz r12,0(r11)",4),
            ins("e_cmp16i. r12,0x0",4),
            br("e_beq cr0,","UNLOCK",4),
            ins("e_cmpl16i. r12,0x4000",4),
            br("e_beq cr0,","UNLOCK",4),

            // r9 = action-now boolean. Exact V609 logical bits only.
            ins("e_lis r10,0x4001",4),
            ins("e_add16i r10,r10,0x314c",4),
            ins("e_lwz r10,0(r10)",4),
            ins("e_li r9,0x0",4),
            ins("se_btsti r10,0x14",2),
            br("e_bne cr0,","SAW",4),
            ins("se_btsti r10,0xb",2),
            br("e_bne cr0,","SAW",4),
            ins("se_btsti r10,0x9",2),
            br("e_beq cr0,","AFTER_ACTION",4),

            mark("SAW"),
            ins("e_li r9,0x1",4),
            ins("e_or2i r12,0x1000",4),

            mark("AFTER_ACTION"),
            // Extract countdown (low nine bits) without disturbing flags.
            ins("e_rlwinm r8,r12,0x0,0x17,0x1f",4),
            ins("e_cmp16i. r8,0x0",4),
            br("e_beq cr0,","ELAPSED",4),
            ins("e_add16i r8,r8,-1",4),
            // Clear low nine count bits then merge decremented count back.
            ins("e_rlwinm r12,r12,0x0,0x0,0x16",4),
            ins("or r12,r12,r8",4),
            ins("e_cmp16i. r8,0x0",4),
            br("e_bne cr0,","COMMIT",4),

            mark("ELAPSED"),
            ins("e_or2i r12,0x2000",4),
            // No release until current session has positively observed ACTION set.
            ins("e_andi. r7,r12,0x1000",4),
            br("e_beq cr0,","COMMIT",4),
            // If ACTION is still set, remain in AP0 and wait for a later clear.
            ins("e_cmp16i. r9,0x0",4),
            br("e_bne cr0,","COMMIT",4),

            // minimum_elapsed && saw_set && now_clear => DONE + CAN318 AP2.
            ins("e_li r12,0x4000",4),
            ins("e_stw r12,0(r11)",4),
            ins("e_lis r6,0x4004",4),
            ins("e_add16i r6,r6,0x7caf",4),
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
                "V617R1 requires exact V497R1 input BIN. SHA256="+sha);

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
            "V617R1 AP wrapper cave");
        requireZeroRange(image,ONEHZ_WRAPPER,ONEHZ_WRAPPER_RESERVED,
            "V617R1 oneHz wrapper cave");
        requireZeroRange(image,WAKE_WRAPPER,WAKE_WRAPPER_RESERVED,
            "V617R1 wake wrapper cave");
        requireZeroRange(image,STATE_HELPER,STATE_HELPER_RESERVED,
            "V617R1 state helper cave");
    }

    private void validateOutput(byte[] baseline,byte[] patched,Contract c,
            byte[] compensation) {
        requireBytes(patched,INSERT_368,c.apHook,
            "V617R1 AP publication detour");
        requireBytes(patched,ONE_HZ,c.oneHzHook,
            "V617R1 oneHz countdown detour");
        requireBytes(patched,WAKE_EDGE_SEND_CALL,c.wakeEdgeHook,
            "V617R1 A47EA falling-edge wake detour");
        requireBytes(patched,AP_WRAPPER,c.apWrapper,"V617R1 AP wrapper");
        requireBytes(patched,ONEHZ_WRAPPER,c.oneHzWrapper,
            "V617R1 oneHz wrapper");
        requireBytes(patched,WAKE_WRAPPER,c.wakeWrapper,
            "V617R1 wake wrapper");
        requireBytes(patched,STATE_HELPER,c.stateHelper,
            "V617R1 state helper");
        requireBytes(patched,COMPENSATION_ADDRESS,compensation,
            "V617R1 CRC compensation");

        // Explicitly prove command32/check path is untouched after V579R1 closure.
        requireBytes(patched,COMMAND32_HANDLER,
            slice(baseline,COMMAND32_HANDLER,c.command32Entry.length),
            "V617R1 command32 handler unchanged");
        requireBytes(patched,COMMAND32_CHECK_CALL,
            slice(baseline,COMMAND32_CHECK_CALL,c.command32CheckCall.length),
            "V617R1 command32 check call unchanged");
        requireBytes(patched,SELECTOR_ENABLE_LOAD,
            slice(baseline,SELECTOR_ENABLE_LOAD,c.selectorEnableLoad.length),
            "V617R1 selector-enable load unchanged");

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
                "V617R1 CRC mismatch. stored=0x%08X calculated=0x%08X",
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
                inRange(a,WAKE_EDGE_SEND_CALL,4);
            if(!allowed)
                throw new IllegalStateException(
                    "Unexpected V617R1 changed byte at "+hex(a)+".");
        }
    }

    private void writeReport(File report,File input,String stockSha,
            byte[] baseline,byte[] patched,Contract c,byte[] compensation)
            throws Exception {
        int changed=0;
        List<String> ranges=new ArrayList<String>();
        int start=-1,last=-1;
        for(int i=0;i<IMAGE_SIZE;i++){
            if(baseline[i]==patched[i])continue;
            changed++;
            if(start<0){start=last=i;}
            else if(i==last+1)last=i;
            else {ranges.add(hex(start)+".."+hex(last));start=last=i;}
        }
        if(start>=0)ranges.add(hex(start)+".."+hex(last));

        try(BufferedWriter w=new BufferedWriter(
                new OutputStreamWriter(new FileOutputStream(report),StandardCharsets.UTF_8))){
            w.write("Tesla Gateway V497R1 AP318 Startup/Wake Min300 Set-Clear V617R1\r\n");
            w.write("=================================================================\r\n\r\n");
            w.write("BENCH/STATIONARY ONLY. NOT FOR ROAD USE.\r\n");
            w.write("Keep rollback image immediately available.\r\n\r\n");

            w.write("Purpose\r\n-------\r\n");
            w.write("Hold only CAN318 AP at AP0 for a minimum 300 oneHz ticks, then release only after this session has positively observed the exact V609 ACTION trio set and subsequently clear.\r\n");
            w.write("Each observed V585 A47EA falling-edge event re-arms the state before the original F7942 event send. This hook is not claimed to represent every vehicle wake.\r\n\r\n");

            w.write("State machine\r\n-------------\r\n");
            w.write("scratch 0x40014E2C: low9=countdown, bit12=SAW_ACTION_SET, bit13=MINIMUM_ELAPSED, exact 0x4000=DONE.\r\n");
            w.write("ACTION_WORD 0x4001314C exact bits: 0x00000800, 0x00100000, 0x00400000.\r\n");
            w.write("Release condition: minimum_elapsed && saw_action_set && action_bits_now_clear.\r\n");
            w.write("The oneHz helper samples ACTION before stock oneHz reaches 0x7150E -> A31E4, so a same-iteration A31E4 clear cannot erase the observation.\r\n\r\n");

            w.write("Concurrency\r\n-----------\r\n");
            w.write("Wake re-arm + CAN318 AP clear and oneHz state transition + AP2 restore use stock critical pair 0xF7380/0xF73A8.\r\n");
            w.write("Therefore a stale oneHz transition cannot commit across an observed A47EA re-arm.\r\n\r\n");

            w.write("Hooks/wrappers\r\n--------------\r\n");
            w.write("0x00087128 -> "+hex(AP_WRAPPER)+" AP318-only publication detour: "+toHex(c.apHook)+"\r\n");
            w.write("0x0006F99C -> "+hex(ONEHZ_WRAPPER)+" oneHz ABI-preserving detour; span="+c.oneHzSpan+" bytes\r\n");
            w.write("0x000A4ADA -> "+hex(WAKE_WRAPPER)+" observed A47EA falling-edge wrapper: "+toHex(c.wakeEdgeHook)+"\r\n");
            w.write("state helper @"+hex(STATE_HELPER)+" length="+c.stateHelper.length+" bytes\r\n");
            w.write("AP wrapper length: "+c.apWrapper.length+" bytes\r\n");
            w.write("oneHz wrapper length: "+c.oneHzWrapper.length+" bytes\r\n");
            w.write("wake wrapper length: "+c.wakeWrapper.length+" bytes\r\n");
            w.write("CRC compensation @0x00125800: "+toHex(compensation)+"\r\n\r\n");

            w.write("Explicit non-changes\r\n--------------------\r\n");
            w.write("- Runtime AP2 force retained.\r\n");
            w.write("- CAN368 and CAN398 AP2 retained.\r\n");
            w.write("- command32 handler 0x771B4 unchanged.\r\n");
            w.write("- command32 0x77226 -> 0x88340 unchanged.\r\n");
            w.write("- process_vehicle_config_check 0x88340 unchanged.\r\n");
            w.write("- reset/watchdog paths unchanged.\r\n");
            w.write("- V596R1 local powerRails observer conclusion unchanged.\r\n\r\n");

            w.write("Validation\r\n----------\r\n");
            w.write("Input: "+input.getAbsolutePath()+"\r\n");
            w.write("Stock Ghidra SHA256: "+stockSha+"\r\n");
            w.write("Input V497R1 SHA256: "+sha256(baseline)+"\r\n");
            w.write("Changed byte count: "+changed+"\r\n");
            w.write("Changed ranges: "+String.join(", ",ranges)+"\r\n");
            w.write(String.format(Locale.ROOT,
                "Stored/calculated app CRC: 0x%08X / 0x%08X\r\n",
                getU32BE(patched,APP_CRC_ADDRESS),
                calculateApplicationCrc(slice(patched,APP_START,EXPECTED_APP_SIZE))));
            w.write("Patched SHA256: "+sha256(patched)+"\r\n\r\n");

            w.write("Stationary test order\r\n---------------------\r\n");
            w.write("1. After independent artifact validation, flash V617R1 on the stationary bench/car only.\r\n");
            w.write("2. On initial boot, CAN318 AP is intentionally AP0. While it is still AP0, initiate Software Check; do NOT wait for AP2 to return first.\r\n");
            w.write("3. AP2 cannot return before 300 oneHz ticks and cannot return until the helper has seen ACTION set and later clear. Thus AP2 returning is the practical proof that set-then-clear completed.\r\n");
            w.write("4. Confirm the Software Check no longer causes the reboot during/after that completed session.\r\n");
            w.write("5. Then allow a real rest period. After wake, continue the test only if the UI behavior shows CAN318 AP0 was re-armed; otherwise classify A47EA coverage as unproven for that wake.\r\n");
            w.write("6. While the post-event AP0 hold is still active, initiate Software Check again. Preserve SD logs and note whether AP2 later returns and whether any reboot occurs.\r\n\r\n");

            w.write("Interpretation\r\n--------------\r\n");
            w.write("AP2 returns after the per-event hold and no later reboot occurs: supports a session-scoped CAN318 publication/reconciliation window. It does NOT identify either V596R1-blinded local powerRails observer as causal.\r\n");
            w.write("AP2 never returns after Software Check: the state machine did not observe a valid set-then-clear completion (or the action remains pending); do not widen timing blindly.\r\n");
            w.write("Confirmed AP0 re-arm + AP2 later returns + reboot still occurs: this combined window is causally negative and should not be widened again without new evidence.\r\n");
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
                "V617R1 BIN/S19 builder requires a NEW EMPTY output directory.");
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
