// TeslaGatewayV497R1AP318StartupAndWakeMin300SecA31E4CompletionBenchBuilderV617.java
//
// BENCH/STATIONARY ONLY. Direct image synthesis; active Ghidra program is not
// committed or modified.
//
// Evidence carried forward
// ------------------------
// * V580: CAN318 AP0 for the first 300 oneHz ticks, with CAN368/CAN398/runtime
//   still AP2, produced the only demonstrated temporary good AP2 session.
// * V585: A47EA falling edge -> F7942(0x40013150) is a proven native wake source
//   capable of causing same-iteration powerRails CAN318 re-sampling.
// * V586R4: a 5-second wake gate was too short; reboot behavior was unchanged.
// * V609: process_vehicle_config_check sets ACTION_WORD bits 0x00000800,
//   0x00100000 and 0x00400000; oneHz -> A31E4 conditionally clears that exact
//   trio, giving a finite asynchronous reconciliation-complete surface.
// * V614: no non-retired local exact CAN318 AP-field consumer remains.
// * V616: no AP-family CAN registration owner is re-entered from lifecycle roots.
//
// V617 is therefore not a simple widening of V586. It combines the known-good
// V580 minimum duration with the V609 finite completion surface and the V585
// native wake event.
//
// Runtime behavior
// ----------------
// * First AP publication starts a 300-tick CAN318-only AP0 hold (V580 behavior).
// * Every V585 A47EA falling wake edge re-arms the same 300-tick hold and clears
//   only CAN318 AP bits before signaling stock F7942.
// * At/after 300 ticks, release is allowed only when ACTION_WORD config bits
//   0x800 / 0x100000 / 0x400000 are all clear. If still set, scratch becomes
//   0x2000 and AP0 is held until a later oneHz sample sees all three clear.
// * Completion writes 0x7FFF and restores CAN318 AP2 immediately.
// * CAN368, CAN398 and runtime AP2 are untouched. command32/0x88340/reset logic
//   are untouched.
//
// Input: exact V497R1 2 MiB BIN. Output directory MUST be new/empty. Emits
// patched BIN/S19, exact rollback BIN/S19, report and hashes. Application CRC
// remains stock 0x38C63335 using the established compensation word.
//
// @category TeslaGateway.Bench
// @menupath Tools.Tesla.Build V497R1 AP318 Startup Wake Min300 A31E4 Completion V617

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

public class TeslaGatewayV497R1AP318StartupAndWakeMin300SecA31E4CompletionBenchBuilderV617
        extends GhidraScript {

    private static final String PREFIX =
        "TeslaGatewayV497R1AP318StartupAndWakeMin300SecA31E4CompletionBenchBuilderV617";

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

    // Proven V580 scratch word reused as the combined session state.
    // 0 = not started; 1..300 = minimum AP0 hold countdown;
    // 0x2000 = minimum elapsed but reconciliation bits still pending;
    // 0x7FFF = session hold complete / CAN318 AP2 released.
    private static final long SCRATCH_WORD = 0x40014E2CL;
    private static final int WINDOW_TICKS = 300;
    private static final int WAIT_SENTINEL = 0x2000;
    private static final int DONE_SENTINEL = 0x7FFF;

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

    // Verified-zero padding family. V617 adds a third bounded wrapper cave.
    private static final long AP_WRAPPER = 0x00125A00L;
    private static final int AP_WRAPPER_RESERVED = 0x80;
    private static final long ONEHZ_WRAPPER = 0x00125B40L;
    private static final int ONEHZ_WRAPPER_RESERVED = 0x140;
    private static final long WAKE_WRAPPER = 0x00125C80L;
    private static final int WAKE_WRAPPER_RESERVED = 0x80;

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
                "V617 requires the exact stock analysed Ghidra project. SHA256="+stockSha);

        Contract c=validateAndBuildStockContract();

        File input=askFile("Select exact V497R1 2 MiB BIN","Open");
        if(input==null)return;
        File outDir=askDirectory("Select NEW EMPTY V617 output folder","Select");
        if(outDir==null)return;
        requireEmptyDirectory(outDir);

        byte[] baseline=readWholeFile(input);
        validateV497R1Baseline(baseline,c);

        byte[] patched=baseline.clone();

        // V617 adds no command32/check hook.
        putBytes(patched,INSERT_368,c.apHook);
        putBytes(patched,ONE_HZ,c.oneHzHook);
        putBytes(patched,WAKE_EDGE_SEND_CALL,c.wakeEdgeHook);
        putBytes(patched,AP_WRAPPER,c.apWrapper);
        putBytes(patched,ONEHZ_WRAPPER,c.oneHzWrapper);
        putBytes(patched,WAKE_WRAPPER,c.wakeWrapper);

        // Re-solve the established four-byte CRC-neutral compensation slot.
        putBytes(patched,COMPENSATION_ADDRESS,new byte[]{0,0,0,0});
        byte[] app=slice(patched,APP_START,EXPECTED_APP_SIZE);
        int compOffset=(int)(COMPENSATION_ADDRESS-APP_START);
        byte[] compensation=solveFourBytePatch(app,compOffset,STOCK_APP_CRC);
        if(compensation==null)
            throw new IllegalStateException("V617 CRC-neutral compensation solver failed.");
        putBytes(patched,COMPENSATION_ADDRESS,compensation);

        validateOutput(baseline,patched,c,compensation);

        String stem=
            "Tesla_MCU1_V497R1_AP318StartupWakeMin300A31E4Completion_V617_CRCNeutral";
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
            "V617 complete.\n\n"+
            "Initial boot and each V585 A47EA falling wake edge start a minimum 300-oneHz-tick CAN318-only AP0 hold.\n"+
            "After the minimum interval, release waits until ACTION_WORD bits 0x800/0x100000/0x400000 are all clear; then CAN318 AP2 is restored.\n"+
            "CAN368/CAN398 and runtime AP2 remain AP2. Command32 and 0x88340 are untouched.\n\n"+
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
                "V617 expected direct 4-byte A47EA event-send call at "+hex(WAKE_EDGE_SEND_CALL)+".");
        Address[] wakeFlows=wakeCall.getFlows();
        if(wakeFlows==null || wakeFlows.length!=1 ||
           (wakeFlows[0].getOffset()&0xffffffffL)!=EVENT_SEND)
            throw new IllegalStateException(
                "V617 A47EA wake-edge call does not target F7942.");
        c.wakeEdgeOriginal=readCurrentBytes(addr(WAKE_EDGE_SEND_CALL),4);
        c.wakeEdgeHook=assembleLine(addr(WAKE_EDGE_SEND_CALL),
            "e_bl "+hex(WAKE_WRAPPER),4);

        c.apWrapper=buildApWrapper(c);
        c.oneHzWrapper=buildOneHzWrapper(c);
        c.wakeWrapper=buildWakeWrapper(c);

        if(c.apWrapper.length>AP_WRAPPER_RESERVED)
            throw new IllegalStateException(
                "V617 AP wrapper exceeds reserved cave: "+c.apWrapper.length);
        if(c.oneHzWrapper.length>ONEHZ_WRAPPER_RESERVED)
            throw new IllegalStateException(
                "V617 oneHz wrapper exceeds reserved cave: "+c.oneHzWrapper.length);
        if(c.wakeWrapper.length>WAKE_WRAPPER_RESERVED)
            throw new IllegalStateException(
                "V617 wake wrapper exceeds reserved cave: "+c.wakeWrapper.length);

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

        long active=AP_WRAPPER+0x44L;
        long start=AP_WRAPPER+0x4AL;
        long common=AP_WRAPPER+0x54L;

        // DONE is the only AP2 release state. WAIT and active countdown are AP0.
        p=emit(out,p,"e_cmpl16i. r12,0x7fff",4);
        p=emit(out,p,"e_beq cr0,"+hex(common),4);
        p=emit(out,p,"e_cmpl16i. r12,0x2000",4);
        p=emit(out,p,"e_beq cr0,"+hex(active),4);
        p=emit(out,p,"e_cmp16i. r12,0x0",4);
        p=emit(out,p,"e_beq cr0,"+hex(start),4);
        p=emit(out,p,"e_cmpl16i. r12,0x12c",4);
        p=emit(out,p,"e_bgt cr0,"+hex(start),4);

        if((p.getOffset()&0xffffffffL)!=active)
            throw new IllegalStateException("V617 AP active label drifted: "+p+" expected "+hex(active));
        p=emit(out,p,"se_li r0,0x0",2);
        p=emit(out,p,"e_b "+hex(common),4);

        if((p.getOffset()&0xffffffffL)!=start)
            throw new IllegalStateException("V617 AP start label drifted: "+p+" expected "+hex(start));
        p=emit(out,p,"e_li r12,0x12c",4);
        p=emit(out,p,"e_stw r12,0(r11)",4);
        p=emit(out,p,"se_li r0,0x0",2);

        if((p.getOffset()&0xffffffffL)!=common)
            throw new IllegalStateException("V617 AP common label drifted: "+p+" expected "+hex(common));

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

        long base=ONEHZ_WRAPPER+c.oneHzOriginal.length;
        long checkCompletion=base+(21L*4L);
        long pending=base+0x96L;
        long restoreOnly=base+0x9EL;

        p=emit(out,p,"e_stwu r1,-32(r1)",4);                 // 0
        p=emit(out,p,"e_stw r0,16(r1)",4);                  // 1
        p=emit(out,p,"e_stw r11,20(r1)",4);                 // 2
        p=emit(out,p,"e_stw r12,24(r1)",4);                 // 3
        p=emit(out,p,"mfcr r0",4);                          // 4
        p=emit(out,p,"e_stw r0,28(r1)",4);                  // 5
        p=emit(out,p,"e_lis r11,0x4001",4);                 // 6
        p=emit(out,p,"e_add16i r11,r11,0x4e2c",4);          // 7
        p=emit(out,p,"e_lwz r12,0(r11)",4);                 // 8
        p=emit(out,p,"e_cmpl16i. r12,0x7fff",4);             // 9
        p=emit(out,p,"e_beq cr0,"+hex(restoreOnly),4);       // 10
        p=emit(out,p,"e_cmpl16i. r12,0x2000",4);             // 11
        p=emit(out,p,"e_beq cr0,"+hex(checkCompletion),4);   // 12
        p=emit(out,p,"e_cmp16i. r12,0x0",4);                // 13
        p=emit(out,p,"e_beq cr0,"+hex(restoreOnly),4);       // 14
        p=emit(out,p,"e_cmpl16i. r12,0x12c",4);              // 15
        p=emit(out,p,"e_bgt cr0,"+hex(restoreOnly),4);       // 16
        p=emit(out,p,"e_add16i r12,r12,-1",4);              // 17
        p=emit(out,p,"e_stw r12,0(r11)",4);                 // 18
        p=emit(out,p,"e_cmp16i. r12,0x0",4);                // 19
        p=emit(out,p,"e_bne cr0,"+hex(restoreOnly),4);       // 20

        if((p.getOffset()&0xffffffffL)!=checkCompletion)
            throw new IllegalStateException("V617 completion label drifted: "+p+" expected "+hex(checkCompletion));

        // V609 finite completion surface: all three process-config ACTION bits clear.
        p=emit(out,p,"e_lis r12,0x4001",4);                 // 21
        p=emit(out,p,"e_add16i r12,r12,0x314c",4);          // 22
        p=emit(out,p,"e_lwz r0,0(r12)",4);                  // 23
        p=emit(out,p,"se_btsti r0,0x14",2);                 // 24 (0x00000800)
        p=emit(out,p,"e_bne cr0,"+hex(pending),4);           // 25
        p=emit(out,p,"se_btsti r0,0xb",2);                  // 26 (0x00100000)
        p=emit(out,p,"e_bne cr0,"+hex(pending),4);           // 27
        p=emit(out,p,"se_btsti r0,0x9",2);                  // 28 (0x00400000)
        p=emit(out,p,"e_bne cr0,"+hex(pending),4);           // 29

        // Completion: mark DONE and restore only CAN318 AP2 immediately.
        p=emit(out,p,"e_li r12,0x7fff",4);                  // 30
        p=emit(out,p,"e_stw r12,0(r11)",4);                 // 31
        p=emit(out,p,"e_lis r11,0x4004",4);                 // 32
        p=emit(out,p,"e_add16i r11,r11,0x7caf",4);          // 33
        p=emit(out,p,"e_lbz r12,0(r11)",4);                 // 34
        p=emit(out,p,"e_and2i. r12,0x1f",4);                // 35
        p=emit(out,p,"e_or2i r12,0x40",4);                  // 36
        p=emit(out,p,"e_stb r12,0(r11)",4);                 // 37
        p=emit(out,p,"e_b "+hex(restoreOnly),4);            // 38

        if((p.getOffset()&0xffffffffL)!=pending)
            throw new IllegalStateException("V617 pending label drifted: "+p+" expected "+hex(pending));
        p=emit(out,p,"e_li r12,0x2000",4);                  // 39
        p=emit(out,p,"e_stw r12,0(r11)",4);                 // 40

        if((p.getOffset()&0xffffffffL)!=restoreOnly)
            throw new IllegalStateException("V617 restore label drifted: "+p+" expected "+hex(restoreOnly));
        p=emit(out,p,"e_lwz r0,28(r1)",4);                  // 41
        p=emit(out,p,"mtcrf 0xff,r0",4);                    // 42
        p=emit(out,p,"e_lwz r12,24(r1)",4);                 // 43
        p=emit(out,p,"e_lwz r11,20(r1)",4);                 // 44
        p=emit(out,p,"e_lwz r0,16(r1)",4);                  // 45
        p=emit(out,p,"e_add16i r1,r1,32",4);                // 46
        p=emit(out,p,"e_b "+hex(c.oneHzRejoin),4);          // 47
        return out.toByteArray();
    }

    private byte[] buildWakeWrapper(Contract c) throws Exception {
        ByteArrayOutputStream out=new ByteArrayOutputStream();
        Address p=addr(WAKE_WRAPPER);

        // Preserve caller return and temporaries. r3-r6 remain original F7942 args.
        p=emit(out,p,"e_stwu r1,-32(r1)",4);
        p=emit(out,p,"e_stw r0,16(r1)",4);
        p=emit(out,p,"e_stw r11,20(r1)",4);
        p=emit(out,p,"e_stw r12,24(r1)",4);
        p=emit(out,p,"se_mflr r0",2);
        p=emit(out,p,"e_stw r0,28(r1)",4);

        // Arm/re-arm the V580-proven 300 oneHz-tick minimum hold.
        // r12 is not encodable by the 16-bit se_li form in this VLE profile;
        // use the 32-bit e_li form. V586R3 correctly failed before image synthesis.
        p=emit(out,p,"e_lis r11,0x4001",4);
        p=emit(out,p,"e_add16i r11,r11,0x4e2c",4);
        p=emit(out,p,"e_li r12,0x12c",4);
        p=emit(out,p,"e_stw r12,0(r11)",4);

        // Clear ONLY CAN318 AP bits before waking powerRails.
        p=emit(out,p,"e_lis r11,0x4004",4);
        p=emit(out,p,"e_add16i r11,r11,0x7caf",4);
        p=emit(out,p,"e_lbz r12,0(r11)",4);
        p=emit(out,p,"e_and2i. r12,0x1f",4);
        p=emit(out,p,"e_stb r12,0(r11)",4);

        // Original A47EA action, with original r3-r6.
        p=emit(out,p,"e_bl "+hex(EVENT_SEND),4);

        // Return exactly to A47EA after the replaced call.
        p=emit(out,p,"e_lwz r0,28(r1)",4);
        p=emit(out,p,"se_mtlr r0",2);
        p=emit(out,p,"e_lwz r12,24(r1)",4);
        p=emit(out,p,"e_lwz r11,20(r1)",4);
        p=emit(out,p,"e_lwz r0,16(r1)",4);
        p=emit(out,p,"e_add16i r1,r1,32",4);
        p=emit(out,p,"se_blr",2);
        return out.toByteArray();
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
                "V617 requires exact V497R1 input BIN. SHA256="+sha);

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
            "V617 AP wrapper cave");
        requireZeroRange(image,ONEHZ_WRAPPER,ONEHZ_WRAPPER_RESERVED,
            "V617 oneHz wrapper cave");
        requireZeroRange(image,WAKE_WRAPPER,WAKE_WRAPPER_RESERVED,
            "V617 wake wrapper cave");
    }

    private void validateOutput(byte[] baseline,byte[] patched,Contract c,
            byte[] compensation) {
        requireBytes(patched,INSERT_368,c.apHook,
            "V617 AP publication detour");
        requireBytes(patched,ONE_HZ,c.oneHzHook,
            "V617 oneHz countdown detour");
        requireBytes(patched,WAKE_EDGE_SEND_CALL,c.wakeEdgeHook,
            "V617 A47EA falling-edge wake detour");
        requireBytes(patched,AP_WRAPPER,c.apWrapper,"V617 AP wrapper");
        requireBytes(patched,ONEHZ_WRAPPER,c.oneHzWrapper,
            "V617 oneHz wrapper");
        requireBytes(patched,WAKE_WRAPPER,c.wakeWrapper,
            "V617 wake wrapper");
        requireBytes(patched,COMPENSATION_ADDRESS,compensation,
            "V617 CRC compensation");

        // Explicitly prove command32/check path is untouched after V579R1 closure.
        requireBytes(patched,COMMAND32_HANDLER,
            slice(baseline,COMMAND32_HANDLER,c.command32Entry.length),
            "V617 command32 handler unchanged");
        requireBytes(patched,COMMAND32_CHECK_CALL,
            slice(baseline,COMMAND32_CHECK_CALL,c.command32CheckCall.length),
            "V617 command32 check call unchanged");
        requireBytes(patched,SELECTOR_ENABLE_LOAD,
            slice(baseline,SELECTOR_ENABLE_LOAD,c.selectorEnableLoad.length),
            "V617 selector-enable load unchanged");

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
                "V617 CRC mismatch. stored=0x%08X calculated=0x%08X",
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
                inRange(a,WAKE_EDGE_SEND_CALL,4);
            if(!allowed)
                throw new IllegalStateException(
                    "Unexpected V617 changed byte at "+hex(a)+".");
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
            w.write("Tesla Gateway V497R1 AP318 Startup/Wake Min300 + A31E4 Completion V617\r\n");
            w.write("================================================================\r\n\r\n");
            w.write("BENCH/STATIONARY ONLY. NOT FOR ROAD USE.\r\n");
            w.write("Keep rollback image immediately available.\r\n\r\n");

            w.write("Purpose\r\n-------\r\n");
            w.write("Initial AP publication starts the V580-proven minimum 300-second CAN318-only AP0 window; each V585-validated A47EA falling wake edge re-arms the same window before powerRails is signalled.\r\n");
            w.write("Release is additionally gated by the V609 ACTION_WORD completion surface, so this is not a simple widening of V586.\r\n\r\n");

            w.write("Runtime sequence\r\n----------------\r\n");
            w.write("1. A47EA reaches stock falling-edge send site 0x000A4ADA.\r\n");
            w.write("2. V617 wrapper writes scratch 0x40014E2C=300.\r\n");
            w.write("3. V617 clears only CAN318 AP mask 0xE0 at byte 0x40047CAF.\r\n");
            w.write("4. Wrapper calls stock F7942 with the original r3-r6, signalling 0x40013150.\r\n");
            w.write("5. During scratch 1..300 / WAIT, apply_autopilot_config keeps only CAN318 at AP0.\r\n");
            w.write("6. oneHz decrements for 300 ticks. At expiry it tests ACTION_WORD bits 0x800/0x100000/0x400000.\r\n");
            w.write("7. If any remain set, scratch becomes 0x2000 and CAN318 remains AP0 until all three clear.\r\n");
            w.write("8. Completion writes scratch 0x7FFF and restores CAN318 AP2 immediately.\r\n");
            w.write("9. Another falling wake edge re-arms the full minimum-300s hold.\r\n\r\n");

            w.write("Hooks/wrappers\r\n--------------\r\n");
            w.write("0x00087128 -> "+hex(AP_WRAPPER)+" AP318-only detour: "+toHex(c.apHook)+"\r\n");
            w.write("0x0006F99C -> "+hex(ONEHZ_WRAPPER)+" oneHz countdown detour; span="+c.oneHzSpan+" bytes\r\n");
            w.write("0x000A4ADA -> "+hex(WAKE_WRAPPER)+" A47EA falling-edge wrapper: "+toHex(c.wakeEdgeHook)+"\r\n");
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
            w.write("- individual ACC/drive/HVAC helper paths unchanged.\r\n\r\n");

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

            w.write("Stationary test\r\n---------------\r\n");
            w.write("1. Flash V617. As with V580, CAN318 AP is intentionally AP0 during the initial minimum-300s window, so visible AP2 may be absent initially.\r\n");
            w.write("2. Wait for the initial hold to complete and confirm AP2 returns; then establish the awake-session Software-page baseline.\r\n");
            w.write("3. Allow the car to settle/rest normally.\r\n");
            w.write("4. Wake using the normal real-world sequence: unlock/open door/brake/Drive as applicable.\r\n");
            w.write("5. The native A47EA falling edge should arm CAN318 AP0 for at least 300 oneHz ticks, while UI/runtime AP2 remains otherwise intact.\r\n");
            w.write("6. After the post-wake hold completes and AP2 returns, run Software Check and record reboot/no reboot. Preserve SD logs.\r\n\r\n");

            w.write("Interpretation\r\n--------------\r\n");
            w.write("AP2 visible + wake + no later reboot: strong support that the V583 powerRails resample is the relevant lifecycle observer and can be masked locally.\r\n");
            w.write("AP2 visible but reboot still returns after wake: either another 0x40013150 producer/observer matters or the minimum 300-second + completion hold is still insufficient; use logs before widening it.\r\n");
            w.write("AP2 UI disappears transiently but returns: UI is live to the minimum-300s AP0 transition, but lifecycle gating may still be viable with a shorter hold.\r\n");
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
                "V617 BIN/S19 builder requires a NEW EMPTY output directory.");
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
