// TeslaApplyConfigFallbackAndAPNoPendingCRCNeutralV2.java
// Keeps autopilot out of the reason-1/2/3 watched scan, restores the other
// 14 descriptor watch flags, and redirects only reason-4/reason-5 fallback
// branches to FUN_00095354's clean return-0 epilogue. CRC-neutral.
//
// @category Tesla.ReverseEngineering
// @menupath Tools.Tesla.Apply Config Fallback and AP No-Pending V2

import ghidra.app.script.GhidraScript;
import ghidra.program.model.address.Address;
import ghidra.program.model.lang.Register;
import ghidra.program.model.mem.Memory;

import java.io.File;
import java.io.PrintWriter;
import java.math.BigInteger;
import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.Date;
import java.util.List;
import java.util.Locale;
import java.util.zip.CRC32;

public class TeslaApplyConfigFallbackAndAPNoPendingCRCNeutralV2
        extends GhidraScript {

    private static final long APP_START = 0x00020000L;
    private static final long APP_CRC_ADDR = 0x00020000L;
    private static final long APP_SIZE_ADDR = 0x00020004L;
    private static final long APP_SIZE_INV_ADDR = 0x00020008L;
    private static final long EXPECTED_APP_SIZE = 0x0012929AL;
    private static final long EXPECTED_APP_SIZE_INV = 0xFFED6D65L;
    private static final long STOCK_CRC = 0x38C63335L;

    private static final long COMP_ADDR = 0x00125800L;
    private static final long PADDING_START = 0x00125086L;
    private static final long PADDING_END = 0x00125FFBL;

    private static final long CALL_SITE = 0x000771A4L;
    private static final byte[] EXPECTED_CALL = new byte[] {
        (byte)0x78, (byte)0x01, (byte)0xE5, (byte)0x81
    };

    private static final long UPDATER_ENTRY = 0x00095724L;
    private static final byte[] EXPECTED_UPDATER = new byte[] {
        (byte)0x18, (byte)0x21, (byte)0x06, (byte)0xC8
    };

    private static final long RUNTIME_LOAD = 0x00087110L;
    private static final byte[] EXPECTED_RUNTIME = new byte[] {
        (byte)0x48, (byte)0x20
    };

    private static final long AUTOPILOT_VALUE_ADDR = 0x0001CDBDL;
    private static final int EXPECTED_AUTOPILOT_VALUE = 0x32;

    private static final int FLAGS_OFFSET = 0x0C;
    private static final int WATCHED_FLAG = 0x00000080;
    private static final int ALLOWED_DESCRIPTOR_FLAGS = WATCHED_FLAG;
    private static final long AUTOPILOT_DESCRIPTOR = 0x00024D58L;

    private static final long STRING_MIN = 0x00023000L;
    private static final long STRING_MAX = 0x00025000L;
    private static final int MAX_NAME_LENGTH = 96;

    private static final long CLEAN_RETURN_ZERO = 0x00095604L;

    /*
     * VLE e_b encodes a signed 24-bit byte displacement:
     *   0x79 | displacement[23:0]
     */
    private static final BranchPatch[] BRANCH_PATCHES =
        new BranchPatch[] {
            new BranchPatch(
                0x00095572L,
                "reason 4: null/missing fallback structure",
                new byte[] {
                    (byte)0x79, (byte)0xFF, (byte)0xFE, (byte)0x6A
                },
                new byte[] {
                    (byte)0x79, (byte)0x00, (byte)0x00, (byte)0x92
                }
            ),
            new BranchPatch(
                0x000955F4L,
                "reason 4: empty/malformed fallback value",
                new byte[] {
                    (byte)0x79, (byte)0xFF, (byte)0xFD, (byte)0xE8
                },
                new byte[] {
                    (byte)0x79, (byte)0x00, (byte)0x00, (byte)0x10
                }
            ),
            new BranchPatch(
                0x00095634L,
                "reason 4: fallback key exhausted/missing",
                new byte[] {
                    (byte)0x79, (byte)0xFF, (byte)0xFD, (byte)0xA8
                },
                new byte[] {
                    (byte)0x79, (byte)0xFF, (byte)0xFF, (byte)0xD0
                }
            ),
            new BranchPatch(
                0x00095720L,
                "reason 5: fallback value differs",
                new byte[] {
                    (byte)0x79, (byte)0xFF, (byte)0xFC, (byte)0xBC
                },
                new byte[] {
                    (byte)0x79, (byte)0xFF, (byte)0xFE, (byte)0xE4
                }
            )
        };

    private static final ExpectedDescriptor[] EXPECTED_DESCRIPTORS =
        new ExpectedDescriptor[] {
            new ExpectedDescriptor(0x00024C08L, "isEbuck"),
            new ExpectedDescriptor(0x00024C18L, "updateWhatYouSee"),
            new ExpectedDescriptor(0x00024CF8L, "freeSlaveCharger"),
            new ExpectedDescriptor(0x00024D18L, "navigationAllowed"),
            new ExpectedDescriptor(0x00024D58L, "autopilot"),
            new ExpectedDescriptor(0x00024D68L, "xcpEsp"),
            new ExpectedDescriptor(0x00024D78L, "xcpIbst"),
            new ExpectedDescriptor(0x00024DA8L, "softPackConfig"),
            new ExpectedDescriptor(0x00024E58L, "performanceAddOn"),
            new ExpectedDescriptor(0x00024F18L, "r79BehaviorOverride"),
            new ExpectedDescriptor(0x00024F78L, "efficiencyPackage"),
            new ExpectedDescriptor(0x00025088L, "gtwEnableLatencyLogging"),
            new ExpectedDescriptor(0x00025098L, "connectivityPackage"),
            new ExpectedDescriptor(0x000250A8L, "deliveryStatus"),
            new ExpectedDescriptor(0x000250D8L, "birthday")
        };

    @Override
    protected void run() throws Exception {
        if (currentProgram == null) {
            popup("No program is open.");
            return;
        }

        Memory memory = currentProgram.getMemory();

        if (!verifyCoreState(memory)) {
            return;
        }

        long appSize = readU32BE(memory, addr(APP_SIZE_ADDR));
        long appSizeInv = readU32BE(memory, addr(APP_SIZE_INV_ADDR));

        if (appSize != EXPECTED_APP_SIZE ||
            appSizeInv != EXPECTED_APP_SIZE_INV ||
            appSizeInv != ((~appSize) & 0xffffffffL)) {

            popup(String.format(
                Locale.ROOT,
                "Application size header is invalid.\n\n" +
                "Size:       0x%08X\n" +
                "Complement: 0x%08X",
                appSize,
                appSizeInv
            ));
            return;
        }

        byte[] currentImage =
            readBytes(memory, addr(APP_START), (int)appSize);

        long storedBefore =
            readU32BE(memory, addr(APP_CRC_ADDR));
        long calculatedBefore =
            calculateCrc(currentImage);

        if (storedBefore != STOCK_CRC ||
            calculatedBefore != STOCK_CRC) {

            popup(String.format(
                Locale.ROOT,
                "Current image is not the expected CRC-neutral base.\n\n" +
                "Stored CRC32:     0x%08X\n" +
                "Calculated CRC32: 0x%08X\n" +
                "Required CRC32:   0x%08X",
                storedBefore,
                calculatedBefore,
                STOCK_CRC
            ));
            return;
        }

        verifyPaddingRun(currentImage);

        List<DescriptorState> descriptors =
            readDescriptorStates(memory);

        for (BranchPatch patch : BRANCH_PATCHES) {
            byte[] actual =
                readBytes(memory, addr(patch.address), 4);

            if (!same(actual, patch.original) &&
                !same(actual, patch.patched)) {

                popup(
                    "Unexpected bytes at fallback branch.\n\n" +
                    String.format(
                        Locale.ROOT,
                        "Address:  0x%08X\n",
                        patch.address
                    ) +
                    "Purpose:  " + patch.description + "\n" +
                    "Original: " + toHex(patch.original) + "\n" +
                    "Patched:  " + toHex(patch.patched) + "\n" +
                    "Found:    " + toHex(actual)
                );
                return;
            }
        }

        byte[] proposedImage = currentImage.clone();
        List<Change> descriptorChanges = new ArrayList<Change>();
        List<Change> branchChanges = new ArrayList<Change>();

        for (DescriptorState descriptor : descriptors) {
            int targetFlags =
                descriptor.address == AUTOPILOT_DESCRIPTOR
                    ? 0
                    : WATCHED_FLAG;

            if (descriptor.flags != targetFlags) {
                descriptorChanges.add(
                    new Change(
                        descriptor.address + FLAGS_OFFSET,
                        descriptor.name,
                        intToBE(descriptor.flags),
                        intToBE(targetFlags)
                    )
                );
            }

            writeIntBE(
                proposedImage,
                offsetInApplication(
                    descriptor.address + FLAGS_OFFSET
                ),
                targetFlags
            );
        }

        for (BranchPatch patch : BRANCH_PATCHES) {
            byte[] actual =
                readBytes(memory, addr(patch.address), 4);

            if (!same(actual, patch.patched)) {
                branchChanges.add(
                    new Change(
                        patch.address,
                        patch.description,
                        actual,
                        patch.patched
                    )
                );
            }

            putBytes(
                proposedImage,
                patch.address,
                patch.patched
            );
        }

        byte[] compensationBefore =
            readBytes(memory, addr(COMP_ADDR), 4);

        int compensationOffset =
            offsetInApplication(COMP_ADDR);

        for (int index = 0; index < 4; index++) {
            proposedImage[compensationOffset + index] = 0;
        }

        byte[] compensationAfter =
            solveFourBytePatch(
                proposedImage,
                compensationOffset,
                STOCK_CRC
            );

        if (compensationAfter == null) {
            popup("CRC compensation solver failed.");
            return;
        }

        System.arraycopy(
            compensationAfter,
            0,
            proposedImage,
            compensationOffset,
            4
        );

        long finalProposedCrc =
            calculateCrc(proposedImage);

        if (finalProposedCrc != STOCK_CRC) {
            popup(String.format(
                Locale.ROOT,
                "Proposed image failed CRC-neutral verification.\n\n" +
                "Calculated: 0x%08X\n" +
                "Required:   0x%08X",
                finalProposedCrc,
                STOCK_CRC
            ));
            return;
        }

        StringBuilder branchSummary = new StringBuilder();

        for (BranchPatch patch : BRANCH_PATCHES) {
            byte[] before =
                readBytes(memory, addr(patch.address), 4);

            branchSummary.append(
                String.format(
                    Locale.ROOT,
                    "0x%08X  %-43s\n" +
                    "            %s -> %s  e_b 0x%08X\n",
                    patch.address,
                    patch.description,
                    toHex(before),
                    toHex(patch.patched),
                    CLEAN_RETURN_ZERO
                )
            );
        }

        StringBuilder descriptorSummary = new StringBuilder();

        for (DescriptorState descriptor : descriptors) {
            int targetFlags =
                descriptor.address == AUTOPILOT_DESCRIPTOR
                    ? 0
                    : WATCHED_FLAG;

            descriptorSummary.append(
                String.format(
                    Locale.ROOT,
                    "0x%08X  %-30s  %08X -> %08X  %s%n",
                    descriptor.address + FLAGS_OFFSET,
                    descriptor.name,
                    descriptor.flags,
                    targetFlags,
                    descriptor.flags == targetFlags
                        ? "[already correct]"
                        : "[change]"
                )
            );
        }

        String confirmation =
            "Apply corrected V6/AP no-pending diagnostic?\n\n" +
            "The prior V1 test incorrectly restored autopilot to 0x80, which\n" +
            "re-enabled reason 3 whenever Tesla supplied autopilot=0.\n\n" +
            "This corrected build keeps AP at 0x00, restores the other 14\n" +
            "watched descriptors to 0x80, and redirects only reason 4/5\n" +
            "fallback outcomes to FUN_00095354's clean return-0 epilogue.\n\n" +
            "Fallback branch patches:\n" +
            branchSummary.toString() +
            "\nDescriptor state:\n" +
            descriptorSummary.toString() +
            "\nFields restored: " + descriptorChanges.size() +
            "\nBranches changed: " + branchChanges.size() +
            "\nCRC compensation:\n" +
            "  " + toHex(compensationBefore) +
            " -> " + toHex(compensationAfter) +
            "\n\nStored/calculated CRC remains 0x38C63335.";

        if (!askYesNo(
                "Apply corrected config fallback/AP no-pending patch",
                confirmation)) {

            println("Cancelled.");
            return;
        }

        Register vle = currentProgram.getRegister("vle");

        if (vle == null) {
            popup(
                "The current program has no processor-context register named 'vle'."
            );
            return;
        }

        int transaction =
            currentProgram.startTransaction(
                "Apply corrected config fallback/AP no-pending patch"
            );
        boolean commit = false;

        try {
            for (Change change : descriptorChanges) {
                Address start = addr(change.address);
                clearListing(start, addr(change.address + 3));
                memory.setBytes(start, change.after);
            }

            for (BranchPatch patch : BRANCH_PATCHES) {
                Address start = addr(patch.address);
                Address end = addr(patch.address + 3);

                clearListing(start, end);

                currentProgram
                    .getProgramContext()
                    .setValue(
                        vle,
                        start,
                        end,
                        BigInteger.ONE
                    );

                memory.setBytes(start, patch.patched);
                disassemble(start);
            }

            Address compensationStart = addr(COMP_ADDR);

            clearListing(
                compensationStart,
                addr(COMP_ADDR + 3)
            );

            memory.setBytes(
                compensationStart,
                compensationAfter
            );

            memory.setBytes(
                addr(APP_CRC_ADDR),
                u32BE(STOCK_CRC)
            );

            commit = true;
        }
        finally {
            currentProgram.endTransaction(
                transaction,
                commit
            );
        }

        if (!commit) {
            popup(
                "Patch transaction failed and was rolled back."
            );
            return;
        }

        Verification verification =
            verifyFinalState(
                memory,
                descriptors,
                compensationAfter,
                appSize
            );

        File reportFile = askFile(
            "Save V6 fallback patch report",
            "Save"
        );

        writeReport(
            reportFile,
            descriptors,
            compensationBefore,
            compensationAfter,
            verification
        );

        popup(String.format(
            Locale.ROOT,
            "Corrected V6/AP fallback patch %s.\n\n" +
            "Descriptor flags:   %s\n" +
            "Fallback branches:  %s\n" +
            "Stored CRC32:       0x%08X\n" +
            "Calculated CRC32:   0x%08X\n" +
            "Compensation:       %s\n\n" +
            "Report:\n%s",
            verification.pass ? "verified" : "FAILED",
            verification.descriptorPass ? "PASS" : "FAIL",
            verification.branchPass ? "PASS" : "FAIL",
            verification.storedCrc,
            verification.calculatedCrc,
            toHex(verification.compensation),
            reportFile.getAbsolutePath()
        ));
    }

    private boolean verifyCoreState(
            Memory memory) throws Exception {

        byte[] call =
            readBytes(memory, addr(CALL_SITE), 4);
        byte[] updater =
            readBytes(memory, addr(UPDATER_ENTRY), 4);
        byte[] runtime =
            readBytes(memory, addr(RUNTIME_LOAD), 2);
        int autopilotValue =
            memory.getByte(
                addr(AUTOPILOT_VALUE_ADDR)
            ) & 0xff;

        boolean pass =
            same(call, EXPECTED_CALL) &&
            same(updater, EXPECTED_UPDATER) &&
            same(runtime, EXPECTED_RUNTIME) &&
            autopilotValue == EXPECTED_AUTOPILOT_VALUE;

        if (!pass) {
            popup(
                "Core runtime-AP image state is not present.\n\n" +
                "Call:       " + toHex(call) + "\n" +
                "Updater:    " + toHex(updater) + "\n" +
                "Runtime:    " + toHex(runtime) + "\n" +
                String.format(
                    Locale.ROOT,
                    "AP value:   %02X\n\n",
                    autopilotValue
                ) +
                "Expected:\n" +
                "  0x771A4 = 78 01 E5 81\n" +
                "  0x95724 = 18 21 06 C8\n" +
                "  0x87110 = 48 20\n" +
                "  0x1CDBD = 32"
            );
        }

        return pass;
    }

    private List<DescriptorState> readDescriptorStates(
            Memory memory) throws Exception {

        List<DescriptorState> result =
            new ArrayList<DescriptorState>();

        for (ExpectedDescriptor expected :
                EXPECTED_DESCRIPTORS) {

            long namePointer =
                readU32BE(
                    memory,
                    addr(expected.address)
                );

            if (namePointer < STRING_MIN ||
                namePointer >= STRING_MAX) {

                throw new IllegalStateException(
                    String.format(
                        Locale.ROOT,
                        "Invalid name pointer at descriptor 0x%08X: 0x%08X",
                        expected.address,
                        namePointer
                    )
                );
            }

            String actualName =
                readCString(memory, namePointer);

            if (!expected.name.equals(actualName)) {
                throw new IllegalStateException(
                    String.format(
                        Locale.ROOT,
                        "Descriptor identity mismatch at 0x%08X.\n" +
                        "Expected: %s\n" +
                        "Found:    %s",
                        expected.address,
                        expected.name,
                        actualName
                    )
                );
            }

            int flags =
                (int)readU32BE(
                    memory,
                    addr(
                        expected.address +
                        FLAGS_OFFSET
                    )
                );

            if ((flags & ~ALLOWED_DESCRIPTOR_FLAGS) != 0) {
                throw new IllegalStateException(
                    String.format(
                        Locale.ROOT,
                        "Unexpected descriptor flags at 0x%08X (%s).\n" +
                        "Found: 0x%08X\n" +
                        "Accepted: 0x00000000 or 0x00000080",
                        expected.address + FLAGS_OFFSET,
                        expected.name,
                        flags
                    )
                );
            }

            result.add(
                new DescriptorState(
                    expected.address,
                    expected.name,
                    flags
                )
            );
        }

        return result;
    }

    private Verification verifyFinalState(
            Memory memory,
            List<DescriptorState> descriptors,
            byte[] expectedCompensation,
            long appSize) throws Exception {

        boolean descriptorPass = true;

        for (DescriptorState descriptor :
                descriptors) {

            int expected =
                descriptor.address == AUTOPILOT_DESCRIPTOR
                    ? 0
                    : WATCHED_FLAG;

            int actual =
                (int)readU32BE(
                    memory,
                    addr(
                        descriptor.address +
                        FLAGS_OFFSET
                    )
                );

            if (actual != expected) {
                descriptorPass = false;
            }
        }

        boolean branchPass = true;

        for (BranchPatch patch : BRANCH_PATCHES) {
            byte[] actual =
                readBytes(
                    memory,
                    addr(patch.address),
                    4
                );

            if (!same(actual, patch.patched)) {
                branchPass = false;
            }
        }

        boolean corePass =
            same(
                readBytes(memory, addr(CALL_SITE), 4),
                EXPECTED_CALL
            ) &&
            same(
                readBytes(memory, addr(UPDATER_ENTRY), 4),
                EXPECTED_UPDATER
            ) &&
            same(
                readBytes(memory, addr(RUNTIME_LOAD), 2),
                EXPECTED_RUNTIME
            ) &&
            (
                memory.getByte(
                    addr(AUTOPILOT_VALUE_ADDR)
                ) & 0xff
            ) == EXPECTED_AUTOPILOT_VALUE;

        byte[] actualCompensation =
            readBytes(
                memory,
                addr(COMP_ADDR),
                4
            );

        byte[] finalImage =
            readBytes(
                memory,
                addr(APP_START),
                (int)appSize
            );

        long stored =
            readU32BE(
                memory,
                addr(APP_CRC_ADDR)
            );
        long calculated =
            calculateCrc(finalImage);

        boolean pass =
            descriptorPass &&
            branchPass &&
            corePass &&
            same(
                actualCompensation,
                expectedCompensation
            ) &&
            stored == STOCK_CRC &&
            calculated == STOCK_CRC;

        return new Verification(
            pass,
            descriptorPass,
            branchPass,
            corePass,
            stored,
            calculated,
            actualCompensation
        );
    }

    private void writeReport(
            File file,
            List<DescriptorState> descriptors,
            byte[] compensationBefore,
            byte[] compensationAfter,
            Verification verification) throws Exception {

        PrintWriter writer =
            new PrintWriter(file, "UTF-8");

        try {
            writer.println(
                "Tesla Config Fallback and AP No-Pending Patch Report V2"
            );
            writer.println(
                "================================================"
            );
            writer.println();
            writer.println(
                "Created: " +
                new SimpleDateFormat(
                    "yyyy-MM-dd HH:mm:ss"
                ).format(new Date())
            );
            writer.println(
                "Program: " +
                currentProgram.getName()
            );
            writer.println();

            writer.println("V6 outcome applied");
            writer.println("------------------");
            writer.printf(
                Locale.ROOT,
                "Clean return-0 target: 0x%08X%n",
                CLEAN_RETURN_ZERO
            );
            writer.println();

            for (BranchPatch patch : BRANCH_PATCHES) {
                writer.printf(
                    Locale.ROOT,
                    "0x%08X  %s%n",
                    patch.address,
                    patch.description
                );
                writer.println(
                    "  Original: " +
                    toHex(patch.original)
                );
                writer.println(
                    "  Patched:  " +
                    toHex(patch.patched)
                );
            }

            writer.println();
            writer.println("Descriptor watch state");
            writer.println("----------------------");

            for (DescriptorState descriptor :
                    descriptors) {

                int targetFlags =
                    descriptor.address == AUTOPILOT_DESCRIPTOR
                        ? 0
                        : WATCHED_FLAG;

                writer.printf(
                    Locale.ROOT,
                    "0x%08X  %-30s  %08X -> %08X%n",
                    descriptor.address + FLAGS_OFFSET,
                    descriptor.name,
                    descriptor.flags,
                    targetFlags
                );
            }

            writer.println();
            writer.println(
                "Compensation before: " +
                toHex(compensationBefore)
            );
            writer.println(
                "Compensation after:  " +
                toHex(compensationAfter)
            );
            writer.printf(
                Locale.ROOT,
                "Stored CRC32:         0x%08X%n",
                verification.storedCrc
            );
            writer.printf(
                Locale.ROOT,
                "Calculated CRC32:     0x%08X%n",
                verification.calculatedCrc
            );
            writer.println();
            writer.println(
                "Descriptor verification: " +
                (
                    verification.descriptorPass
                        ? "PASS"
                        : "FAIL"
                )
            );
            writer.println(
                "Fallback branch verification: " +
                (
                    verification.branchPass
                        ? "PASS"
                        : "FAIL"
                )
            );
            writer.println(
                "Core runtime-AP verification: " +
                (
                    verification.corePass
                        ? "PASS"
                        : "FAIL"
                )
            );
            writer.println(
                "Overall verification: " +
                (
                    verification.pass
                        ? "PASS"
                        : "FAIL"
                )
            );
        }
        finally {
            writer.close();
        }
    }

    private void verifyPaddingRun(
            byte[] image) {

        int start =
            offsetInApplication(PADDING_START);
        int end =
            offsetInApplication(PADDING_END);
        int compensation =
            offsetInApplication(COMP_ADDR);

        for (int offset = start;
             offset <= end;
             offset++) {

            boolean inCompensation =
                offset >= compensation &&
                offset < compensation + 4;

            if (!inCompensation &&
                image[offset] != 0) {

                throw new IllegalStateException(
                    String.format(
                        Locale.ROOT,
                        "Padding is nonzero at 0x%08X: %02X",
                        APP_START + offset,
                        image[offset] & 0xff
                    )
                );
            }
        }
    }

    private String readCString(
            Memory memory,
            long address) throws Exception {

        StringBuilder builder =
            new StringBuilder();

        for (int index = 0;
             index < MAX_NAME_LENGTH;
             index++) {

            int value =
                memory.getByte(
                    addr(address + index)
                ) & 0xff;

            if (value == 0) {
                break;
            }

            if (value < 0x20 ||
                value > 0x7e) {
                return "";
            }

            builder.append((char)value);
        }

        return builder.toString();
    }

    private void putBytes(
            byte[] image,
            long absoluteAddress,
            byte[] value) {

        int offset =
            offsetInApplication(
                absoluteAddress
            );

        System.arraycopy(
            value,
            0,
            image,
            offset,
            value.length
        );
    }

    private byte[] solveFourBytePatch(
            byte[] source,
            int offset,
            long target) {

        byte[] work = source.clone();

        work[0] = 0;
        work[1] = 0;
        work[2] = 0;
        work[3] = 0;

        for (int index = 0;
             index < 4;
             index++) {
            work[offset + index] = 0;
        }

        long base = rawCrc(work);
        long rhs =
            (target ^ base) &
            0xffffffffL;

        long[] basisVector =
            new long[32];
        int[] basisMask =
            new int[32];

        for (int variable = 0;
             variable < 32;
             variable++) {

            int byteIndex =
                variable / 8;
            int bitInByte =
                7 - (variable % 8);

            work[offset + byteIndex] =
                (byte)(1 << bitInByte);

            long vector =
                (rawCrc(work) ^ base) &
                0xffffffffL;
            int mask =
                1 << variable;

            work[offset + byteIndex] = 0;

            for (int bit = 31;
                 bit >= 0;
                 bit--) {

                long bitMask = 1L << bit;

                if ((vector & bitMask) == 0) {
                    continue;
                }

                if (basisVector[bit] == 0) {
                    basisVector[bit] = vector;
                    basisMask[bit] = mask;
                    vector = 0;
                    break;
                }

                vector ^= basisVector[bit];
                mask ^= basisMask[bit];
            }
        }

        long remaining = rhs;
        int solution = 0;

        for (int bit = 31;
             bit >= 0;
             bit--) {

            long bitMask = 1L << bit;

            if ((remaining & bitMask) == 0) {
                continue;
            }

            if (basisVector[bit] == 0) {
                return null;
            }

            remaining ^= basisVector[bit];
            solution ^= basisMask[bit];
        }

        if (remaining != 0) {
            return null;
        }

        byte[] patch =
            new byte[4];

        for (int variable = 0;
             variable < 32;
             variable++) {

            if ((solution &
                (1 << variable)) == 0) {
                continue;
            }

            int byteIndex =
                variable / 8;
            int bitInByte =
                7 - (variable % 8);

            patch[byteIndex] |=
                (byte)(1 << bitInByte);
        }

        return patch;
    }

    private long calculateCrc(
            byte[] source) {

        byte[] image = source.clone();

        image[0] = 0;
        image[1] = 0;
        image[2] = 0;
        image[3] = 0;

        return rawCrc(image);
    }

    private long rawCrc(
            byte[] image) {

        CRC32 crc = new CRC32();
        crc.update(image);

        return crc.getValue() &
            0xffffffffL;
    }

    private int offsetInApplication(
            long absoluteAddress) {

        long offset =
            absoluteAddress - APP_START;

        if (offset < 0 ||
            offset > Integer.MAX_VALUE) {
            throw new IllegalArgumentException(
                "Address outside application: 0x" +
                Long.toHexString(
                    absoluteAddress
                )
            );
        }

        return (int)offset;
    }

    private void writeIntBE(
            byte[] data,
            int offset,
            int value) {

        data[offset] =
            (byte)((value >>> 24) & 0xff);
        data[offset + 1] =
            (byte)((value >>> 16) & 0xff);
        data[offset + 2] =
            (byte)((value >>> 8) & 0xff);
        data[offset + 3] =
            (byte)(value & 0xff);
    }

    private byte[] intToBE(
            int value) {

        return new byte[] {
            (byte)((value >>> 24) & 0xff),
            (byte)((value >>> 16) & 0xff),
            (byte)((value >>> 8) & 0xff),
            (byte)(value & 0xff)
        };
    }

    private byte[] u32BE(
            long value) {

        return new byte[] {
            (byte)((value >>> 24) & 0xff),
            (byte)((value >>> 16) & 0xff),
            (byte)((value >>> 8) & 0xff),
            (byte)(value & 0xff)
        };
    }

    private long readU32BE(
            Memory memory,
            Address address) throws Exception {

        byte[] bytes =
            readBytes(memory, address, 4);

        return ((long)(bytes[0] & 0xff) << 24) |
               ((long)(bytes[1] & 0xff) << 16) |
               ((long)(bytes[2] & 0xff) << 8) |
               ((long)(bytes[3] & 0xff));
    }

    private byte[] readBytes(
            Memory memory,
            Address address,
            int length) throws Exception {

        byte[] bytes = new byte[length];

        int read =
            memory.getBytes(address, bytes);

        if (read != length) {
            throw new IllegalStateException(
                "Read " + read +
                " of " + length +
                " bytes at " + address
            );
        }

        return bytes;
    }

    private boolean same(
            byte[] first,
            byte[] second) {

        if (first.length != second.length) {
            return false;
        }

        for (int index = 0;
             index < first.length;
             index++) {

            if (first[index] != second[index]) {
                return false;
            }
        }

        return true;
    }

    private String toHex(
            byte[] bytes) {

        StringBuilder builder =
            new StringBuilder();

        for (int index = 0;
             index < bytes.length;
             index++) {

            if (index > 0) {
                builder.append(' ');
            }

            builder.append(
                String.format(
                    Locale.ROOT,
                    "%02X",
                    bytes[index] & 0xff
                )
            );
        }

        return builder.toString();
    }

    private Address addr(
            long value) {

        return currentProgram
            .getAddressFactory()
            .getDefaultAddressSpace()
            .getAddress(value);
    }

    private static class BranchPatch {
        final long address;
        final String description;
        final byte[] original;
        final byte[] patched;

        BranchPatch(
                long address,
                String description,
                byte[] original,
                byte[] patched) {

            this.address = address;
            this.description = description;
            this.original = original;
            this.patched = patched;
        }
    }

    private static class ExpectedDescriptor {
        final long address;
        final String name;

        ExpectedDescriptor(
                long address,
                String name) {

            this.address = address;
            this.name = name;
        }
    }

    private static class DescriptorState {
        final long address;
        final String name;
        final int flags;

        DescriptorState(
                long address,
                String name,
                int flags) {

            this.address = address;
            this.name = name;
            this.flags = flags;
        }
    }

    private static class Change {
        final long address;
        final String description;
        final byte[] before;
        final byte[] after;

        Change(
                long address,
                String description,
                byte[] before,
                byte[] after) {

            this.address = address;
            this.description = description;
            this.before = before;
            this.after = after;
        }
    }

    private static class Verification {
        final boolean pass;
        final boolean descriptorPass;
        final boolean branchPass;
        final boolean corePass;
        final long storedCrc;
        final long calculatedCrc;
        final byte[] compensation;

        Verification(
                boolean pass,
                boolean descriptorPass,
                boolean branchPass,
                boolean corePass,
                long storedCrc,
                long calculatedCrc,
                byte[] compensation) {

            this.pass = pass;
            this.descriptorPass =
                descriptorPass;
            this.branchPass = branchPass;
            this.corePass = corePass;
            this.storedCrc = storedCrc;
            this.calculatedCrc =
                calculatedCrc;
            this.compensation =
                compensation;
        }
    }
}
