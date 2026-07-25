// Export the active Ghidra program as a complete 2 MiB MPC5668G CFLASH image
// and as a Motorola S-record file matching the existing PEmicro backup layout.
//
// V10 validates AP excluded from watched changes, the other 14 descriptor
// flags restored, reason-4/reason-5 fallback branches redirected, runtime
// autopilot=2, and stock CRC compensation.
//
// @category Tesla.Export
// @author OpenAI

import ghidra.app.script.GhidraScript;
import ghidra.program.model.address.Address;
import ghidra.program.model.address.AddressSpace;
import ghidra.program.model.mem.Memory;

import java.io.BufferedInputStream;
import java.io.BufferedOutputStream;
import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.nio.charset.StandardCharsets;
import java.security.MessageDigest;
import java.util.Locale;
import java.util.zip.CRC32;

public class TeslaFullCflashS19ExporterV10 extends GhidraScript {

    private static final long START = 0x00000000L;
    private static final long END = 0x001fffffL;
    private static final int IMAGE_SIZE = 0x00200000;
    private static final int RECORD_DATA_LENGTH = 16;

    private static final long CALL_SITE_ADDRESS = 0x000771a4L;
    private static final byte[] ORIGINAL_CALL_BYTES = new byte[] {
        (byte) 0x78, (byte) 0x01, (byte) 0xe5, (byte) 0x81
    };

    private static final long UPDATER_ENTRY_ADDRESS = 0x00095724L;
    private static final byte[] STOCK_UPDATER_ENTRY_BYTES = new byte[] {
        (byte) 0x18, (byte) 0x21, (byte) 0x06, (byte) 0xc8
    };

    private static final long RUNTIME_VALUE_LOAD_ADDRESS = 0x00087110L;
    private static final byte[] FORCE_RUNTIME_TWO_BYTES = new byte[] {
        (byte) 0x48, (byte) 0x20
    };

    private static final long AUTOPILOT_VALUE_ADDRESS = 0x0001cdbdL;
    private static final int AUTOPILOT_VALUE_REQUIRED = 0x32; // ASCII '2'

    private static final long DESCRIPTOR_TABLE_START = 0x00024bf8L;
    private static final int DESCRIPTOR_COUNT = 84;
    private static final int DESCRIPTOR_STRIDE = 0x10;
    private static final int DESCRIPTOR_FLAGS_OFFSET = 0x0c;
    private static final long WATCHED_FLAG_MASK = 0x00000080L;

    private static final long AUTOPILOT_DESCRIPTOR_FLAGS_ADDRESS = 0x00024d64L;
    private static final byte[] AUTOPILOT_DESCRIPTOR_FLAGS_REQUIRED =
        new byte[] {
            (byte) 0x00, (byte) 0x00, (byte) 0x00, (byte) 0x00
        };

    private static final long[] FALLBACK_BRANCH_ADDRESSES =
        new long[] {
            0x00095572L,
            0x000955f4L,
            0x00095634L,
            0x00095720L
        };

    private static final byte[][] FALLBACK_BRANCH_BYTES =
        new byte[][] {
            new byte[] {
                (byte) 0x79, (byte) 0x00, (byte) 0x00, (byte) 0x92
            },
            new byte[] {
                (byte) 0x79, (byte) 0x00, (byte) 0x00, (byte) 0x10
            },
            new byte[] {
                (byte) 0x79, (byte) 0xff, (byte) 0xff, (byte) 0xd0
            },
            new byte[] {
                (byte) 0x79, (byte) 0xff, (byte) 0xfe, (byte) 0xe4
            }
        };

    private static final long APP_HEADER_ADDRESS = 0x00020000L;
    private static final long APP_CRC_ADDRESS = 0x00020000L;
    private static final long APP_SIZE_ADDRESS = 0x00020004L;
    private static final long APP_SIZE_INVERSE_ADDRESS = 0x00020008L;

    private static final long EXPECTED_APP_SIZE = 0x0012929aL;
    private static final long EXPECTED_APP_SIZE_INVERSE = 0xffed6d65L;
    private static final long REQUIRED_STOCK_APP_CRC = 0x38c63335L;

    private static final long PADDING_START_ADDRESS = 0x00125086L;
    private static final long PADDING_END_ADDRESS = 0x00125ffbL;
    private static final long COMPENSATION_ADDRESS = 0x00125800L;

    private Memory memory;
    private AddressSpace addressSpace;
    private int missingByteCount;

    @Override
    protected void run() throws Exception {
        if (currentProgram == null) {
            popup("No program is open.");
            return;
        }

        memory = currentProgram.getMemory();
        addressSpace = currentProgram.getAddressFactory().getDefaultAddressSpace();

        println("Tesla full CFLASH BIN/S19 exporter");
        println("Program: " + currentProgram.getName());
        println(String.format(Locale.ROOT, "Range: 0x%08X-0x%08X", START, END));

        byte[] callSite = readRange(
            CALL_SITE_ADDRESS, ORIGINAL_CALL_BYTES.length, false);
        if (!equalsBytes(callSite, ORIGINAL_CALL_BYTES)) {
            popup("Export stopped: the original updater call is not present at 0x771A4.\n" +
                  "Expected: 78 01 E5 81\n" +
                  "Found:    " + toHex(callSite));
            return;
        }

        byte[] updaterEntry = readRange(
            UPDATER_ENTRY_ADDRESS, STOCK_UPDATER_ENTRY_BYTES.length, false);
        if (!equalsBytes(updaterEntry, STOCK_UPDATER_ENTRY_BYTES)) {
            popup("Export stopped: the stock updater entry is not present at 0x95724.\n" +
                  "Expected: 18 21 06 C8\n" +
                  "Found:    " + toHex(updaterEntry));
            return;
        }

        byte[] runtimeForce = readRange(
            RUNTIME_VALUE_LOAD_ADDRESS, FORCE_RUNTIME_TWO_BYTES.length, false);
        if (!equalsBytes(runtimeForce, FORCE_RUNTIME_TWO_BYTES)) {
            popup("Export stopped: the runtime autopilot=2 patch is not present at 0x87110.\n" +
                  "Expected: 48 20\n" +
                  "Found:    " + toHex(runtimeForce));
            return;
        }

        byte[] descriptorFlags = readRange(
            AUTOPILOT_DESCRIPTOR_FLAGS_ADDRESS,
            AUTOPILOT_DESCRIPTOR_FLAGS_REQUIRED.length,
            false);
        if (!equalsBytes(
                descriptorFlags,
                AUTOPILOT_DESCRIPTOR_FLAGS_REQUIRED)) {
            popup("Export stopped: autopilot is still in the watched-change scan at 0x24D64.\n" +
                  "Expected: 00 00 00 00\n" +
                  "Found:    " + toHex(descriptorFlags));
            return;
        }

        int remainingWatchedFlags = 0;

        for (int descriptorIndex = 0;
             descriptorIndex < DESCRIPTOR_COUNT;
             descriptorIndex++) {

            long flagsAddress =
                DESCRIPTOR_TABLE_START +
                ((long) descriptorIndex * DESCRIPTOR_STRIDE) +
                DESCRIPTOR_FLAGS_OFFSET;

            long flags = readUnsignedIntBE(flagsAddress);

            if ((flags & WATCHED_FLAG_MASK) != 0) {
                remainingWatchedFlags++;
            }
        }

        if (remainingWatchedFlags != 14) {
            popup("Export stopped: corrected descriptor watch state is not present.\n" +
                  "Expected descriptors with bit 0x80: 14 (AP must be clear)\n" +
                  "Found: " + remainingWatchedFlags);
            return;
        }

        byte[][] fallbackBranches =
            new byte[FALLBACK_BRANCH_ADDRESSES.length][];

        for (int branchIndex = 0;
             branchIndex < FALLBACK_BRANCH_ADDRESSES.length;
             branchIndex++) {

            fallbackBranches[branchIndex] = readRange(
                FALLBACK_BRANCH_ADDRESSES[branchIndex],
                FALLBACK_BRANCH_BYTES[branchIndex].length,
                false);

            if (!equalsBytes(
                    fallbackBranches[branchIndex],
                    FALLBACK_BRANCH_BYTES[branchIndex])) {

                popup(String.format(Locale.ROOT,
                    "Export stopped: fallback branch patch missing.\n" +
                    "Address:  0x%08X\n" +
                    "Expected: %s\n" +
                    "Found:    %s",
                    FALLBACK_BRANCH_ADDRESSES[branchIndex],
                    toHex(FALLBACK_BRANCH_BYTES[branchIndex]),
                    toHex(fallbackBranches[branchIndex])));
                return;
            }
        }

        byte[] appHeader = readRange(APP_HEADER_ADDRESS, 12, false);
        long storedAppCrc = readUnsignedIntBE(APP_CRC_ADDRESS);
        long appSize = readUnsignedIntBE(APP_SIZE_ADDRESS);
        long appSizeInverse = readUnsignedIntBE(APP_SIZE_INVERSE_ADDRESS);

        if (appSize != EXPECTED_APP_SIZE ||
            appSizeInverse != EXPECTED_APP_SIZE_INVERSE ||
            appSizeInverse != ((~appSize) & 0xffffffffL)) {
            popup(String.format(Locale.ROOT,
                "Export stopped: the gateway application size header is invalid.\n" +
                "Expected size:       %08X\n" +
                "Found size:          %08X\n" +
                "Expected complement: %08X\n" +
                "Found complement:    %08X",
                EXPECTED_APP_SIZE, appSize,
                EXPECTED_APP_SIZE_INVERSE, appSizeInverse));
            return;
        }

        long calculatedAppCrc = calculateApplicationCrc((int) appSize);

        if (storedAppCrc != calculatedAppCrc) {
            popup(String.format(Locale.ROOT,
                "Export stopped: the stored gateway application CRC does not match the current bytes.\n" +
                "Stored CRC32:     %08X\n" +
                "Calculated CRC32: %08X",
                storedAppCrc, calculatedAppCrc));
            return;
        }

        if (storedAppCrc != REQUIRED_STOCK_APP_CRC) {
            popup(String.format(Locale.ROOT,
                "Export stopped: this is not a CRC-neutral image.\n" +
                "Required stock CRC32: %08X\n" +
                "Stored CRC32:         %08X",
                REQUIRED_STOCK_APP_CRC, storedAppCrc));
            return;
        }

        byte[] compensationBytes = readRange(
            COMPENSATION_ADDRESS, 4, false);

        if (equalsBytes(
                compensationBytes,
                new byte[] {0, 0, 0, 0})) {
            popup("Export stopped: the CRC compensation slot at 0x125800 is blank.");
            return;
        }

        int paddingLength =
            (int)(PADDING_END_ADDRESS - PADDING_START_ADDRESS + 1);
        byte[] paddingRun = readRange(
            PADDING_START_ADDRESS, paddingLength, false);

        int compensationOffset =
            (int)(COMPENSATION_ADDRESS - PADDING_START_ADDRESS);

        for (int i = 0; i < paddingRun.length; i++) {
            boolean inCompensation =
                i >= compensationOffset &&
                i < compensationOffset + 4;

            if (!inCompensation && paddingRun[i] != 0) {
                popup(String.format(Locale.ROOT,
                    "Export stopped: padding run contains an unexpected nonzero byte.\n" +
                    "Address: %08X\nValue:   %02X",
                    PADDING_START_ADDRESS + i,
                    paddingRun[i] & 0xff));
                return;
            }
        }

        int autopilotValue = readUnsignedByte(AUTOPILOT_VALUE_ADDRESS, false);
        if (autopilotValue != AUTOPILOT_VALUE_REQUIRED) {
            popup(String.format(Locale.ROOT,
                "Export stopped: autopilot is not set to ASCII '2' at 0x%08X.\n" +
                "Expected: 32\nFound:    %02X\n\n" +
                "Patch the configuration value before exporting, otherwise the shim will preserve the wrong value.",
                AUTOPILOT_VALUE_ADDRESS, autopilotValue));
            return;
        }

        File outputDirectory = askDirectory("Choose firmware export directory", "Export");
        File binFile = new File(outputDirectory, "Tesla_MCU1_ConfigFallback_AP_NoPending_CRCNeutral.bin");
        File s19File = new File(outputDirectory, "Tesla_MCU1_ConfigFallback_AP_NoPending_CRCNeutral.S19");
        File reportFile = new File(outputDirectory, "Tesla_MCU1_ConfigFallback_AP_NoPending_CRCNeutral_export_report.txt");

        if ((binFile.exists() || s19File.exists() || reportFile.exists()) &&
            !askYesNo("Overwrite existing exports?",
                "One or more output files already exist in:\n" + outputDirectory.getAbsolutePath() +
                "\n\nOverwrite them?")) {
            println("Export cancelled.");
            return;
        }

        missingByteCount = 0;
        byte[] image = readRange(START, IMAGE_SIZE, true);
        if (monitor.isCancelled()) {
            println("Export cancelled.");
            return;
        }

        writeBinary(binFile, image);
        writeS19(s19File, image);

        S19Validation validation = validateS19(s19File);
        String binSha256 = sha256(binFile);
        String s19Sha256 = sha256(s19File);

        writeReport(reportFile, binFile, s19File, validation, binSha256, s19Sha256,
            callSite, updaterEntry, runtimeForce, descriptorFlags,
            fallbackBranches, compensationBytes, appHeader, autopilotValue,
            storedAppCrc, calculatedAppCrc,
            appSize, appSizeInverse);

        println("Export complete:");
        println("  BIN:    " + binFile.getAbsolutePath());
        println("  S19:    " + s19File.getAbsolutePath());
        println("  Report: " + reportFile.getAbsolutePath());
        println("  BIN SHA-256: " + binSha256);
        println("  S19 SHA-256: " + s19Sha256);
        println("  S-record validation: " + (validation.valid ? "PASS" : "FAIL"));

        popup("Firmware export completed.\n\n" +
              "S19 validation: " + (validation.valid ? "PASS" : "FAIL") + "\n" +
              "Records: " + validation.totalRecords + "\n" +
              "Missing Ghidra bytes filled with FF: " + missingByteCount + "\n\n" +
              "Review the generated report before flashing.");
    }

    private byte[] readRange(long start, int length, boolean fillMissingWithFF) throws Exception {
        byte[] result = new byte[length];
        for (int i = 0; i < length; i++) {
            if ((i & 0x3fff) == 0) {
                monitor.setProgress(i);
                monitor.setMessage(String.format(Locale.ROOT,
                    "Reading CFLASH at 0x%08X", start + i));
                if (monitor.isCancelled()) {
                    return result;
                }
            }

            Address address = addressSpace.getAddress(start + i);
            try {
                if (!memory.contains(address)) {
                    throw new Exception("Address is not mapped");
                }
                result[i] = memory.getByte(address);
            }
            catch (Exception ex) {
                if (!fillMissingWithFF) {
                    throw new Exception(String.format(Locale.ROOT,
                        "Cannot read required byte at 0x%08X", start + i), ex);
                }
                result[i] = (byte) 0xff;
                missingByteCount++;
            }
        }
        return result;
    }

    private int readUnsignedByte(long address, boolean fillMissingWithFF) throws Exception {
        return readRange(address, 1, fillMissingWithFF)[0] & 0xff;
    }

    private long readUnsignedIntBE(long address) throws Exception {
        byte[] bytes = readRange(address, 4, false);
        return ((long) (bytes[0] & 0xff) << 24) |
               ((long) (bytes[1] & 0xff) << 16) |
               ((long) (bytes[2] & 0xff) << 8) |
               ((long) (bytes[3] & 0xff));
    }

    private long calculateApplicationCrc(int appSize) throws Exception {
        byte[] appImage = readRange(APP_HEADER_ADDRESS, appSize, false);

        // The loader calculates over the complete application image while
        // treating the stored CRC field at 0x20000-0x20003 as four zero bytes.
        appImage[0] = 0;
        appImage[1] = 0;
        appImage[2] = 0;
        appImage[3] = 0;

        CRC32 crc32 = new CRC32();
        crc32.update(appImage);
        return crc32.getValue() & 0xffffffffL;
    }

    private void writeBinary(File file, byte[] image) throws Exception {
        monitor.setMessage("Writing raw 2 MiB binary");
        BufferedOutputStream output = new BufferedOutputStream(new FileOutputStream(file));
        try {
            output.write(image);
        }
        finally {
            output.close();
        }
    }

    private void writeS19(File file, byte[] image) throws Exception {
        monitor.setMessage("Writing Motorola S-record file");
        BufferedWriter writer = new BufferedWriter(new OutputStreamWriter(
            new FileOutputStream(file), StandardCharsets.US_ASCII));
        try {
            for (int offset = 0; offset < image.length; offset += RECORD_DATA_LENGTH) {
                if ((offset & 0x3fff) == 0) {
                    monitor.setProgress(offset);
                    monitor.setMessage(String.format(Locale.ROOT,
                        "Writing S-record at 0x%08X", offset));
                    if (monitor.isCancelled()) {
                        throw new Exception("Export cancelled while writing S19");
                    }
                }

                int dataLength = Math.min(RECORD_DATA_LENGTH, image.length - offset);
                writer.write(makeSRecord(offset, image, offset, dataLength));
                writer.write("\r\n");
            }
        }
        finally {
            writer.close();
        }
    }

    private String makeSRecord(int address, byte[] source, int sourceOffset, int dataLength) {
        int addressBytes = address <= 0xffff ? 2 : 3;
        char recordType = addressBytes == 2 ? '1' : '2';
        int count = addressBytes + dataLength + 1;
        int sum = count;

        StringBuilder line = new StringBuilder(2 + 2 + (addressBytes * 2) + (dataLength * 2) + 2);
        line.append('S').append(recordType);
        appendHexByte(line, count);

        for (int shift = (addressBytes - 1) * 8; shift >= 0; shift -= 8) {
            int value = (address >>> shift) & 0xff;
            appendHexByte(line, value);
            sum += value;
        }

        for (int i = 0; i < dataLength; i++) {
            int value = source[sourceOffset + i] & 0xff;
            appendHexByte(line, value);
            sum += value;
        }

        appendHexByte(line, (~sum) & 0xff);
        return line.toString();
    }

    private void appendHexByte(StringBuilder builder, int value) {
        final char[] hex = "0123456789ABCDEF".toCharArray();
        builder.append(hex[(value >>> 4) & 0x0f]);
        builder.append(hex[value & 0x0f]);
    }

    private S19Validation validateS19(File file) throws Exception {
        S19Validation result = new S19Validation();
        result.valid = true;
        int expectedAddress = 0;

        BufferedReader reader = new BufferedReader(new InputStreamReader(
            new FileInputStream(file), StandardCharsets.US_ASCII));
        try {
            String line;
            int lineNumber = 0;
            while ((line = reader.readLine()) != null) {
                lineNumber++;
                if (line.length() == 0) {
                    continue;
                }

                if (line.length() < 10 || line.charAt(0) != 'S') {
                    result.fail("Invalid record syntax at line " + lineNumber);
                    break;
                }

                char type = line.charAt(1);
                int addressBytes;
                if (type == '1') {
                    addressBytes = 2;
                    result.s1Records++;
                }
                else if (type == '2') {
                    addressBytes = 3;
                    result.s2Records++;
                }
                else {
                    result.fail("Unexpected record type S" + type + " at line " + lineNumber);
                    break;
                }

                int count = parseHexByte(line, 2);
                if (line.length() != 4 + (count * 2)) {
                    result.fail("Record length mismatch at line " + lineNumber);
                    break;
                }

                int sum = count;
                int address = 0;
                int cursor = 4;
                for (int i = 0; i < addressBytes; i++) {
                    int value = parseHexByte(line, cursor);
                    cursor += 2;
                    sum += value;
                    address = (address << 8) | value;
                }

                int dataLength = count - addressBytes - 1;
                if (dataLength != RECORD_DATA_LENGTH) {
                    result.fail("Unexpected data length at line " + lineNumber + ": " + dataLength);
                    break;
                }

                if (address != expectedAddress) {
                    result.fail(String.format(Locale.ROOT,
                        "Non-contiguous address at line %d: expected 0x%08X, found 0x%08X",
                        lineNumber, expectedAddress, address));
                    break;
                }

                for (int i = 0; i < dataLength; i++) {
                    int value = parseHexByte(line, cursor);
                    cursor += 2;
                    sum += value;
                }

                int checksum = parseHexByte(line, cursor);
                sum += checksum;
                if ((sum & 0xff) != 0xff) {
                    result.fail("Checksum failure at line " + lineNumber);
                    break;
                }

                if ((address <= 0xffff && type != '1') ||
                    (address > 0xffff && type != '2')) {
                    result.fail("Wrong record type for address at line " + lineNumber);
                    break;
                }

                result.totalRecords++;
                result.dataBytes += dataLength;
                expectedAddress += dataLength;
            }
        }
        finally {
            reader.close();
        }

        if (result.valid && result.dataBytes != IMAGE_SIZE) {
            result.fail("S19 data size is " + result.dataBytes + ", expected " + IMAGE_SIZE);
        }
        if (result.valid && result.totalRecords != IMAGE_SIZE / RECORD_DATA_LENGTH) {
            result.fail("S19 record count is " + result.totalRecords + ", expected " +
                (IMAGE_SIZE / RECORD_DATA_LENGTH));
        }
        if (result.valid && result.s1Records != 0x10000 / RECORD_DATA_LENGTH) {
            result.fail("Unexpected S1 record count: " + result.s1Records);
        }
        if (result.valid && result.s2Records != (IMAGE_SIZE - 0x10000) / RECORD_DATA_LENGTH) {
            result.fail("Unexpected S2 record count: " + result.s2Records);
        }

        return result;
    }

    private int parseHexByte(String value, int offset) {
        return Integer.parseInt(value.substring(offset, offset + 2), 16);
    }

    private String sha256(File file) throws Exception {
        MessageDigest digest = MessageDigest.getInstance("SHA-256");
        InputStream input = new BufferedInputStream(new FileInputStream(file));
        try {
            byte[] buffer = new byte[65536];
            int read;
            while ((read = input.read(buffer)) >= 0) {
                if (read > 0) {
                    digest.update(buffer, 0, read);
                }
            }
        }
        finally {
            input.close();
        }
        return toHexCompact(digest.digest());
    }

    private void writeReport(File reportFile, File binFile, File s19File,
            S19Validation validation, String binSha256, String s19Sha256,
            byte[] callSite, byte[] updaterEntry, byte[] runtimeForce,
            byte[] descriptorFlags, byte[][] fallbackBranches,
            byte[] compensationBytes,
            byte[] appHeader,
            int autopilotValue, long storedAppCrc, long calculatedAppCrc,
            long appSize, long appSizeInverse) throws Exception {

        BufferedWriter writer = new BufferedWriter(new OutputStreamWriter(
            new FileOutputStream(reportFile), StandardCharsets.UTF_8));
        try {
            writer.write("TESLA MCU1 FULL CFLASH EXPORT REPORT\r\n");
            writer.write("===================================\r\n\r\n");
            writer.write("Program: " + currentProgram.getName() + "\r\n");
            writer.write(String.format(Locale.ROOT,
                "Export range: 0x%08X-0x%08X\r\n", START, END));
            writer.write("Image size: " + IMAGE_SIZE + " bytes (2 MiB)\r\n");
            writer.write("Missing/unreadable bytes filled with FF: " + missingByteCount + "\r\n\r\n");

            writer.write("Required patch checks\r\n");
            writer.write("---------------------\r\n");
            writer.write(String.format(Locale.ROOT,
                "0x%08X original updater call: %s [PASS]\r\n",
                CALL_SITE_ADDRESS, toHex(callSite)));
            writer.write(String.format(Locale.ROOT,
                "0x%08X stock updater entry: %s [PASS]\r\n",
                UPDATER_ENTRY_ADDRESS, toHex(updaterEntry)));
            writer.write(String.format(Locale.ROOT,
                "0x%08X runtime autopilot=2 instruction: %s [PASS]\r\n",
                RUNTIME_VALUE_LOAD_ADDRESS, toHex(runtimeForce)));
            writer.write(String.format(Locale.ROOT,
                "0x%08X autopilot watched-change flags: %s [PASS]\r\n",
                AUTOPILOT_DESCRIPTOR_FLAGS_ADDRESS,
                toHex(descriptorFlags)));
            writer.write(
                "Exactly 14 descriptor watched flags restored; AP clear [PASS]\r\n");

            for (int branchIndex = 0;
                 branchIndex < fallbackBranches.length;
                 branchIndex++) {

                writer.write(String.format(Locale.ROOT,
                    "0x%08X fallback branch to clean return: %s [PASS]\r\n",
                    FALLBACK_BRANCH_ADDRESSES[branchIndex],
                    toHex(fallbackBranches[branchIndex])));
            }
            writer.write(String.format(Locale.ROOT,
                "0x%08X CRC compensation bytes: %s [PASS]\r\n",
                COMPENSATION_ADDRESS, toHex(compensationBytes)));
            writer.write(String.format(Locale.ROOT,
                "0x%08X autopilot value: %02X ('%c') [PASS]\r\n",
                AUTOPILOT_VALUE_ADDRESS, autopilotValue, (char) autopilotValue));
            writer.write(String.format(Locale.ROOT,
                "0x%08X application header bytes: %s [PASS]\r\n",
                APP_HEADER_ADDRESS, toHex(appHeader)));
            writer.write(String.format(Locale.ROOT,
                "Application size: 0x%08X [PASS]\r\n", appSize));
            writer.write(String.format(Locale.ROOT,
                "Application size complement: 0x%08X [PASS]\r\n",
                appSizeInverse));
            writer.write(String.format(Locale.ROOT,
                "Stored application CRC32: 0x%08X [PASS]\r\n",
                storedAppCrc));
            writer.write(String.format(Locale.ROOT,
                "Calculated application CRC32: 0x%08X [PASS]\r\n",
                calculatedAppCrc));
            writer.write(String.format(Locale.ROOT,
                "Stored and calculated application CRC32 equal stock value 0x%08X [PASS]\r\n\r\n",
                REQUIRED_STOCK_APP_CRC));

            writer.write("Output files\r\n");
            writer.write("------------\r\n");
            writer.write("BIN: " + binFile.getAbsolutePath() + "\r\n");
            writer.write("BIN size: " + binFile.length() + "\r\n");
            writer.write("BIN SHA-256: " + binSha256 + "\r\n\r\n");
            writer.write("S19: " + s19File.getAbsolutePath() + "\r\n");
            writer.write("S19 size: " + s19File.length() + "\r\n");
            writer.write("S19 SHA-256: " + s19Sha256 + "\r\n\r\n");

            writer.write("Motorola S-record validation\r\n");
            writer.write("----------------------------\r\n");
            writer.write("Validation: " + (validation.valid ? "PASS" : "FAIL") + "\r\n");
            writer.write("Total records: " + validation.totalRecords + "\r\n");
            writer.write("S1 records: " + validation.s1Records + "\r\n");
            writer.write("S2 records: " + validation.s2Records + "\r\n");
            writer.write("Data bytes: " + validation.dataBytes + "\r\n");
            writer.write("Data bytes per record: " + RECORD_DATA_LENGTH + "\r\n");
            writer.write("Line endings: CRLF\r\n");
            writer.write("Header/termination records: none, matching the supplied PEmicro backups\r\n");
            if (!validation.valid) {
                writer.write("Failure: " + validation.failureReason + "\r\n");
            }

            writer.write("\r\nFLASHING CAUTION\r\n");
            writer.write("-----------------\r\n");
            writer.write("The S-record checksum validation only proves record integrity and address coverage.\r\n");
            writer.write("The gateway application CRC was recalculated and validated before export.\r\n");
            writer.write("Keep the verified original full backup available for recovery and use bench power.\r\n");
        }
        finally {
            writer.close();
        }
    }

    private boolean equalsBytes(byte[] left, byte[] right) {
        if (left == null || right == null || left.length != right.length) {
            return false;
        }
        for (int i = 0; i < left.length; i++) {
            if (left[i] != right[i]) {
                return false;
            }
        }
        return true;
    }

    private String toHex(byte[] bytes) {
        StringBuilder builder = new StringBuilder(bytes.length * 3);
        for (int i = 0; i < bytes.length; i++) {
            if (i != 0) {
                builder.append(' ');
            }
            appendHexByte(builder, bytes[i] & 0xff);
        }
        return builder.toString();
    }

    private String toHexCompact(byte[] bytes) {
        StringBuilder builder = new StringBuilder(bytes.length * 2);
        for (int i = 0; i < bytes.length; i++) {
            appendHexByte(builder, bytes[i] & 0xff);
        }
        return builder.toString().toLowerCase(Locale.ROOT);
    }

    private static class S19Validation {
        boolean valid;
        int totalRecords;
        int s1Records;
        int s2Records;
        int dataBytes;
        String failureReason = "";

        void fail(String reason) {
            valid = false;
            failureReason = reason;
        }
    }
}
