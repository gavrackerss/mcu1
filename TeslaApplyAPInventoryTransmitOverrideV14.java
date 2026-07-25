// Ghidra compatibility shim for TeslaApplyAPInventoryTransmitOverrideV13.
//
// This V1.4 wrapper keeps the full V1.3 preflight, transaction, CRC-neutral
// compensation and final verification logic, but replaces the six VLE
// SCALE-immediate instructions that Ghidra 12.1.2 cannot assemble reliably.
//
// The replacement uses e_rlwimi with the already-known r11 payload address:
//   - each clear operation rotates a known run of zero bits into the AP field;
//   - each restore operation rotates address bit 0 (known 1 for all three
//     payload-byte addresses) into the AP2 bit;
//   - e_rlwimi does not alter CR0.
//
// REQUIREMENT: keep TeslaApplyAPInventoryTransmitOverrideV13.java in the same
// Ghidra script directory. This class deliberately reuses its full validation
// and patch implementation.
//
// @category Tesla.Patch
// @menupath Tools.Tesla.Apply AP Inventory Transmit Override V1.4

import java.lang.reflect.Field;

public class TeslaApplyAPInventoryTransmitOverrideV14
        extends TeslaApplyAPInventoryTransmitOverrideV13 {

    private static final String[][] REPLACEMENTS = new String[][] {
        {
            "e_andi r12,r12,0xe3",
            "e_rlwimi r12,r11,14,27,29"
        },
        {
            "e_andi r12,r12,0x1f",
            "e_rlwimi r12,r11,17,24,26"
        },
        {
            "e_andi r12,r12,0xc7",
            "e_rlwimi r12,r11,15,26,28"
        },
        {
            "e_ori r12,r12,0x08",
            "e_rlwimi r12,r11,3,28,28"
        },
        {
            "e_ori r12,r12,0x40",
            "e_rlwimi r12,r11,6,25,25"
        },
        {
            "e_ori r12,r12,0x10",
            "e_rlwimi r12,r11,4,27,27"
        }
    };

    @Override
    protected void run() throws Exception {
        patchParentWrapperAssembly();

        println(
            "TeslaApplyAPInventoryTransmitOverrideV14: installed the " +
            "CR-neutral e_rlwimi assembly substitutions.");
        println(
            "The inherited V1.3 prompts/report labels are expected; the " +
            "assembled wrapper is the V1.4 form.");

        super.run();
    }

    private void patchParentWrapperAssembly() throws Exception {
        Field field = TeslaApplyAPInventoryTransmitOverrideV13.class
            .getDeclaredField("WRAPPER_ASM");
        field.setAccessible(true);

        String[] wrapper = (String[])field.get(null);
        if (wrapper == null || wrapper.length == 0) {
            throw new IllegalStateException(
                "V1.3 WRAPPER_ASM is unavailable or empty.");
        }

        for (String[] replacement : REPLACEMENTS) {
            replaceExactlyOnce(wrapper, replacement[0], replacement[1]);
        }
    }

    private void replaceExactlyOnce(
            String[] wrapper,
            String oldLine,
            String newLine) {

        int oldCount = 0;
        int newCount = 0;
        int oldIndex = -1;

        for (int index = 0; index < wrapper.length; index++) {
            if (oldLine.equals(wrapper[index])) {
                oldCount++;
                oldIndex = index;
            }
            if (newLine.equals(wrapper[index])) {
                newCount++;
            }
        }

        if (oldCount == 1 && newCount == 0) {
            wrapper[oldIndex] = newLine;
            return;
        }

        // Idempotent when this shim is run more than once in the same Ghidra
        // session and the parent class remains loaded.
        if (oldCount == 0 && newCount == 1) {
            return;
        }

        throw new IllegalStateException(
            "Cannot safely substitute V1.3 wrapper line.\n" +
            "Old: " + oldLine + " (count=" + oldCount + ")\n" +
            "New: " + newLine + " (count=" + newCount + ")");
    }
}
