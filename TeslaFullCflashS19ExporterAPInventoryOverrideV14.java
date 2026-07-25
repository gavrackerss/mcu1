// Ghidra compatibility shim for
// TeslaFullCflashS19ExporterAPInventoryOverrideV13.
//
// This V1.4 exporter keeps the complete V1.3 validation and BIN/S19 export
// implementation, but replaces the six VLE SCALE-immediate instructions that
// Ghidra 12.1.2 rejects with CR-neutral e_rlwimi equivalents matching the V1.4
// apply script.
//
// REQUIREMENT: keep
// TeslaFullCflashS19ExporterAPInventoryOverrideV13.java in the same Ghidra
// script directory. Run this V14 script, not V13.
//
// Note: because the underlying exporter implementation is inherited, its file
// names and popup text still contain V13. The bytes validated and exported are
// the V1.4 wrapper form.
//
// @category Tesla.Export
// @menupath Tools.Tesla.Export AP Inventory Override V1.4 BIN and S19

import java.lang.reflect.Field;

public class TeslaFullCflashS19ExporterAPInventoryOverrideV14
        extends TeslaFullCflashS19ExporterAPInventoryOverrideV13 {

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
            "TeslaFullCflashS19ExporterAPInventoryOverrideV14: installed " +
            "the CR-neutral e_rlwimi validation substitutions.");
        println(
            "Inherited V1.3 output filenames and popup labels are expected; " +
            "the validated/exported wrapper is the V1.4 form.");

        super.run();
    }

    private void patchParentWrapperAssembly() throws Exception {
        Field field = TeslaFullCflashS19ExporterAPInventoryOverrideV13.class
            .getDeclaredField("WRAPPER_ASM");
        field.setAccessible(true);

        String[] wrapper = (String[])field.get(null);
        if (wrapper == null || wrapper.length == 0) {
            throw new IllegalStateException(
                "V1.3 exporter WRAPPER_ASM is unavailable or empty.");
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

        // Idempotent if the script is run again in the same Ghidra session.
        if (oldCount == 0 && newCount == 1) {
            return;
        }

        throw new IllegalStateException(
            "Cannot safely substitute V1.3 exporter wrapper line.\n" +
            "Old: " + oldLine + " (count=" + oldCount + ")\n" +
            "New: " + newLine + " (count=" + newCount + ")");
    }
}
