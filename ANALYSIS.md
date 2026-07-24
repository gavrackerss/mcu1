# Tesla MCU1 autopilot runtime/configuration check analysis

## Correct loader setup

- Firmware input: `Tesla_MCU1_ConfigCheckBypass.S19`.
- The repository `ghidra_12.1.2_PUBLIC_20260605.zip` is only a Git LFS pointer in this checkout, so I fetched the matching public Ghidra release into `/tmp` for headless work.
- The S-record payload maps as one contiguous 2 MiB image: `0x00000000..0x001fffff`.
- The runtime code is PowerPC VLE/e200-style code. Importing as normal PowerPC gives false bad-instruction results. In Ghidra headless, set the `vle` context register to `1` across the image before analysis.

## Why `internal.dat = 0` is not enough

The `internal.dat` text block is not the only source of truth once the firmware is running. The text values are parsed into packed runtime configuration words in RAM, and later code reads those packed words directly. If another runtime patch forces AP2 by writing the RAM words, the update-time check can still see AP-enabled state even when the embedded text is changed back to zero.

The embedded flash text values are still useful for locating the parser, but the live checks are against RAM fields:

| Flash address | Text/value |
| --- | --- |
| `0x0001ccb2` | `autopilotcameratype 1` |
| `0x0001cdb3` | `autopilot 2` |

## Key strings and dispatch table

The compiled key names are in the configuration metadata region:

| Address | Key string |
| --- | --- |
| `0x00024164` | `autopilot` |
| `0x0002452c` | `autopilotCameraType` |

The following 16-byte rows map those keys to VLE handlers:

| Table row | Key pointer | Key | Handler pointer |
| --- | --- | --- | --- |
| `0x00024d50` | `0x00024164` | `autopilot` | `0x000870f0` |
| `0x000250b0` | `0x0002452c` | `autopilotCameraType` | `0x0008657c` |

## Decoded autopilot handlers

### `0x000870f0` — `autopilot`

This handler parses the value and then writes a forced AP2 value into several packed runtime words. The key instruction is `se_li r0,0x2` at `0x00087110`; the value `2` is then inserted into these RAM words:

| RAM word | Accesses in handler | Meaning from handler behavior |
| --- | --- | --- |
| `0x4004aa38` | read `0x0008711a`, write `0x00087134` | One packed copy of the autopilot mode. |
| `0x40047cac` | read `0x0008711e`, write `0x0008713c` | Second packed copy of the same forced AP2 value. |
| `0x40049da4` | read `0x00087124`, write `0x00087138` | Third packed copy of the same forced AP2 value. |

Pseudocode from the VLE decode:

```c
if (parse_config_value(param, tmp) == 0) {
    RAM[0x4004aa38] = (RAM[0x4004aa38] & 0xffffffe3) | 0x08;
    RAM[0x40047cac] = (RAM[0x40047cac] & 0xffffff1f) | 0x40;
    RAM[0x40049da4] = (RAM[0x40049da4] & 0xffffffc7) | 0x10;
}
```

### `0x0008657c` — `autopilotCameraType`

This handler parses the camera type and inserts the low two bits into two packed runtime words:

| RAM word | Accesses in handler | Meaning from handler behavior |
| --- | --- | --- |
| `0x40047f2c` | read `0x000865a2`, write `0x000865b2` | Packed camera-type field. |
| `0x40016844` | read `0x000865a8`, write `0x000865b4` | Mirrored/alternate packed camera-type field. |

Pseudocode from the VLE decode:

```c
if (parse_config_value(param, tmp) == 0) {
    RAM[0x40047f2c] = (RAM[0x40047f2c] & 0xfff3ffff) | ((tmp[0] & 3) << 18);
    RAM[0x40016844] = (RAM[0x40016844] & 0xf3ffffff) | ((tmp[0] & 3) << 26);
}
```

## Runtime readers/checks that do not use `internal.dat`

These are the important follow-up locations because they read the packed runtime words populated by the handlers above.

| Address | RAM field read | Check performed | Why it matters |
| --- | --- | --- | --- |
| `0x0006da12` | `0x4004aa38` | `e_andi. r7,r0,0xc0000000`; returns true/false from the masked live value. | This is a direct runtime accessor for a packed AP-related word. It is independent of the text block after parsing. |
| `0x00068f2a` | `0x40047cac` | Tests bit `0x16`; falls through to another live config check. | Runtime feature-gate helper using one AP mirror word. |
| `0x0006d5ec` | `0x40047cac` | Masks bits `0x5..0x6` and compares to a generated bit value before a timed gate. | Runtime feature/update eligibility helper. |
| `0x0006d734` | `0x40047cac` | Tests bit `0x0b`, then masks bits `0x5..0x6` and checks a 5-second timer gate. | Likely part of the configuration-refresh/update transition path. |
| `0x0006d6d2` | `0x40047f2c` | Masks `0x00030000` and compares it with `0x00004000`. | Direct runtime check of `autopilotCameraType` packed value. |
| `0x00080842` | `0x40047f2c` | Tests bit `0x0e` inside a large state machine. | Runtime state-machine gate influenced by camera type. |
| `0x0009defe` | `0x4004aa38` | Masks `0x00e00000` and compares against `0x00400000`/`0x00a00000`. | Another live packed-config reader; not the low AP2 field written by `0x870f0`, but it proves the same runtime word is used by later logic. |

## Most likely update-time cause

Given your observation that changing `internal.dat` to `0` does not stop the update-triggered “Vehicle configuration update” behavior, the check is probably **not** re-reading only the text at `0x0001cdb3`. The stronger candidates are:

1. `0x0006da12` reading `0x4004aa38`.
2. `0x0006d5ec` / `0x0006d734` reading `0x40047cac` with a 5-second timer gate.
3. `0x0006d6d2` reading `0x40047f2c` for camera type.
4. The large runtime state machine around `0x00080820`, which branches on `0x40047f2c` at `0x00080842` and then performs multiple timed/configuration writes.

Those locations are the actual runtime checklist to inspect or patch. The dispatch handlers at `0x870f0` and `0x8657c` explain where the AP2 values are packed; the update-time detection likely happens later when those RAM words are read by the helpers above.

## Suggested patch strategy

- If your existing patch forces AP2 by writing the RAM mirrors, also neutralize the reader(s) that feed the update-time checker rather than only editing `internal.dat`.
- Start with `0x0006da12`/`0x0006da16` for `0x4004aa38` and `0x0006d6d2`/`0x0006d6da` for `0x40047f2c`; they are small, isolated helpers.
- If those are not sufficient, inspect callers of `0x0006d5ec` and `0x0006d734`; both combine the packed AP mirror with a 5-second timer (`0x1388`), which matches an update/configuration refresh style gate.

## Reproduction commands

```bash
python3 - <<'PY'
from pathlib import Path
mem=bytearray(0x200000)
for line in Path('Tesla_MCU1_ConfigCheckBypass.S19').read_text().splitlines():
    if line and line[0]=='S' and line[1] in '123':
        t=line[1]
        cnt=int(line[2:4],16)
        alen={'1':2,'2':3,'3':4}[t]
        addr=int(line[4:4+alen*2],16)
        data=bytes.fromhex(line[4+alen*2:4+(cnt-1)*2])
        mem[addr:addr+len(data)]=data
Path('/tmp/firmware.bin').write_bytes(mem)
PY
```

```java
// Save as SetVleAnalyze.java and use as a Ghidra preScript.
import ghidra.app.script.GhidraScript;
import ghidra.program.model.lang.Register;
import java.math.BigInteger;
public class SetVleAnalyze extends GhidraScript {
    public void run() throws Exception {
        Register r = currentProgram.getProgramContext().getRegister("vle");
        currentProgram.getProgramContext().setValue(r, toAddr(0), toAddr(0x1fffff), BigInteger.ONE);
    }
}
```

```bash
/tmp/ghidra/ghidra_12.1.2_PUBLIC/support/analyzeHeadless /tmp/ghvle2 MCU \
  -import /tmp/firmware.bin \
  -loader BinaryLoader \
  -loader-baseAddr 0 \
  -processor PowerPC:BE:64:VLE-32addr \
  -cspec default \
  -overwrite \
  -scriptPath /tmp/ghscripts \
  -preScript SetVleAnalyze.java \
  -analysisTimeoutPerFile 300
```
