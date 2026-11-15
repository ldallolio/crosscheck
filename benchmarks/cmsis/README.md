# CMSIS-DSP: an open-source embedded library

`run_cmsis.py` runs `crosscheck-tool` on the C sources of
[CMSIS-DSP](https://github.com/ARM-software/CMSIS-DSP) (Arm, Apache-2.0), the
signal-processing library of the Cortex-M ecosystem: filters, transforms, matrix,
statistics and fast-math kernels, written in a MISRA-like style for real-time use.
CMSIS-DSP (revision `5a28089`) and the CMSIS 6 Core headers (`69b5aa3`) are fetched into
`.cache/` (gitignored; nothing is vendored).

```bash
python3 benchmarks/cmsis/run_cmsis.py [--json out.json] [--only Group/file.c] [--range 1024]
```

Every source file (632, without the per-group unity files and the `_*.c` templates) is
analysed for a **Cortex-M4** target (`--target=thumbv7em-none-eabi -mcpu=cortex-m4`,
freestanding; `.cache/stubs/` declares the few `string.h` and `math.h` functions the
headers need), every function (`--all`), in two modes:

1. **as is**: the file alone, no annotation;
2. **with input ranges and context**: the other files of the same group and the common
   tables are included after the file as definitions (calls into them have bodies; only
   the file's functions are analysed as roots); `memset`, `memcpy`, `memmove` get
   *illustrative* contracts (4 + 1 unit per byte, `.cache/contracts.json`); and
   `input-range=1,1024`: every integer input without a declared range, parameters and
   the fields read through pointer parameters (`S->numTaps`), is assumed in [1, 1024]
   (unsigned) or [-1024, 1024] (signed). Sizes of at least 1 are what the code assumes
   when it computes `blockSize - 1U`. These are assumptions of the run, listed in every
   report, not statements about the library.

## Results (2026-11-15)

786 functions, 1235 loops:

| Mode | Functions bounded | Loops with a derived bound |
|---|---:|---:|
| as is | 161 | 356 |
| with input ranges and context | **616** (78%) | 1024 |
| *before this step (2026-11-14), with ranges on parameters only* | *357* | *758* |

What the step changed, by the blockers measured on the first run:

| Blocker (first run, with ranges) | Change | Kind |
|---|---|---|
| Arm intrinsics (`__qadd16`, `__SMLAD`, …: `__builtin_arm_*`), 223 files | one arithmetic unit each (assumption) | cost model |
| GNU statement expressions and one-instruction inline assembly in the CMSIS Core intrinsics | evaluated (straight-line only); one unit per instruction (assumption) | cost model |
| `blockSize - 1U` with `blockSize` possibly 0 (wrap-around) | inputs assumed ≥ 1 by the run (`input-range=1,N`) | harness |
| sizes in instance structures (`S->numTaps`, `S->fftLen`) | fields read through pointer parameters are symbols (assumption: not modified while the function runs) | analysis |
| `do { … } while (--j)` | integer tests in C as `!= 0`; the guard's side effect gives `j >= 1` as invariant | analysis |
| calls into other files of the library | group context | harness |
| `memset` / `memcpy` | library contracts (illustrative) | contracts |

Remaining, with ranges and context (functions not bounded, by error):

- **loops (291 errors)**: mostly the transforms' loops that halve or quarter a counter
  (`n2 >>= 2`: logarithmic, beyond linear potentials) and loops whose bound is a
  value read from memory;
- **calls into other groups (162)**: callees in another group, not included in the
  context (e.g. a transform calling a support function);
- **contract arguments without an upper bound (13)**: `memset`/`memcpy` lengths computed
  from values the analysis does not bound;
- **recursion (3)** and `tanhf` without a contract (2).

No certificates are emitted in this run, and the bounds are cost bounds in abstract units
with unit weights, not times; see Paper II, "Limitations".
