# Cycle bounds on a Cortex-M0

`run_cycles.py` turns CrossCheck's source loop bounds into **cycle bounds of compiled
code** for a processor whose instruction timings do not depend on the execution history:
the Arm Cortex-M0 (in order, no cache, no branch prediction), with zero-wait-state
memory. It is step S5 of `docs/proposals.md`.

```bash
python3 benchmarks/cycles/run_cycles.py --extra-arg=--gcc-install-dir=/usr/lib/gcc/x86_64-linux-gnu/13 \
    [--only bsort] [--json out.json] [--check] [--mul-cycles 32]
```

For each TACLeBench kernel (the single-file unit of `benchmarks/tacle/run_tacle.py`):

1. **Source loop bounds**: CrossCheck analyses the kernel (no annotation) and gives each
   loop a bound in the calling contexts of `main` (else for every call).
2. **Compilation**: Clang 18, `--target=thumbv6m-none-eabi -mcpu=cortex-m0 -O1 -g
   -fno-unroll-loops -ffreestanding -fno-builtin`, one object file.
3. **Static bound** (`wcet.py`): for each function, the control-flow graph of the code
   reachable from its entry (`m0.decode`, ARMv6-M Thumb); it must be reducible, without
   indirect jumps. Each natural loop is matched with the source loops through the debug
   line table (the source loop whose line occurs among the loop's own instructions; the
   largest bound if several do; no bound if none does), and its back edges are bounded by
   that source bound. The bound is the timing schema on the binary: a loop costs
   `N × (longest iteration) + (longest exit path)`, inner loops first, a call the callee's
   bound, a conditional branch the taken case (3 cycles).
4. **Check by execution** (`m0.Machine`, an interpreter of the instruction set written for
   this purpose): the kernel's `main` must return 0 (TACLeBench programs check their own
   result, which also checks the interpreter); every call of a function with a bound must
   take at most that many cycles, and every binary loop's back edges per entry at most its
   matched bound. `--check` fails otherwise. Run-time helpers without code (`__aeabi_*`
   division and floating point, `memset`, `memcpy`) are executed natively at no cost; a
   function that calls one has no static bound, so it is never compared.

Timings (`m0.cycles`): 1 cycle for data processing, 2 for loads and stores, `1+N` for
`LDM`/`STM`/`PUSH`/`POP`, `4+N` for `POP` with the PC (N counts the PC, as in the manual), 3 for `B` and a taken conditional branch, 1 for one not taken, 4 for `BL`,
3 for `BX`, `MULS` 32 (small multiplier; `--mul-cycles 1` for the fast one).

**What is trusted**: the timing table (the instruction summary of the Arm Cortex-M0
Technical Reference Manual, revision r0p0, Arm DDI 0432C, Table 3-1: `test_m0.py` holds
the table, 87 rows, and compares `m0.cycles` with it; `SVC`, `BKPT`, `WFE`, `WFI`, `CPS`
and the 32-bit system instructions stop the decoder, so a function that contains one gets
no bound; not checked here against hardware); that a binary loop
iterates at most as often as the source loop it is matched with (checked on the runs,
not proved); zero-wait-state memory, no interrupts (see `CROSSCHECK_INTERRUPT` for those).
The interpreter counts cycles with the same table, so the check validates the path
analysis and the loop matching, not the table.

`python3 benchmarks/cycles/test_m0.py` runs the interpreter's self-test (`selftest.c` and
`runtime.c` at `-O0` and `-O1`, results compared with the C semantics). Integer division
(`/`, `%`) is compiled from `runtime.c` (restoring division, 32 iterations) with each kernel,
so that its loop is bounded by CrossCheck and its cycles are counted; floating point
(software on the M0) has no code here and blocks the functions that use it.

## Results (2026-11-16)

29 kernels compiled; 28 return 0 when run (`fft` returns 1: it converts negative floats to
`unsigned long`, undefined behaviour in C, which Arm's conversion saturates and x86's wraps;
it is listed in `EXPECTED_FAILURE`). 156 s in total.

- **107 of the 267 kernel functions** receive a cycle bound (`runtime.c` not counted).
- **6 entry functions** (`main`) are bounded:

| Kernel | Bound (cycles) | Observed | Bound / observed |
|---|---:|---:|---:|
| binarysearch | 32,686 | 24,241 | 1.35 |
| bsort | 369,779 | 148,668 | 2.49 |
| countnegative | 449,615 | 327,923 | 1.37 |
| isqrt | 1,005,075 | 689,071 | 1.46 |
| jfdctint | 75,652 | 60,911 | 1.24 |
| matrix1 | 63,722 | 48,548 | 1.31 |

- **Checks**: 11 calls of bounded functions (the others are inlined at `-O1`) and 45 binary
  loops were compared with the run: **no violation**; over 10 of the calls, bound/observed is
  between 1.02 and 2.49. The eleventh, a function of `fft` bounded since logarithmic potentials
  (2026-11-15), has a bound 970 times its observed cycles: its three nested loops are
  bounded by the product of their bounds, while at each outer iteration the count of one
  inner loop doubles and that of the other halves. `bsort`'s factor comes from its triangular nested loops, bounded
  as a rectangle (no amortisation).
- **Not bounded**, by cause: software floating point (`__aeabi_f*`, `__aeabi_d*`: most of the
  numeric kernels), source loops without a bound (data-dependent: `insertsort`,
  `binarysearch`, `quicksort`), and their callers.

Matching rule: the first version, which took the largest bound among all lines of a
loop's instructions, gave `matrix1_main` 100 iterations instead of 10 (an instruction of
the loop's preheader inherits the line of another loop) and a bound 105 times the observed
cycles; trying the lines of the back-edge branches first gives 1.31.

## OTAWA on the same binaries (2026-11-16)

`run_otawa.py` gives CrossCheck's loop bounds to [OTAWA](https://github.com/statinf-otawa/otawa-project)
(Ballabriga, Cassé, Rochange, Sainrat, SEUS 2010; version 2.3.0 here), which is not part
of this repository: build its image yourself (`docker build . --target otawa-dev -t
otawa:dev` in its project). The script runs it without network.

```bash
python3 benchmarks/cycles/run_otawa.py --lld PATH/TO/ld.lld --check \
    --extra-arg=--gcc-install-dir=/usr/lib/gcc/x86_64-linux-gnu/13   # on the author's machine
#   --lld: any LLVM linker for Arm; a Rust toolchain has one (`rust-lld`)
```

Each kernel is linked into an executable (no library: the soft-float functions stay
undefined, and the functions that call them have no bound, as above). For every function
with a bound of the timing schema, the bounds of its loops are written as FFX flow facts
on the headers of the binary loops, by label and offset (`<loop label="f" offset="0x16"
maxcount="N+1"/>`: a source bound `N` counts executions of the body, OTAWA's `maxcount`
executions of the header per entry of the loop), and `owcet -s trivial -p stages=1`
computes a bound by IPET, in executed instructions (no Cortex-M0 description was written
for OTAWA, so this is not a cycle bound). The program is then run by `m0.py`.

| | |
|---|---:|
| functions given to OTAWA (those with a cycle bound above) | 107 |
| ... for which OTAWA computes a bound | 107 (6 entry functions `main`) |
| flow facts | 199 |
| calls completed by the runs and compared | 11, **no bound below the executed instructions** |
| bound / executed, geometric mean (largest) | 2.36 (756: `fft_bit_reduct`, product of nested bounds) |
| OTAWA's bound at most the timing schema's (same unit) | 52 functions; above for 55 |

OTAWA's bound is above the schema's where a loop header gets one more execution than the
body and the schema counts only the exit path for it. **Why label and offset**: the FFX
that the plugin exports designates a loop by source file and line; on these `-O1`
binaries OTAWA could not place such facts (inlined callees, rotated loops: "no limit for
the loop at ..."), so the matching of binary loops to source loops is done by `wcet.py`,
as for the cycle bounds. That matching is checked on runs, not proved.

## Stack bounds (2026-11-16)

`stack.py` bounds the stack of every function of the same binaries: the largest depth of
the stack pointer below its value at entry, callees included. The depth is computed on the
control-flow graph (`push`, `pop`, `sub sp`, `add sp`); it must have one value at every
instruction and be 0 at every return. The rule over calls is a maximum, not a sum:
`stack(f) = max(own depth, depth at a call + stack(callee))` (Lean:
`Stack.highWater_le_of_bound`, Paper I `prop:stack`). No loop bound is needed, so more
functions get a stack bound than a cycle bound. `run_cycles.py` computes them and checks
each against the run: for every activation, the stack pointer at entry minus the lowest
value seen until it returns (`--check` fails on a violation).

| | |
|---|---:|
| functions with a stack bound | **143 of 267** |
| entry functions (`main`) with a stack bound | 10 of 29 |
| calls compared with the run | 24, **no violation** |
| of which the bound equals the observed stack | 19 |

| Kernel | Stack bound of `main` (bytes) | Observed |
|---|---:|---:|
| binarysearch | 56 | 56 |
| bsort | 28 | 28 |
| countnegative | 64 | 64 |
| fac | 24 | 24 |
| insertsort | 32 | 32 |
| isqrt | 52 | 52 |
| jfdctint | 104 | 104 |
| matrix1 | 36 | 36 |
| md5 | 584 | 552 |
| prime | 56 | 56 |

(`fac` is recursive in the source; at `-O1` the compiler turns its recursion into a loop.)

No bound, by cause (124 functions): a call to a software floating-point helper, which the
interpreter provides in Python, without code (84); a call to such a function (32); the
stack pointer written from a register whose value is not a constant loaded just before
(4; `ldr r, =-size; add sp, r`, the way large frames are reserved, is handled); recursion
in the binary (4: `bitonic`, `quicksort`, `recursion`). A recursive function could be bounded
from a recursion depth (`Stack.highWater_le_depth`); this is not implemented.

What the bound covers: the stack of the program's own code. Not counted: exception frames
(8 words per interrupt taken on this processor), and anything a real run-time library
would add. The decoder and the control-flow graph are those of the cycle analysis, and
the check is against the same interpreter: it tests the path analysis, not the decoder.
