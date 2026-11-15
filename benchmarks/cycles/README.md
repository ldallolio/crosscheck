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
`LDM`/`STM`/`PUSH`/`POP`, `4+N` for `POP` with the PC (counting the PC, which is
conservative), 3 for `B` and a taken conditional branch, 1 for one not taken, 4 for `BL`,
3 for `BX`, `MULS` 32 (small multiplier; `--mul-cycles 1` for the fast one).

**What is trusted**: the timing table (from the instruction summary of the Arm Cortex-M0
Technical Reference Manual, not checked here against hardware); that a binary loop
iterates at most as often as the source loop it is matched with (checked on the runs,
not proved); zero-wait-state memory, no interrupts (see `CROSSCHECK_INTERRUPT` for those).
The interpreter counts cycles with the same table, so the check validates the path
analysis and the loop matching, not the table.

`python3 benchmarks/cycles/test_m0.py` runs the interpreter's self-test (`selftest.c` and
`runtime.c` at `-O0` and `-O1`, results compared with the C semantics). Integer division
(`/`, `%`) is compiled from `runtime.c` (restoring division, 32 iterations) with each kernel,
so that its loop is bounded by CrossCheck and its cycles are counted; floating point
(software on the M0) has no code here and blocks the functions that use it.

## Results (2026-11-15)

29 kernels compiled; 28 return 0 when run (`fft` returns 1: it converts negative floats to
`unsigned long`, undefined behaviour in C, which Arm's conversion saturates and x86's wraps;
it is listed in `EXPECTED_FAILURE`). 156 s in total.

- **104 of the 267 kernel functions** receive a cycle bound (`runtime.c` not counted).
- **5 entry functions** (`main`) are bounded:

| Kernel | Bound (cycles) | Observed | Bound / observed |
|---|---:|---:|---:|
| bsort | 369,779 | 148,668 | 2.49 |
| countnegative | 449,615 | 327,923 | 1.37 |
| isqrt | 1,005,075 | 689,071 | 1.46 |
| jfdctint | 75,652 | 60,911 | 1.24 |
| matrix1 | 63,722 | 48,548 | 1.31 |

- **Checks**: 10 calls of bounded functions (the others are inlined at `-O1`) and 43 binary
  loops were compared with the run: **no violation**; over 9 of the calls, bound/observed is
  between 1.02 and 2.49. The tenth, a function of `fft` bounded since logarithmic potentials
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
