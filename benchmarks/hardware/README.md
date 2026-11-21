# Measurements on a Cortex-M0 board

The cycle bounds of `benchmarks/cycles` (computed from the source loop bounds, or certified
by `crosscheck-check`) hold for the timing table of `m0.py` and `Thumb.decode`, which was
written from Arm's Cortex-M0 documentation and has so far been checked only against our own
emulator. `hw.py` checks it against a processor: each kernel object `KERNEL.m0TAG.o`, the one
whose bounds were computed, is linked unchanged with `stm32f0/startup.c`, flashed on an
STM32F0 board, and its `main` is timed with the 32-bit timer TIM2 at the core clock.

**Status: not yet run on a board.** The build has been run (2026-11-20, Clang objects, F091RC:
26 of the 29 kernels link, the emulator's predictions are recorded; 12 of them call no library
code and can be compared exactly, 5 of these with a certified bound for `main`: `binarysearch`,
`bsort`, `countnegative`, `jfdctint`, `matrix1`; `isqrt` has a certified bound too, but calls
soft-float routines), the measurement has not: the register addresses and the clock set-up
come from the STM32F0 reference manual (RM0091) and are untried. The emulator's counts with
the 32-cycle multiplier equal those of `run_cycles.py` on the same objects (checked on five
kernels).

## What is needed

- a board with an STM32F0 (a Cortex-M0 core; with the single-cycle multiplier, as far as we
  know: to be confirmed in ST's PM0215, and by the measurement itself, since `build` records
  the emulator's counts with both multipliers, `emulated` and `emulated_mul32`): NUCLEO-F091RC
  (256 KB flash, 32 KB RAM: every kernel that fits, see below) or NUCLEO-F072RB (16 KB RAM);
- `st-flash` (stlink tools) or OpenOCD, and the ST-Link's virtual serial port (`/dev/ttyACM0`);
- the Docker image `armgcc:local` (`docker build -t armgcc:local benchmarks/hardware`).

## Steps

```bash
# objects and bounds (Clang; or add --gcc armgcc:local --tag=.gcc for GCC)
python3 benchmarks/cycles/run_cycles.py --check --certify OUT --checker formalization/.lake/build/bin/crosscheck-check \
    --certify-loops --abi --frame --jobs 4 --json RUN.json --extra-arg=--gcc-install-dir=/usr/lib/gcc/x86_64-linux-gnu/13
python3 benchmarks/hardware/hw.py build --run RUN.json [--tag .gcc] [--board f091]
python3 benchmarks/hardware/hw.py measure --port /dev/ttyACM0     # board connected
python3 benchmarks/hardware/hw.py report
```

## What is compared

- **Soundness**: the cycles of `main` on the board must not exceed its bound (computed and
  certified; the bounds use a 32-cycle multiplier, an upper bound for the single-cycle one).
  `report` exits with status 1 otherwise.
- **The timing table**: for kernels that call no library code, the board's count should equal
  the emulator's with `MUL_CYCLES = 1` (recorded by `build`). A difference shows where the
  table, or the assumption of memory without wait states, is wrong. Kernels with soft-float or
  `mem*` calls run libgcc/newlib on the board, computed natively by the emulator: listed, not
  compared.
- The return value of `main` (the kernel's own self-check) on the board and in the emulator.

Measurement: `measure(f)` (assembly, in `startup.c`) reads `TIM2_CNT`, calls `f` by `BLX`,
reads it again; the same for an empty function (4 cycles in the emulator: `movs r0, #0; bx
lr`). The cycles of `main` are `raw − empty + 4`: the timer reads, the call and the
peripheral access cancel out. Clock: the reset state (HSI 8 MHz, flash latency 0, prefetch
on, no interrupt), so that there are no wait states, as the timing table assumes. At 8 MHz
the slowest kernels (`pm`, `md5`, about 15 million cycles) take about 2 s.

## Kernels that do not fit

With 32 KB of RAM (F091RC), the kernels whose data and stack exceed it (`pm`, `quicksort`,
`sha` with 33-52 KB) fail to link; `build` prints the linker's message. With 16 KB (F072RB),
also `fft` and `ludcmp`.
