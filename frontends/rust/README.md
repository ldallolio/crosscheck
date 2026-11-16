# Rust front-end

`mir2c.py` translates the MIR of a Rust file into C; the C is analysed by
`crosscheck-tool` like any C code (bounds, certificates checked by the Lean checker, and,
where the C is in the mini-C fragment, validation against it). The C translation is
not verified: for Rust code, it is part of what is trusted, as the C++ front-end is for C.

```bash
python3 frontends/rust/crosscheck_rust.py frontends/rust/examples/kernels.rs --out /tmp/k \
    --checker formalization/.lake/build/bin/crosscheck-check -- --gcc-install-dir=/usr/lib/gcc/x86_64-linux-gnu/13
python3 frontends/rust/tests/test_rust.py --checker formalization/.lake/build/bin/crosscheck-check
```

**MIR as text.** The front-end reads what `rustc --emit=mir -O -C overflow-checks=on -C
panic=abort` prints. That output is for humans and changes between Rust releases; this
version is written for **rustc 1.100.0** (CI pins it). When the format changes, the
translator reports untranslated functions or the differential test fails, and `mir2c.py`
must be adjusted. A stable interface would be a `rustc_private` driver on a nightly
toolchain (`stable_mir`), which is not used here.

**Fragment.** Free functions (no generics, closures, traits, methods) over integers,
`bool`, slices of integers (`&[T]`, `&mut [T]`, passed as pointer and length), `Option` of
an integer (`for i in a..b` loops, which `-O` inlines to integer MIR), and calls between
such functions. Loops are rebuilt as `while (test)`, where the test is the conjunction of
the tests at the loop's head (through overflow checks); conditionals use the immediate
post-dominator. Not translated (reason printed): slice iterators (`for &v in x.iter()`:
pointer arithmetic), loops without a test at their head (`loop` with `break`), several
exits, references to scalars, structs, floating point.

**Semantics** (what the bound means for the Rust function):
- MIR's `Add`, `Sub`, `Mul` wrap (`wrapping_add`, …): computed in C on an unsigned type of
  at least 32 bits;
- checked arithmetic (`+` with `overflow-checks=on`) panics on overflow: plain C
  arithmetic, which the analysis assumes not to overflow, so **the bound covers the
  executions that do not panic**;
- every other `assert` (bounds checks, division by zero, `assert!`) and every call that
  does not return (`panic!`) becomes `if (!(c)) return 0;`: the C program then has more
  behaviours (it goes on where Rust stops), so bounds of the C bound the Rust function,
  and the asserted fact holds after it. A user `assert!(n <= 1000)` is thus a way to give
  an input range **that is checked at run time, not trusted**;
- `usize`/`isize` are 64 bits (the host's); costs are those of the cost model on the C
  translation, an abstract unit like the C front-end's.

**Tests** (`tests/test_rust.py`): a differential test, every translated function of
`examples/kernels.rs` run on the same random inputs in Rust and in the generated C
(compiled by the host compiler), results and `&mut` slices compared whenever Rust does not
panic; the `rejected_*` functions (Euclid's gcd, Collatz, a wrapping loop that never
exits, a loop that ends only by overflow) must have no bound.

Results (2026-11-15, rustc 1.100.0): 11 of the 12 functions translated (`count_above`
uses a slice iterator); 382 differential runs, no mismatch (38 Rust panics skipped);
bounded: `fir`, `sat_sum`, `bubble`, `steps_down`, `table`, `twice` (with `assert!`
ranges, no annotation); `isqrt` not bounded (its test `(r+1)² ≤ x` is quadratic); the 4
`rejected_*` not bounded; certificates for `steps_down`, `table`, `twice`, all accepted,
all three also validated against mini-C since 2026-11-16 (`steps_down` only, before calls and unsigned stores were in mini-C) (`fir`, `sat_sum`, `bubble` have `usize`
counters, for which the certificate generator does not find the invariants).
