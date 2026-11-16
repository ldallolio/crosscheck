#!/usr/bin/env python3
# Copyright (c) 2026 Luca Dall'Olio. Released under the MIT license.
"""Test of the loop instrumentation of measure_loops.py on a program whose counts are
known by construction.

    test_measure_loops.py [--clang CLANG] [--opt OPT] [--cc CC] [--extra-arg ARG]...

Each loop of the program below is followed, on its line, by `// expect N`: the largest
number of executions of its body in one entry of the loop, or `// expect none` for a loop
that is never entered. The cases are those where a wrong instrumentation would show: `do`
loops, loops left by `break`, `continue`, a loop entered several times, nested loops (the
inner count is per entry, not the total), a loop in a recursive function, a loop whose
body never runs, and the form `while (n-- > 0)` (kernel `filterbank`).
"""
import argparse
import pathlib
import re
import shutil
import sys
import tempfile

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import measure_loops  # noqa: E402

PROGRAM = r"""
volatile int sink;
static void twice(int n) {
  for (int i = 0; i < n; i++) // expect 6
    sink += i;
}
static void rec(int n) {
  if (n <= 0) return;
  for (int i = 0; i < n; i++) // expect 4
    sink += i;
  rec(n - 1);
}
static void never(int n) {
  if (n > 100) {
    while (n > 0) // expect none
      n--;
  }
}
int main(void) {
  int i, j, k, n;
  for (i = 0; i < 7; i++) // expect 7
    sink += i;
  n = 2;
  while (n-- > 0) // expect 2
    sink += n;
  i = 0;
  do { // expect 5
    sink += i;
  } while (++i < 5);
  k = 0;
  while (1) { // expect 4
    if (k == 3) break;
    k++;
  }
  for (i = 0; i < 9; i++) { // expect 9
    if (i % 2) continue;
    sink += i;
  }
  for (i = 0; i < 3; i++) // expect 3
    for (j = 0; j < i + 2; j++) // expect 4
      sink += j;
  twice(3);
  twice(6);
  twice(1);
  rec(4);
  never(5);
  for (i = 0; i < 0; i++) // expect 0
    sink += i;
  i = 10;
  do { // expect 1
    sink += i;
  } while (i < 5);
  j = 0;
  do { // expect 3
    j++;
    if (j == 3) break;
    sink += j;
  } while (1);
  return 0;
}
"""


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--clang", default=shutil.which("clang") or "/usr/lib/llvm-18/bin/clang")
    ap.add_argument("--opt", default=shutil.which("opt") or "/usr/lib/llvm-18/bin/opt")
    ap.add_argument("--cc", default="cc")
    ap.add_argument("--extra-arg", action="append", default=[])
    a = ap.parse_args()
    expect = {}
    for n, text in enumerate(PROGRAM.splitlines(), 1):
        m = re.search(r"// expect (\w+)", text)
        if m:
            expect[n] = None if m.group(1) == "none" else int(m.group(1))
    with tempfile.TemporaryDirectory() as tmp:
        work = pathlib.Path(tmp)
        unit = work / "known.c"
        unit.write_text(PROGRAM)
        counts, not_reached, skipped = measure_loops.observed_counts(
            unit, work, a.clang, a.opt, a.extra_arg, work, a.cc)
    bad = []
    if skipped:
        bad.append(f"{skipped} loop(s) not instrumented")
    for line, want in sorted(expect.items()):
        got = counts.get(line)
        if want is None:
            if line not in not_reached or got is not None:
                bad.append(f"line {line}: expected not reached, got {got}")
        elif got != want:
            bad.append(f"line {line}: expected {want}, got {got}"
                       + (" (not reached)" if line in not_reached else ""))
    extra = sorted(set(counts) - set(expect))
    if extra:
        bad.append(f"counts on lines without an expectation: {extra}")
    for b in bad:
        print(b, file=sys.stderr)
    print(f"{len(expect)} loops, {len(bad)} mismatch(es)")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
