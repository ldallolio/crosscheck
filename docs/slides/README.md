# Slides

A short presentation of CrossCheck ([Slidev](https://sli.dev), Markdown in `slides.md`): the
idea and a little theory, one example followed through the whole pipeline with its real
artifacts (C source, the plugin's untrusted facts, the source certificate and the checker's
verdict, the Lean theorems, the Cortex-M0 machine code, the cycle certificate with a loop
bound proved on the instructions, an emulated run, the time budget after linking, a
tampered certificate rejected), time and complexity, what is trusted, the benchmarks and
the comparison with other tools.

```bash
cd docs/slides
npm install                  # Slidev 53.1.0, pinned in package.json
npm run dev                  # presenter at http://localhost:3030
npm run build                # static site in dist/
npm run export               # PDF (uses playwright-chromium: npx playwright install chromium)
```

## The example

`demo/fir.c`: an 8-tap FIR filter over a block of 1 to 56 samples with a 500 µs budget at
48 MHz. `python3 docs/slides/demo/run_demo.py` (from the repository root, after building the
plugin and `lake build crosscheck-check`; needs scipy) regenerates every artifact the slides
show into `demo/out/`, with paths relative to the repository: `report.json`,
`source-cert.json`, `check-source.txt`, `fir.s`, `cycles-cert.json`, `check-cycles.txt`,
`budget.txt`, `check-tampered.txt`, `summary.json`, `times.json`. The slides quote these
files; after a change of the tools, rerun the script and update the quotes.

The benchmark figures are those of `benchmarks/*/README.md` and the papers (reproduced on
2026-11-21, `docs/release-checklist.md`).
