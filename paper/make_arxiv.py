#!/usr/bin/env python3
# Copyright (c) 2026 Luca Dall'Olio. All rights reserved.
# Released under the MIT license as described in the file LICENSE.
"""Self-contained arXiv source bundles of the papers.

    (cd paper/theory && latexmk -pdf crosscheck-theory.tex)   # first: the .aux and .bbl
    (cd paper/tool && latexmk -pdf crosscheck-tool.tex)
    (cd paper/binary && latexmk -pdf crosscheck-binary.tex)
    python3 paper/make_arxiv.py [--out paper/arxiv] [theory tool binary]

For each paper, `OUT/<paper>/` gets the .tex and its .bbl (arXiv does not run BibTeX), with
the bibliography path `../crosscheck` replaced by the paper's own name. References to the
other papers' numbered results (`\\ref{I-label}`, `\\ref{II-label}`, through `xr`) are
replaced by the numbers in those papers' .aux files, and `xr` is removed, so a bundle needs
no file of another paper. Each bundle is then compiled three times with pdflatex in an empty
directory; the script fails if a reference or citation is undefined or the source is not
ASCII. `OUT/<paper>.tar.gz` is the file to upload. Nothing is uploaded.
"""
import argparse
import pathlib
import re
import shutil
import subprocess
import sys
import tarfile
import tempfile

HERE = pathlib.Path(__file__).resolve().parent
PAPERS = {"theory": "crosscheck-theory", "tool": "crosscheck-tool", "binary": "crosscheck-binary"}
PREFIX = {"I": "theory", "II": "tool"}


def labels(aux):
    """label -> number, from a .aux file (hyperref's five-field \\newlabel)."""
    out = {}
    for m in re.finditer(r"\\newlabel\{([^}]*)\}\{\{([^}]*)\}", aux.read_text(errors="replace")):
        out[m.group(1)] = m.group(2)
    return out


def bundle(name, out):
    src = HERE / name / f"{PAPERS[name]}.tex"
    text = src.read_text()
    if any(ord(c) > 127 for c in text):
        sys.exit(f"{src}: not ASCII")
    for pre, other in PREFIX.items():
        if f"\\externaldocument[{pre}-]" not in text:
            continue
        nums = labels(HERE / other / f"{PAPERS[other]}.aux")

        def repl(m, nums=nums, pre=pre):
            lab = m.group(1)
            if lab not in nums:
                sys.exit(f"{name}: {pre}-{lab} is not in the .aux of {other}")
            return nums[lab]
        text = re.sub(r"\\ref\{" + pre + r"-([^}]*)\}", repl, text)
        text = re.sub(r"\\externaldocument\[" + pre + r"-\]\{[^}]*\}\n?", "", text)
    text = text.replace("\\usepackage{xr-hyper}\n", "")
    if re.search(r"\\ref\{(I|II)-", text):
        sys.exit(f"{name}: unresolved cross-paper reference")
    text = text.replace("\\bibliography{../crosscheck}", f"\\bibliography{{{PAPERS[name]}}}")
    d = out / name
    if d.exists():
        shutil.rmtree(d)
    d.mkdir(parents=True)
    (d / f"{PAPERS[name]}.tex").write_text(text)
    shutil.copy(HERE / name / f"{PAPERS[name]}.bbl", d / f"{PAPERS[name]}.bbl")
    # compile the bundle alone
    with tempfile.TemporaryDirectory() as t:
        for f in d.iterdir():
            shutil.copy(f, t)
        for _ in range(3):
            p = subprocess.run(["pdflatex", "-interaction=nonstopmode", "-halt-on-error", PAPERS[name]],
                               cwd=t, capture_output=True, text=True)
            if p.returncode:
                sys.exit(f"{name}: pdflatex failed:\n" + p.stdout[-1500:])
        log = (pathlib.Path(t) / f"{PAPERS[name]}.log").read_text(errors="replace")
        bad = [l for l in log.splitlines() if re.search(r"undefined|Warning", l)]
        if bad:
            sys.exit(f"{name}: warnings in the bundle:\n" + "\n".join(bad[:10]))
        pages = re.search(r"Output written on .* \((\d+) pages", log)
    tgz = out / f"{name}.tar.gz"
    with tarfile.open(tgz, "w:gz") as tar:
        for f in sorted(d.iterdir()):
            tar.add(f, arcname=f.name)
    print(f"{name}: {tgz} ({pages.group(1) if pages else '?'} pages), compiled alone without warnings")


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("papers", nargs="*", default=["theory", "tool"], choices=sorted(PAPERS))
    ap.add_argument("--out", default=str(HERE / "arxiv"))
    a = ap.parse_args()
    out = pathlib.Path(a.out)
    out.mkdir(parents=True, exist_ok=True)
    for name in a.papers:
        bundle(name, out)


if __name__ == "__main__":
    main()
