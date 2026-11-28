#!/usr/bin/env python3
# Copyright (c) 2026 Luca Dall'Olio. MIT licence (see the repository's LICENSE).
"""CrossCheck on the C programs of the complexity category of the Termination
Problem Database (TPDB, directory Complexity_C_Integer), the benchmark set on which
complexity analysers such as KoAT2 and CoFloCo are evaluated in the Termination
Competition. Compared with KoAT2 and CoFloCo, whose answers are read from results/
(produced by tools_in_containers.sh).

TPDB is not copied into this repository; a pinned revision is fetched (sparse) into
.cache/ (gitignored).

The programs are functions with integer parameters and nondeterministic values
(__VERIFIER_nondet_int), and their costs are symbolic (e.g. O(n)). CrossCheck derives
numeric bounds only, so it is run in two modes:

  as-is    the file unchanged (compiled as C), like the other tools;
  bounded  a minimal harness, compiled as C++ for the annotation macros: every `int`
           parameter gets CROSSCHECK_RANGE(-K, K), every value assigned from
           __VERIFIER_nondet_int() gets CROSSCHECK_ASSUME(-K <= v && v <= K), and
           __VERIFIER_nondet_int gets CROSSCHECK_COST(1). A bound found in this mode
           means CrossCheck bounds the loops for inputs in [-K, K]; it is not an
           asymptotic bound, and it is compared with the other tools only on
           whether a bound is found.

The entry function of a file is the defined function that no other function of the
file calls (the last one if there are several).
"""

import argparse
import collections
import concurrent.futures
import json
import pathlib
import re
import subprocess
import sys

REPO = "https://github.com/TermCOMP/TPDB"
REV = "bf19a3c906ac76a49251779e41c3adf144caa16c"  # master, 2025-08-19
SUBDIR = "Complexity_C_Integer"
HERE = pathlib.Path(__file__).resolve().parent
ROOT = HERE.parent.parent
K = 1000

FUNC_DEF = re.compile(r"^((?:[A-Za-z_][\w \t\*]*?)?)\b([A-Za-z_]\w*)\s*\(([^()]*)\)[ \t]*(\{|$)", re.M)
CALL = re.compile(r"\b([A-Za-z_]\w*)\s*\(")
PROTO = re.compile(r"^\s*(?:extern\s+)?(?:int|unsigned|unsigned\s+int|long|_Bool|bool)\s+([A-Za-z_]\w*)\s*\([^()]*\)\s*;", re.M)
KEYWORDS = {"if", "while", "for", "switch", "return", "sizeof", "else"}


def fetch(cache: pathlib.Path) -> pathlib.Path:
    src = cache / "TPDB"
    if not (src / ".git").exists():
        src.mkdir(parents=True, exist_ok=True)
        subprocess.run(["git", "init", "-q"], cwd=src, check=True)
        subprocess.run(["git", "sparse-checkout", "set", "--no-cone", f"/{SUBDIR}/"], cwd=src, check=True)
    head = subprocess.run(["git", "rev-parse", "-q", "--verify", "HEAD"], cwd=src,
                          capture_output=True, text=True).stdout.strip()
    if head != REV:
        subprocess.run(["git", "fetch", "-q", "--depth", "1", "--filter=blob:none", REPO, REV], cwd=src, check=True)
        subprocess.run(["git", "checkout", "-q", "--detach", REV], cwd=src, check=True)
    return src / SUBDIR


def strip_comments(text):
    text = re.sub(r"/\*.*?\*/", lambda m: "\n" * m.group(0).count("\n"), text, flags=re.S)
    return re.sub(r"//[^\n]*", "", text)


def definitions(text):
    """Names of the functions defined in the file, in order."""
    out = []
    for m in FUNC_DEF.finditer(text):
        name = m.group(2)
        if name in KEYWORDS or m.group(1).strip() in ("return", "else"):
            continue
        rest = text[m.end(3):]
        if re.match(r"\)\s*\{", rest) or re.match(r"\)\s*\n\s*\{", rest):
            out.append(name)
    return out


def entry_function(text):
    text = strip_comments(text)
    defs = definitions(text)
    # a definition's own header also matches CALL: a function called nowhere else occurs once
    counts = collections.Counter(m.group(1) for m in CALL.finditer(text))
    roots = [d for d in defs if counts[d] <= 1]
    return (roots or defs or [None])[-1]


def inputs_as_parameters(text, externs):
    """The `symbolic` mode: in the entry function, a value read from an undefined function
    (a nondeterministic input) before the first loop becomes a parameter, `x = nondet();`
    being replaced by `x = in_k;`. The competition's tools treat these values as inputs
    of the program too; a certified bound can only mention parameters. Values read inside
    or after a loop are left as they are. `main` is renamed `main_` (it gets parameters)."""
    entry = entry_function(text)
    if not externs or entry is None:
        return text
    for m in FUNC_DEF.finditer(text):
        if m.group(2) == entry and m.group(4) == "{":
            break
    else:
        return text
    loop = re.compile(r"\b(while|for|do)\b").search(text, m.end())
    end = loop.start() if loop else len(text)
    k = [0]
    def sub(a):
        k[0] += 1
        return f"{a.group(1)}in_{k[0]};"
    head = re.sub(r"(=\s*)(?:%s)\s*\(\s*\)\s*;" % "|".join(map(re.escape, externs)), sub, text[m.end():end])
    if not k[0]:
        return text
    old = m.group(3).strip()
    ps = ([] if old in ("", "void") else [old]) + [f"int in_{i}" for i in range(1, k[0] + 1)]
    name = "main_" if entry == "main" else entry
    return text[:m.start()] + f"{m.group(1)}{name}({', '.join(ps)}){m.group(4)}" + head + text[end:]


def harness(text, ranges=True):
    """The `bounded` mode: ranges on int parameters and nondeterministic values. Without
    `ranges` (the `symbolic` mode): only the unit cost of the undefined functions."""
    text = strip_comments(text)
    defs = set(definitions(text))
    externs = [n for n in PROTO.findall(text) if n not in defs]
    def params(m):
        ps = []
        for p in m.group(3).split(","):
            q = p.strip()
            if ranges and re.fullmatch(r"(?:signed\s+)?int\s+[A-Za-z_]\w*", q):
                q = f"CROSSCHECK_RANGE(-{K}, {K}) {q}"
            ps.append(q)
        return f"{m.group(1)}{m.group(2)}({', '.join(ps)}){m.group(4)}"
    if not ranges:
        text = inputs_as_parameters(text, externs)
    out = FUNC_DEF.sub(lambda m: params(m) if m.group(2) not in KEYWORDS else m.group(0), text)
    # functions declared but not defined (nondeterministic values): unit cost, and a
    # range on every variable assigned from one of them
    out = PROTO.sub(lambda m: "CROSSCHECK_COST(1) " + m.group(0).lstrip() if m.group(1) in externs else m.group(0), out)
    if externs and ranges:
        assign = re.compile(r"(\b(?:int\s+)?([A-Za-z_]\w*)\s*=\s*(?:%s)\s*\(\s*\)\s*;)" % "|".join(map(re.escape, externs)))
        out = assign.sub(lambda m: f"{m.group(1)} CROSSCHECK_ASSUME(-{K} <= {m.group(2)} && {m.group(2)} <= {K});", out)
    return "#include <crosscheck/attributes.hpp>\n" + out


def run_crosscheck(tool, path, mode, work, extra, stem, certdir=None, minic=False):
    work.mkdir(parents=True, exist_ok=True)
    report = work / f"{stem}.{mode}.json"
    if mode == "as-is":
        src, args = path, ["-x", "c", "-std=gnu11", "-w"]
    else:
        src = work / f"{stem}.{mode}.cpp"
        src.write_text(harness(path.read_text(errors="replace"), ranges=(mode == "bounded")))
        args = ["-x", "c++", "-std=c++20", "-w", f"-I{ROOT / 'clang-plugin/include'}"]
    certs = [f"--opt=certificates={certdir / (stem + '.json')}"] if certdir and mode == "bounded" else []
    if mode == "symbolic":  # no ranges: potentials only, and a bound in the parameters for the checker
        certs = ["--opt=symbolic", f"--opt=certificates={certdir / 'symbolic' / (stem + '.json')}"]
    if certs and minic:  # mini-C sources, validated by the checker
        certs.append("--opt=minic")
    try:
        subprocess.run([str(tool), "--all", f"--report={report}", *certs, str(src), "--", *args, *extra],
                       capture_output=True, text=True, timeout=120)
    except subprocess.TimeoutExpired:
        return {"__timeout__": True}
    if not report.exists():
        return {}
    out = {f["name"]: bool(f["ok"]) for f in json.loads(report.read_text())["functions"]}
    out["__symbolic__"] = {f["name"] for f in json.loads(report.read_text())["functions"] if f.get("symbolic")}
    if mode == "symbolic" and "main_" in out:  # renamed by inputs_as_parameters
        out["main"] = out["main_"]
        if "main_" in out["__certs__"]:
            out["__certs__"]["main"] = out["__certs__"]["main_"]
        if "main_" in out["__symbolic__"]:
            out["__symbolic__"].add("main")
    # certificates: per function, "symbolic" (a summary in the parameters), "constant" or absent
    out["__certs__"] = {f["name"]: ("symbolic" if "max(" in (f.get("certificate_summary") or "") else "constant")
                        for f in json.loads(report.read_text())["functions"] if f.get("certificate") == "emitted"}
    return out


def koat_answer(tsv, fn):
    if not tsv.exists():
        return None
    for line in tsv.read_text().splitlines():
        name, _, ans = line.partition("\t")
        if name == fn:
            ans = ans.strip()
            if not ans or ans.startswith("!") or "Infinity" in ans or ans.startswith("inf"):
                return "none"
            m = re.search(r"\{O\(([^)]*)\)\}", ans)
            return "O(" + m.group(1) + ")" if m else "bound"
    return "none"


def cofloco_answer(tsv, fn):
    if not tsv.exists():
        return None
    for line in tsv.read_text().splitlines():
        parts = [p.strip() for p in line.split("\t")]
        if parts[0] == fn:
            if len(parts) < 3 or parts[1].startswith("!") or parts[2] in ("infinity", "unknown"):
                return "none"
            return {"constant": "O(1)"}.get(parts[2], "O(" + parts[2] + ")")
    return "none"


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--tool", default=str(ROOT / "clang-plugin/build/crosscheck-tool"))
    ap.add_argument("--cache", default=str(HERE / ".cache"))
    ap.add_argument("--extra-arg", action="append", default=[])
    ap.add_argument("--results", default=str(HERE / "results"))
    ap.add_argument("--json")
    ap.add_argument("--jobs", type=int, default=1, help="programs analysed in parallel")
    ap.add_argument("--list", action="store_true", help="only print the files and their entry functions")
    ap.add_argument("--certificates", help="emit certificates (inputs-in-range mode) into this directory")
    ap.add_argument("--checker", help="crosscheck-check executable: check them (needs --certificates)")
    ap.add_argument("--minic", action="store_true", help="also export mini-C sources and validate the certificates")
    ap.add_argument("--only-symbolic", action="store_true", help="with --symbolic: skip the two other modes")
    ap.add_argument("--symbolic", action="store_true",
                    help="a third mode, without input ranges: option `symbolic` of the tool, and certificates "
                         "with a bound in the parameters (needs --certificates; with --checker they are checked)")
    a = ap.parse_args()
    base = fetch(pathlib.Path(a.cache))
    files = sorted(base.rglob("*.c"))
    if a.list:
        for f in files:
            print(f"{f.relative_to(base)}\t{entry_function(f.read_text(errors='replace'))}")
        return
    res = pathlib.Path(a.results)

    def one(f):
        rel = f.relative_to(base)
        text = f.read_text(errors="replace")
        entry = entry_function(text)
        key = str(rel).replace("/", "__")[:-2]
        row = dict(file=str(rel), family=rel.parts[0], entry=entry)
        certdir = pathlib.Path(a.certificates) if a.certificates else None
        if certdir:
            certdir.mkdir(parents=True, exist_ok=True)
        for mode in ("as-is", "bounded"):
            if a.only_symbolic:
                row[f"crosscheck_{mode}"] = "none"
                continue
            r = run_crosscheck(a.tool, f, mode, pathlib.Path(a.cache) / "work", a.extra_arg, key, certdir, a.minic)
            row[f"crosscheck_{mode}"] = "timeout" if "__timeout__" in r else (
                "bound" if r.get(entry) else "none")
            if mode == "bounded" and certdir:
                row["certificate"] = r.get("__certs__", {}).get(entry)
        if a.symbolic and certdir:
            (certdir / "symbolic").mkdir(parents=True, exist_ok=True)
            r = run_crosscheck(a.tool, f, "symbolic", pathlib.Path(a.cache) / "work", a.extra_arg, key, certdir)
            cert = r.get("__certs__", {}).get(entry)
            # certified for all inputs: a constant bound, or a summary in the parameters
            row["crosscheck_symbolic"] = ("timeout" if "__timeout__" in r else cert if cert else
                                          "potentials only" if entry in r.get("__symbolic__", ()) else "none")
        row["koat"] = koat_answer(res / "koat2" / f"{key}.tsv", entry)
        row["cofloco"] = cofloco_answer(res / "cofloco" / f"{key}.tsv", entry)
        print(f"{rel}\t{entry}\t{row['crosscheck_as-is']}\t{row['crosscheck_bounded']}\t{row['koat']}\t{row['cofloco']}",
              file=sys.stderr)
        return row

    # programs in parallel (each run is its own process; the rows keep the order of the files)
    with concurrent.futures.ThreadPoolExecutor(max_workers=max(1, a.jobs)) as pool:
        rows = list(pool.map(one, files))
    fams = sorted({r["family"] for r in rows})
    tools = ("crosscheck_as-is", "crosscheck_bounded", "koat", "cofloco")
    print("| Family | Programs | CrossCheck as is | CrossCheck, inputs in [-%d, %d] | KoAT2 | CoFloCo |" % (K, K))
    print("|---|---:|---:|---:|---:|---:|")
    for fam in fams + ["Total"]:
        rs = [r for r in rows if fam == "Total" or r["family"] == fam]
        cells = [str(sum(1 for r in rs if r[t] not in (None, "none", "timeout"))) for t in tools]
        print(f"| {fam} | {len(rs)} | " + " | ".join(cells) + " |")
    both = collections.Counter((r["crosscheck_bounded"] == "bound",
                                r["koat"] not in (None, "none") or r["cofloco"] not in (None, "none")) for r in rows)
    print("\nbounded-mode CrossCheck vs (KoAT2 or CoFloCo):", dict(both))
    if a.symbolic and a.certificates:
        c = collections.Counter(r.get("crosscheck_symbolic") for r in rows)
        print(f"\nwithout input ranges (option symbolic), entry functions: {c.get('symbolic', 0)} with a "
              f"certificate whose bound is in the parameters, {c.get('constant', 0)} with a constant "
              f"certified bound, {c.get('potentials only', 0)} with potentials for every loop but no "
              f"certificate, {c.get('none', 0)} without, {c.get('timeout', 0)} timeouts")
        byfam = collections.Counter(r["family"] for r in rows if r.get("crosscheck_symbolic") in ("symbolic", "constant"))
        print("  by family:", dict(sorted(byfam.items())))
        other = collections.Counter((r.get("crosscheck_symbolic") in ("symbolic", "constant"),
                                     r["koat"] not in (None, "none") or r["cofloco"] not in (None, "none")) for r in rows)
        print("  certified without ranges vs (KoAT2 or CoFloCo):", dict(other))
        lin = collections.Counter((r["koat"] or "none") for r in rows if r.get("crosscheck_symbolic") == "symbolic")
        print("  KoAT2's answers on those with a summary in the parameters:", dict(lin.most_common()))
        if a.checker:
            sfiles = sorted(str(p) for p in (pathlib.Path(a.certificates) / "symbolic").glob("*.json"))
            proc = subprocess.run([a.checker, *sfiles], capture_output=True, text=True)
            lines = proc.stdout.splitlines()
            print(f"  checker: {sum(l.startswith('ACCEPTED') for l in lines)} functions accepted, "
                  f"{sum(l.startswith('REJECTED') or (l.startswith('PROGRAM') and 'REJECTED' in l) for l in lines)} "
                  f"rejected (exit {proc.returncode})")
    if a.certificates:
        c = collections.Counter(r.get("certificate") for r in rows if r["crosscheck_bounded"] == "bound")
        print(f"certificates of bounded entry functions: {c.get('symbolic', 0)} with a summary in the "
              f"parameters, {c.get('constant', 0)} constant, {c.get(None, 0)} none")
        lin = sum(1 for r in rows if r.get("certificate") == "symbolic" and (r["koat"] or "").startswith("O(n")
                  and (r["koat"] or "") in ("O(n)", "O(n^1)"))
        print(f"  of the symbolic ones, KoAT2 also gives a linear bound for {lin}")
        if a.checker:
            files = sorted(str(p) for p in pathlib.Path(a.certificates).glob("*.json"))
            proc = subprocess.run([a.checker, *files], capture_output=True, text=True)
            lines = proc.stdout.splitlines()
            acc = sum(l.startswith("ACCEPTED") for l in lines)
            rej = sum(l.startswith("REJECTED") or (l.startswith("PROGRAM") and "REJECTED" in l) for l in lines)
            print(f"checker: {acc} functions accepted, {rej} rejected (exit {proc.returncode})")
            if a.minic:
                val = sum(l.startswith("VALIDATED") for l in lines)
                notval = sum(l.startswith("NOT VALIDATED") for l in lines)
                refused = collections.Counter()
                for f in files:
                    for prog in json.loads(pathlib.Path(f).read_text())["programs"]:
                        for fn in prog["functions"]:
                            if "body" in fn and "source" not in fn and "jsource" not in fn:
                                refused[fn.get("source_refused", "?")] += 1
                print(f"mini-C: {val} validated, {notval} not validated, {sum(refused.values())} not exported")
                for why, n in refused.most_common():
                    print(f"  {n:4d} not exported: {why}")
    if a.json:
        pathlib.Path(a.json).write_text(json.dumps(rows, indent=2) + "\n")


if __name__ == "__main__":
    main()
