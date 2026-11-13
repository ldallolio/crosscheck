#!/usr/bin/env python3
# Copyright (c) 2026 Luca Dall'Olio. MIT licence (see the repository's LICENSE).
"""Download the open-access copies of the papers cited in paper/crosscheck.bib.

For every entry with a DOI, the Semantic Scholar Graph API is asked for an open-access
PDF location and an arXiv identifier; Dagstuhl (OASIcs / LIPIcs) papers are fetched from
DROPS. PDFs go to references/pdf/ (gitignored: most are not ours to redistribute), and
references/sources.json records, for each entry, where the copy came from or that none
was found. Nothing but the DOI is sent to these services.

Usage:  python3 references/fetch_papers.py [--only KEY ...]
"""
import argparse, json, pathlib, re, sys, time, urllib.parse, urllib.request

HERE = pathlib.Path(__file__).resolve().parent
BIB = HERE.parent / "paper" / "crosscheck.bib"
UA = {"User-Agent": "reference-fetcher/1.0"}


def entries():
    src = BIB.read_text()
    for m in re.finditer(r"@(\w+)\{([^,]+),(.*?)\n\}", src, re.S):
        body = m.group(3)
        def f(name):
            x = re.search(r"\b" + name + r"\s*=\s*\{(.*?)\}\s*,?\s*\n", body + "\n", re.S)
            return re.sub(r"\s+", " ", x.group(1)) if x else None
        yield dict(key=m.group(2).strip(), kind=m.group(1).lower(), doi=f("doi"), title=f("title"),
                   url=(re.search(r"\\url\{([^}]*)\}", body) or [None, None])[1])


def get(url, binary=False, tries=3):
    for i in range(tries):
        try:
            with urllib.request.urlopen(urllib.request.Request(url, headers=UA), timeout=60) as r:
                data = r.read()
                return data if binary else json.loads(data)
        except Exception as e:  # noqa: BLE001
            err = e
            time.sleep(3 * (i + 1))
    return None


# Known open locations that the index does not report (publisher open access,
# project or institutional pages).
EXTRA = {
    "gustafsson2010malardalen": ("DROPS (Dagstuhl, open access)",
        "https://drops.dagstuhl.de/storage/01oasics/oasics-vol015-wcet2010/OASIcs.WCET.2010.136/OASIcs.WCET.2010.136.pdf"),
    "falke2011termination": ("DROPS (Dagstuhl, open access)",
        "https://drops.dagstuhl.de/storage/00lipics/lipics-vol010-rta2011/LIPIcs.RTA.2011.41/LIPIcs.RTA.2011.41.pdf"),
    "blazy2013formal": ("HAL (Inria)", "https://inria.hal.science/hal-00848703/document"),
    "lattner2004llvm": ("LLVM project page", "https://llvm.org/pubs/2004-01-30-CGO-LLVM.pdf"),
    "floresmontoya2014cofloco": ("authors' technical report (linked from the CoFloCo README)",
        "https://www.se.tu-darmstadt.de/fileadmin/user_upload/Group_SE/Page_Content/Group_Members/Antonio_Flores-Montoya/APLAS14techReport.pdf"),
}


def candidates(e):
    """Possible PDF URLs for an entry, most reliable first."""
    doi = e["doi"]
    out = []
    if e["key"] in EXTRA:
        out.append(EXTRA[e["key"]])
    if doi and doi.startswith("10.1007/"):
        # Served only when the chapter or article is open access.
        out.append(("publisher (Springer, open access)", f"https://link.springer.com/content/pdf/{doi}.pdf"))
    if doi and doi.startswith("10.1145/"):
        out.append(("publisher (ACM, open access)", f"https://dl.acm.org/doi/pdf/{doi}"))
    if doi:
        d = get("https://api.semanticscholar.org/graph/v1/paper/DOI:" + urllib.parse.quote(doi)
                + "?fields=title,openAccessPdf,externalIds")
        if d:
            ax = (d.get("externalIds") or {}).get("ArXiv")
            if ax:
                out.append(("arXiv", f"https://arxiv.org/pdf/{ax}"))
            oa = (d.get("openAccessPdf") or {}).get("url")
            if oa:
                out.append(("open access (Semantic Scholar)", oa))
        time.sleep(1.2)
    return out


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--only", nargs="*")
    a = ap.parse_args()
    pdfs = HERE / "pdf"
    pdfs.mkdir(exist_ok=True)
    log_path = HERE / "sources.json"
    log = json.loads(log_path.read_text()) if log_path.exists() else {}
    for e in entries():
        k = e["key"]
        if a.only and k not in a.only:
            continue
        target = pdfs / f"{k}.pdf"
        if target.exists() and log.get(k, {}).get("status") == "downloaded":
            continue
        rec = dict(doi=e["doi"], title=e["title"], status="no open-access copy found", source=None)
        if e["kind"] in ("book", "misc") and not e["doi"]:
            rec["status"] = "book or web page" + (f": {e['url']}" if e["url"] else "")
        for label, url in candidates(e):
            if url.endswith("/"):
                continue  # DROPS: resolved through Semantic Scholar's link instead
            data = get(url, binary=True, tries=2)
            if data and data[:5] == b"%PDF-":
                target.write_bytes(data)
                rec.update(status="downloaded", source=label, url=url, bytes=len(data))
                break
        log[k] = rec
        log_path.write_text(json.dumps(log, indent=1, sort_keys=True) + "\n")
        print(f"{rec['status']:28s} {k:34s} {rec.get('source') or ''}", flush=True)


if __name__ == "__main__":
    main()
