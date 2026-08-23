#!/usr/bin/env python3
"""Is the CanonicalTrianglePackingGate table row lost in the MD -> TeX conversion, and does
the module it names exist in the frozen archive?"""
import io
import os
import re
import sys
import zipfile

sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding="utf-8", errors="replace")

T = "C:/p3v14/01_manuscript"
FZ = "C:/p3v14/05_formalization/lean_v1.4_freeze"
NAME = "CanonicalTrianglePackingGate"


def rd(p):
    return open(p, encoding="utf-8", errors="replace").read()


def main():
    for lang, md, tex in (("EN", f"{T}/PAPER_III_preprint_draft_v1.4.md",
                           f"{T}/PAPER_III_preprint_draft_v1.4_en.tex"),
                          ("ES", f"{T}/PAPER_III_preprint_draft_v1.4_es.md",
                           f"{T}/PAPER_III_preprint_draft_v1.4_es.tex")):
        m, x = rd(md), rd(tex)
        print(f"===== {lang}")
        print(f"  in MD : {m.count(NAME)}   in TeX: {x.count(NAME)}")
        # the surrounding table in the MD
        j = m.find(NAME)
        line_start = m.rfind("\n", 0, j) + 1
        line_end = m.find("\n", j)
        row = m[line_start:line_end]
        print(f"  MD row: {row.strip()[:150]}")
        # find neighbouring rows and check whether THEY made it into the TeX
        prev_start = m.rfind("\n", 0, line_start - 1) + 1
        prev = m[prev_start:line_start - 1].strip()
        nxt_end = m.find("\n", line_end + 1)
        nxt = m[line_end + 1:nxt_end].strip()
        for label, r in (("previous row", prev), ("next row", nxt)):
            key = re.findall(r"`([^`]+)`", r)
            present = [k for k in key
                       if k in x or k.replace("_", "\\_") in x]
            print(f"  {label}: keys={key[:3]} present in TeX={present[:3]}")
        # how many rows does that table have in md vs tex
        # locate the table block in the md
        s = line_start
        while s > 0:
            ps = m.rfind("\n", 0, s - 1) + 1
            if not m[ps:s - 1].strip().startswith("|"):
                break
            s = ps
        e = line_end
        while True:
            ne = m.find("\n", e + 1)
            if ne < 0 or not m[e + 1:ne].strip().startswith("|"):
                break
            e = ne
        table = m[s:e]
        rows = [l for l in table.split("\n")
                if l.strip().startswith("|") and set(l.strip()) - set("|-: ")]
        print(f"  MD table rows (incl. header): {len(rows)}")
        keys = [re.findall(r"`([^`]+)`", r) for r in rows]
        flat = [k for ks in keys for k in ks]
        inx = [k for k in flat if k in x or k.replace("_", "\\_") in x]
        print(f"  code keys in that table: {len(flat)}   present in TeX: {len(inx)}")
        missing = [k for k in flat if k not in inx]
        print(f"  MISSING from TeX: {missing}")

    print("\n===== does the module exist in the frozen archive?")
    p = os.path.join(FZ, "PaperIII", NAME + ".lean")
    print(f"  PaperIII/{NAME}.lean on disk: {os.path.isfile(p)}")
    z = zipfile.ZipFile(os.path.join(FZ, "PAPER_III_lean_v1.4_freeze.zip"))
    hits = [n for n in z.namelist() if NAME in n]
    print(f"  entries in the ZIP matching '{NAME}': {hits}")
    src = os.path.join(FZ, "SOURCE_MANIFEST.sha256")
    if os.path.isfile(src):
        t = rd(src)
        print(f"  named in SOURCE_MANIFEST: {NAME in t}")
    # which freeze query file imports it
    for f in sorted(os.listdir(FZ)):
        if f.startswith("FreezeAxioms") and f.endswith(".lean"):
            t = rd(os.path.join(FZ, f))
            if NAME in t:
                print(f"  imported by {f}: yes")


if __name__ == "__main__":
    main()
