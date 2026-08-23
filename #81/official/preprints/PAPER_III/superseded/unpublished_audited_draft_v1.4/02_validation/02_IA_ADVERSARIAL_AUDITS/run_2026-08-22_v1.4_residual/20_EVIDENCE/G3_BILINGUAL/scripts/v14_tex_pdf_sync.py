#!/usr/bin/env python3
"""Are the delivered TeX and the delivered PDF in sync?

The MD names PaperIII.CanonicalTrianglePackingGate three times and the PDF text contains it
three times, but the TeX contains it zero times even ignoring whitespace. Either the TeX is
not the source of the PDF, or the table is rendered from somewhere else. This locates the
table in the TeX and measures the divergence on a broader sample of tokens.
"""
import io
import re
import sys

sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding="utf-8", errors="replace")

T = "C:/p3v14/01_manuscript"
E5 = "C:/erdos_audit/v14/E5"


def rd(p):
    return open(p, encoding="utf-8", errors="replace").read()


def cesu(path):
    b = open(path, "rb").read()
    s = b.decode("utf-8", "surrogatepass")
    out = []
    i = 0
    while i < len(s):
        c = s[i]
        if 0xD800 <= ord(c) <= 0xDBFF and i + 1 < len(s) \
           and 0xDC00 <= ord(s[i + 1]) <= 0xDFFF:
            out.append(chr(0x10000 + ((ord(c) - 0xD800) << 10)
                           + (ord(s[i + 1]) - 0xDC00)))
            i += 2
        else:
            out.append(c)
            i += 1
    return "".join(out)


def main():
    for lang, md, tex, pdftxt in (
            ("EN", f"{T}/PAPER_III_preprint_draft_v1.4.md",
             f"{T}/PAPER_III_preprint_draft_v1.4_en.tex", f"{E5}/pdf_en.txt"),
            ("ES", f"{T}/PAPER_III_preprint_draft_v1.4_es.md",
             f"{T}/PAPER_III_preprint_draft_v1.4_es.tex", f"{E5}/pdf_es.txt")):
        m, x = rd(md), rd(tex)
        p = cesu(pdftxt)
        mf = re.sub(r"\s+", "", m)
        xf = re.sub(r"\s+", "", x)
        pf = re.sub(r"\s+", "", p)
        print(f"===== {lang}")
        print(f"  sizes: md={len(m):,}  tex={len(x):,}  pdftext={len(p):,}")

        # locate the Lean-surface table in the TeX by a neighbouring key
        k = xf.find("PaperIII.CanonicalTrianglePacking")
        print(f"  'PaperIII.CanonicalTrianglePacking' in tex(flat): "
              f"{xf.count('PaperIII.CanonicalTrianglePacking')}")
        j = x.find("CanonicalTrianglePacking")
        if j >= 0:
            print("  raw TeX around the first hit:")
            print("   ", repr(x[max(0, j - 260):j + 320]))

        # broader divergence sample: every backtick token of the md
        toks = sorted(set(re.findall(r"`([A-Za-z][A-Za-z0-9_.]{6,})`", m)))
        miss_tex, miss_pdf = [], []
        for t in toks:
            tf = t.replace("_", "")
            if t not in xf and t.replace("_", "\\_") not in xf:
                miss_tex.append(t)
            if tf not in re.sub(r"[_\\]", "", pf):
                miss_pdf.append(t)
        print(f"  code tokens in md: {len(toks)}")
        print(f"  absent from TeX : {len(miss_tex)} -> {miss_tex[:8]}")
        print(f"  absent from PDF : {len(miss_pdf)} -> {miss_pdf[:8]}")

        # equation tags: md vs tex vs pdf
        tags = sorted(set(re.findall(r"\\tag\{([^}]+)\}", m)))
        print(f"  eq tags md={len(tags)}  in tex="
              f"{sum(1 for t in tags if t in x)}  "
              f"in pdf={sum(1 for t in tags if f'({t})' in p or t in pf)}")
        print()


if __name__ == "__main__":
    main()
