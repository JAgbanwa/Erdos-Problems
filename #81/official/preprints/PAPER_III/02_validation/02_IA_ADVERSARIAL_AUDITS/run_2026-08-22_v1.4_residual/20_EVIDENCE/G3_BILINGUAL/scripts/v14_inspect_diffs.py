#!/usr/bin/env python3
"""Inspect the four EN/ES block differences the deep comparison flagged, and identify the
one formal identifier that does not appear literally in either TeX."""
import io
import re
import sys

sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding="utf-8", errors="replace")

T = "C:/p3v14/01_manuscript"
EN_MD = f"{T}/PAPER_III_preprint_draft_v1.4.md"
ES_MD = f"{T}/PAPER_III_preprint_draft_v1.4_es.md"
EN_TEX = f"{T}/PAPER_III_preprint_draft_v1.4_en.tex"
ES_TEX = f"{T}/PAPER_III_preprint_draft_v1.4_es.tex"

INLINE = re.compile(re.escape("\\("))
HEAD = re.compile(r"^#{1,6}\s+.+$", re.M)


def rd(p):
    return open(p, encoding="utf-8", errors="replace").read()


def main():
    en, es = rd(EN_MD), rd(ES_MD)
    be = [m.start() for m in HEAD.finditer(en)]
    bs = [m.start() for m in HEAD.finditer(es)]

    for idx in (0, 69, 95):
        e = en[be[idx]:be[idx + 1]]
        s = es[bs[idx]:bs[idx + 1]]
        print(f"===== block {idx}: inline EN={len(INLINE.findall(e))} "
              f"ES={len(INLINE.findall(s))}")
        print("  EN:", re.sub(r"\s+", " ", e)[:340])
        print("  ES:", re.sub(r"\s+", " ", s)[:340])
        print()

    print("===== the identifier absent from each TeX")
    for lang, md, tex in (("EN", EN_MD, EN_TEX), ("ES", ES_MD, ES_TEX)):
        m, x = rd(md), rd(tex)
        ids = sorted(set(re.findall(
            r"`([A-Za-z][A-Za-z0-9_.]*\.[A-Za-z0-9_.]+)`", m)))
        miss = [i for i in ids
                if i not in x and i.replace("_", "\\_") not in x]
        print(f"  {lang}: {miss}")
        for i in miss:
            j = m.find(i)
            print("     MD context:",
                  re.sub(r"\s+", " ", m[max(0, j - 170):j + 130]))
            # is any prefix of it present in the tex?
            head = i.split(".")[0]
            print(f"     namespace '{head}' appears in the TeX: "
                  f"{head in x or head.replace('_', chr(92) + '_') in x}")


if __name__ == "__main__":
    main()
