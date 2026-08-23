#!/usr/bin/env python3
"""E1 supplement - locate every changed hunk by section, and confirm the mathematical core
was not touched.

Delta containment by keyword is necessary but not sufficient: a quantifier or constant could
in principle be altered inside prose that also carries a release-status keyword. This locates
each hunk in the document's section structure and asserts that no hunk falls inside the
mathematical core (Sections 3-10 and Appendices A-C, E), and that Appendix D hunks are exactly
the two declared clarifications.
"""
import difflib
import io
import json
import os
import re
import sys

sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding="utf-8", errors="replace")

T = "C:/p3v15"
OLD = f"{T}/superseded/unpublished_audited_draft_v1.4/01_manuscript"
NEW = f"{T}/01_manuscript"
OUT = "C:/v15r/20_EVIDENCE/E1_DELTA"

PAIRS = {"EN": (f"{OLD}/PAPER_III_preprint_draft_v1.4.md",
                f"{NEW}/PAPER_III_preprint_v1.5.md"),
         "ES": (f"{OLD}/PAPER_III_preprint_draft_v1.4_es.md",
                f"{NEW}/PAPER_III_preprint_v1.5_es.md")}

# Sections whose content is mathematical. A hunk landing here is a potential regression.
CORE = re.compile(r"^(?:#\s+)?(?:3|4|5|6|7|8|9|10)\.|^Appendix\s+[ABCE]\b|^Ap[eé]ndice\s+[ABCE]\b")


def rd(p):
    return open(p, encoding="utf-8", errors="replace").read()


def section_index(lines):
    """For each line number, the most recent top-level or sub heading text."""
    out, cur = [], "(front matter)"
    for l in lines:
        m = re.match(r"^(#{1,3})\s+(.*\S)\s*$", l)
        if m and len(m.group(1)) <= 2:
            cur = m.group(2)
        out.append(cur)
    return out


def main():
    os.makedirs(OUT, exist_ok=True)
    res, ok = {}, True
    for lang, (op, np_) in PAIRS.items():
        la, lb = rd(op).splitlines(), rd(np_).splitlines()
        sa, sb = section_index(la), section_index(lb)
        sm = difflib.SequenceMatcher(None, la, lb, autojunk=False)
        hunks = []
        for tag, i1, i2, j1, j2 in sm.get_opcodes():
            if tag == "equal":
                continue
            secs = sorted({sa[k] for k in range(i1, min(i2, len(sa)))} |
                          {sb[k] for k in range(j1, min(j2, len(sb)))})
            sample = next((x for x in lb[j1:j2] if x.strip()),
                          next((x for x in la[i1:i2] if x.strip()), ""))
            hunks.append({"op": tag, "old_range": [i1 + 1, i2], "new_range": [j1 + 1, j2],
                          "sections": secs, "sample": sample[:150],
                          "in_core": any(CORE.match(s) for s in secs)})
        core_hits = [h for h in hunks if h["in_core"]]
        appd = [h for h in hunks
                if any(re.match(r"^(Appendix D|Ap[eé]ndice D)|^D\.\d", s)
                       or "D.1" in s or "D.3" in s for s in h["sections"])]
        print(f"\n=== {lang}: {len(hunks)} hunks")
        for h in hunks:
            flag = "  <-- CORE" if h["in_core"] else ""
            print(f"  [{h['op']:7}] {'/'.join(h['sections'])[:52]:54} "
                  f"{h['sample'][:60]}{flag}")
        print(f"  hunks inside the mathematical core (Sections 3-10, App. A/B/C/E): "
              f"{len(core_hits)}")
        print(f"  hunks inside Appendix D: {len(appd)}")
        res[lang] = {"hunks": hunks, "core_hits": len(core_hits),
                     "appendix_D_hunks": len(appd),
                     "pass": not core_hits and len(appd) == 2}
        ok &= res[lang]["pass"]
        print(f"  ===> {lang}: {'PASS' if res[lang]['pass'] else 'FAIL'} "
              f"(expected 0 core hunks and exactly 2 Appendix D hunks)")
    res["pass"] = ok
    print(f"\nsection-location check: {'PASS' if ok else 'FAIL'}")
    with open(f"{OUT}/E1_hunk_sections.json", "w", encoding="utf-8", newline="\n") as f:
        json.dump(res, f, indent=1, ensure_ascii=False)
        f.write("\n")


if __name__ == "__main__":
    main()
