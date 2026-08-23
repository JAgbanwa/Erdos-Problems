#!/usr/bin/env python3
"""Did the mathematics change from v1.3 to v1.4?

E2's rederivation was performed against v1.3's Sections 4-9. If those sections are
byte-identical in v1.4, the derivation transfers and the only new work is confirming
identity. If they changed, every changed displayed formula must be re-derived. This
compares section by section and lists every differing displayed formula.
"""
import difflib
import io
import json
import re
import sys

sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding="utf-8", errors="replace")

V13 = ("C:/p3v14/02_validation/00_intake/"
       "PAPER_III_preprint_draft_v1.3_BASELINE.md")
V13_ALT = "C:/p3v13/01_manuscript/PAPER_III_preprint_draft_v1.3.md"
V14 = "C:/p3v14/01_manuscript/PAPER_III_preprint_draft_v1.4.md"
OUT = "C:/erdos_audit/v14/E2/math_delta.json"


def rd(p):
    return open(p, encoding="utf-8", errors="replace").read()


def sections(t):
    """Top-level numbered sections, keyed by their number."""
    out = {}
    hs = [(m.start(), m.group(1)) for m in re.finditer(r"^#\s+(\d+)\.", t, re.M)]
    for i, (pos, num) in enumerate(hs):
        end = hs[i + 1][0] if i + 1 < len(hs) else len(t)
        out[num] = t[pos:end]
    return out


def displays(t):
    """Displayed formulas, whitespace-normalized."""
    return [re.sub(r"\s+", "", x) for x in re.findall(r"\\\[(.+?)\\\]", t, re.S)]


def main():
    import os
    v13p = V13 if os.path.isfile(V13) else V13_ALT
    a, b = rd(v13p), rd(V14)
    print(f"v1.3 source used: {v13p}")
    print(f"v1.3 bytes={len(a.encode()):,}  v1.4 bytes={len(b.encode()):,}\n")

    sa, sb = sections(a), sections(b)
    res = {"v13_source": v13p, "sections": {}}
    print(f"{'sec':>4}  {'v1.3 disp':>9} {'v1.4 disp':>9}  identical  formula-set equal")
    for k in sorted(set(sa) | set(sb), key=lambda x: int(x)):
        x, y = sa.get(k, ""), sb.get(k, "")
        dx, dy = displays(x), displays(y)
        same_text = re.sub(r"\s+", " ", x).strip() == re.sub(r"\s+", " ", y).strip()
        same_forms = dx == dy
        res["sections"][k] = {
            "v13_displays": len(dx), "v14_displays": len(dy),
            "text_identical": same_text, "formula_sequence_identical": same_forms,
            "only_in_v13": [f[:90] for f in dx if f not in dy][:6],
            "only_in_v14": [f[:90] for f in dy if f not in dx][:6]}
        print(f"{k:>4}  {len(dx):>9} {len(dy):>9}  {str(same_text):>9}  {same_forms}")

    core = [k for k in ("4", "5", "6", "7", "8", "9") if k in res["sections"]]
    changed = [k for k in core
               if not res["sections"][k]["formula_sequence_identical"]]
    res["core_sections_4_to_9"] = core
    res["core_sections_with_changed_formulas"] = changed
    print(f"\ncore sections 4-9 present: {core}")
    print(f"core sections whose displayed-formula sequence CHANGED: {changed or 'none'}")
    for k in changed:
        s = res["sections"][k]
        print(f"\n  section {k}: only in v1.3 -> {s['only_in_v13']}")
        print(f"  section {k}: only in v1.4 -> {s['only_in_v14']}")

    json.dump(res, open(OUT, "w", encoding="utf-8"), indent=1, ensure_ascii=False)


if __name__ == "__main__":
    main()
