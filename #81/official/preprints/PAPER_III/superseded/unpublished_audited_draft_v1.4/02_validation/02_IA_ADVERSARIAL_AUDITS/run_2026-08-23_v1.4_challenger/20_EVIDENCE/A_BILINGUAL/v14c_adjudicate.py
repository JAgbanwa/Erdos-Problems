#!/usr/bin/env python3
"""Adjudicate the three structural differences the bilingual comparator flagged.

Each candidate must be shown to be translation/localization rather than loss:
  1. displayed formulas   -> differ only inside \\text{...} / \\mbox{...} operands?
  2. table rows           -> differ only in decimal-group separators (8,455 vs 8.455)?
  3. long paragraphs      -> is the extra Spanish paragraph a split of an English one
                             (same content, different break), or is content added/lost?
For (3) the test is content-based: compare the concatenated section text after removing
paragraph breaks, and check that no English sentence lacks a Spanish counterpart by
comparing counts of language-invariant anchors (math spans, citations, code spans) and
the sentence count per section.
"""
import io
import json
import re
import sys

sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding="utf-8", errors="replace")

EN = "C:/p3v14/01_manuscript/PAPER_III_preprint_draft_v1.4.md"
ES = "C:/p3v14/01_manuscript/PAPER_III_preprint_draft_v1.4_es.md"
OUT = "C:/v14c/20_EVIDENCE/A_BILINGUAL/adjudication.json"


def rd(p):
    return open(p, encoding="utf-8", errors="replace").read()


def strip_text_ops(s):
    """Blank out the operand of every \\text-like command: those operands are prose and
    are expected to be translated."""
    for cmd in ("text", "textrm", "textit", "textbf", "mbox", "operatorname", "mathrm"):
        s = re.sub(r"\\" + cmd + r"\{[^{}]*\}", "\\\\" + cmd + "{@}", s)
    return s


def displays(t):
    return [re.sub(r"\s+", "", x) for x in re.findall(r"\\\[(.+?)\\\]", t, re.S)]


def sections(t):
    out, hs = {}, [(m.start(), m.group(1))
                   for m in re.finditer(r"^#+\s+(\d+(?:\.\d+)?)", t, re.M)]
    for i, (pos, num) in enumerate(hs):
        end = hs[i + 1][0] if i + 1 < len(hs) else len(t)
        out[num] = t[pos:end]
    return out


def anchors(s):
    """Language-invariant content anchors inside a block of prose."""
    return {"inline_math": len(re.findall(r"\\\((.+?)\\\)", s, re.S)),
            "displays": len(re.findall(r"\\\[(.+?)\\\]", s, re.S)),
            "citations": len(re.findall(r"\[\d+(?:\s*,\s*\d+)*\]", s)),
            "code": len(re.findall(r"`[^`]+`", s)),
            "eq_tags": len(re.findall(r"\\tag\{[^}]*\}", s))}


def main():
    a, b = rd(EN), rd(ES)
    res = {}

    print("=== 1. displayed formulas: difference confined to \\text{...} operands?")
    da, db = displays(a), displays(b)
    n_diff = sum(1 for x, y in zip(da, db) if x != y)
    sa = [strip_text_ops(x) for x in da]
    sb = [strip_text_ops(y) for y in db]
    resid = [(i, da[i], db[i]) for i in range(min(len(sa), len(sb))) if sa[i] != sb[i]]
    res["displays"] = {"count_en": len(da), "count_es": len(db),
                       "raw_positional_differences": n_diff,
                       "differences_after_masking_text_operands": len(resid),
                       "residual": [{"index": i, "en": x[:200], "es": y[:200]}
                                    for i, x, y in resid[:20]]}
    print(f"  formulas: EN={len(da)} ES={len(db)}")
    print(f"  positional differences raw          : {n_diff}")
    print(f"  positional differences after masking: {len(resid)}")
    for i, x, y in resid[:20]:
        print(f"    [{i}] EN {x[:150]}")
        print(f"         ES {y[:150]}")
    res["displays"]["verdict"] = ("TRANSLATION_ONLY" if not resid
                                 else "RESIDUAL_MATHEMATICAL_DIFFERENCE")
    print(f"  VERDICT: {res['displays']['verdict']}")

    print("\n=== 2. table rows: difference confined to digit-group separators?")

    def rows(t, es):
        out = []
        for line in t.splitlines():
            s = line.strip()
            if s.startswith("|") and s.endswith("|") and not re.fullmatch(r"\|[\s:|-]+\|", s):
                inv = re.findall(r"`[^`]+`|\b\d+(?:[.,]\d+)*\b|[0-9a-f]{16,}", s)
                if inv:
                    # canonicalise thousands separators away
                    out.append("|".join(re.sub(r"(?<=\d)[.,](?=\d{3}\b)", "", x)
                                        for x in inv))
        return sorted(out)

    ra, rb = rows(a, False), rows(b, True)
    res["table_rows"] = {"en": len(ra), "es": len(rb),
                         "equal_after_separator_canonicalisation": ra == rb,
                         "only_en": [x for x in ra if x not in rb][:10],
                         "only_es": [x for x in rb if x not in ra][:10]}
    print(f"  rows EN={len(ra)} ES={len(rb)} equal_after_canonicalisation={ra == rb}")
    if ra != rb:
        print(f"    only EN: {res['table_rows']['only_en']}")
        print(f"    only ES: {res['table_rows']['only_es']}")
    res["table_rows"]["verdict"] = ("LOCALISATION_ONLY" if ra == rb
                                    else "RESIDUAL_TABLE_DIFFERENCE")
    print(f"  VERDICT: {res['table_rows']['verdict']}")

    print("\n=== 3. paragraph-count mismatches: split/merge or content change?")
    sa_, sb_ = sections(a), sections(b)
    flagged = []
    for k in sorted(set(sa_) | set(sb_)):
        x, y = sa_.get(k, ""), sb_.get(k, "")
        pa = len([p for p in re.split(r"\n\s*\n", x) if len(p.strip()) > 120])
        pb = len([p for p in re.split(r"\n\s*\n", y) if len(p.strip()) > 120])
        if pa != pb:
            ax, ay = anchors(x), anchors(y)
            same = ax == ay
            flagged.append({"section": k, "en_paras": pa, "es_paras": pb,
                            "en_anchors": ax, "es_anchors": ay,
                            "anchors_identical": same,
                            "en_chars": len(re.sub(r"\s+", " ", x)),
                            "es_chars": len(re.sub(r"\s+", " ", y))})
    print(f"  {'sec':>6} {'EN':>3} {'ES':>3}  anchors_identical  en_chars es_chars  ratio")
    for f in flagged:
        r = f["es_chars"] / max(1, f["en_chars"])
        print(f"  {f['section']:>6} {f['en_paras']:>3} {f['es_paras']:>3}  "
              f"{str(f['anchors_identical']):>17}  {f['en_chars']:>8} {f['es_chars']:>8}"
              f"  {r:5.2f}")
        if not f["anchors_identical"]:
            for kk in f["en_anchors"]:
                if f["en_anchors"][kk] != f["es_anchors"][kk]:
                    print(f"           anchor '{kk}': EN={f['en_anchors'][kk]} "
                          f"ES={f['es_anchors'][kk]}")
    bad = [f for f in flagged if not f["anchors_identical"]]
    res["paragraphs"] = {"flagged_sections": flagged,
                         "sections_with_anchor_mismatch": [f["section"] for f in bad],
                         "verdict": ("PARAGRAPH_BREAK_ONLY" if not bad
                                     else "ANCHOR_MISMATCH_REQUIRES_INSPECTION")}
    print(f"  VERDICT: {res['paragraphs']['verdict']}")

    json.dump(res, open(OUT, "w", encoding="utf-8"), indent=1, ensure_ascii=False)
    print(f"\n-> {OUT}")


if __name__ == "__main__":
    main()
