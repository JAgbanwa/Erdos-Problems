#!/usr/bin/env python3
"""Independent bilingual loss/duplication check for Paper III v1.4 (challenger run).

Written from scratch rather than reusing the prior run's comparator, per the request's
"rerun or independently replace" clause. Structure that must be language-invariant is
compared element by element in document order: headings, displayed formulas, equation
tags, citation references, Lean identifiers, table rows, list items, and per-section
paragraph counts. Duplicates are reported separately from losses.
"""
import collections
import hashlib
import io
import json
import re
import sys

sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding="utf-8", errors="replace")

EN = "C:/p3v14/01_manuscript/PAPER_III_preprint_draft_v1.4.md"
ES = "C:/p3v14/01_manuscript/PAPER_III_preprint_draft_v1.4_es.md"
OUT = "C:/v14c/20_EVIDENCE/A_BILINGUAL/bilingual_structural_diff.json"


def rd(p):
    return open(p, encoding="utf-8", errors="replace").read()


def norm(s):
    return re.sub(r"\s+", "", s)


def headings(t):
    return [(len(m.group(1)), re.sub(r"\s+", " ", m.group(2)).strip())
            for m in re.finditer(r"^(#{1,6})\s+(.+?)\s*$", t, re.M)]


def displays(t):
    return [norm(x) for x in re.findall(r"\\\[(.+?)\\\]", t, re.S)]


def tags(t):
    """Equation tags such as (5.3) / (9.12) appearing in prose or \\tag{}."""
    return sorted(collections.Counter(
        re.findall(r"\\tag\{([^}]+)\}", t)
        + re.findall(r"\((\d+\.\d+[a-z]?)\)", t)).items())


def cites(t):
    out = []
    for m in re.finditer(r"\[(\d+(?:\s*,\s*\d+)*)\]", t):
        out += [x.strip() for x in m.group(1).split(",")]
    return collections.Counter(out)


def lean_ids(t):
    return collections.Counter(re.findall(r"`([A-Z][A-Za-z0-9_]*(?:\.[A-Za-z0-9_']+)+)`", t))


def table_rows(t):
    """Pipe-table data rows, keyed by their language-invariant cells (code spans,
    numbers, hashes) so translated prose cells do not create false differences."""
    out = []
    for line in t.splitlines():
        s = line.strip()
        if s.startswith("|") and s.endswith("|") and not re.fullmatch(r"\|[\s:|-]+\|", s):
            inv = re.findall(r"`[^`]+`|\b\d+(?:[.,]\d+)*\b|[0-9a-f]{16,}", s)
            if inv:
                out.append("|".join(inv))
    return collections.Counter(out)


def list_items(t):
    return len([l for l in t.splitlines()
                if re.match(r"^\s*(?:[-*+]|\d+\.)\s+\S", l)])


def sections(t):
    out, hs = {}, [(m.start(), m.group(1))
                   for m in re.finditer(r"^#+\s+(\d+(?:\.\d+)?)", t, re.M)]
    for i, (pos, num) in enumerate(hs):
        end = hs[i + 1][0] if i + 1 < len(hs) else len(t)
        out[num] = t[pos:end]
    return out


def cmp_counter(a, b, label, res):
    lost = {k: a[k] - b.get(k, 0) for k in a if a[k] > b.get(k, 0)}
    extra = {k: b[k] - a.get(k, 0) for k in b if b[k] > a.get(k, 0)}
    dup_en = {k: v for k, v in a.items() if v > 1}
    dup_es = {k: v for k, v in b.items() if v > 1}
    res[label] = {"en_distinct": len(a), "es_distinct": len(b),
                  "missing_in_es": lost, "extra_in_es": extra,
                  "repeated_en": dup_en, "repeated_es": dup_es,
                  "ok": not lost and not extra}
    print(f"  {label:18} EN={len(a):<5} ES={len(b):<5} "
          f"missing_in_es={len(lost)} extra_in_es={len(extra)} "
          f"{'OK' if not lost and not extra else 'DIFF'}")
    if lost:
        print(f"      missing: {dict(list(lost.items())[:12])}")
    if extra:
        print(f"      extra  : {dict(list(extra.items())[:12])}")


def main():
    a, b = rd(EN), rd(ES)
    res = {"en": {"path": EN, "sha256": hashlib.sha256(a.encode()).hexdigest(),
                  "bytes": len(a.encode())},
           "es": {"path": ES, "sha256": hashlib.sha256(b.encode()).hexdigest(),
                  "bytes": len(b.encode())}}
    print(f"EN {res['en']['bytes']:,} bytes   ES {res['es']['bytes']:,} bytes\n")

    ha, hb = headings(a), headings(b)
    res["headings"] = {"en": len(ha), "es": len(hb), "level_sequence_equal":
                       [x[0] for x in ha] == [x[0] for x in hb]}
    print(f"  headings           EN={len(ha)} ES={len(hb)} "
          f"level-sequence-equal={res['headings']['level_sequence_equal']}")
    if len(ha) != len(hb):
        res["headings"]["en_only_text"] = [x[1] for x in ha][:40]
        res["headings"]["es_only_text"] = [x[1] for x in hb][:40]

    da, db = displays(a), displays(b)
    seq_eq = da == db
    res["displayed_formulas"] = {"en": len(da), "es": len(db), "sequence_identical": seq_eq,
                                "only_en": [x[:110] for x in da if x not in db][:15],
                                "only_es": [x[:110] for x in db if x not in da][:15]}
    print(f"  displays           EN={len(da)} ES={len(db)} sequence_identical={seq_eq}")
    if not seq_eq:
        print(f"      only in EN: {res['displayed_formulas']['only_en']}")
        print(f"      only in ES: {res['displayed_formulas']['only_es']}")

    cmp_counter(collections.Counter(dict(tags(a))), collections.Counter(dict(tags(b))),
                "equation tags", res)
    cmp_counter(cites(a), cites(b), "citations", res)
    cmp_counter(lean_ids(a), lean_ids(b), "lean identifiers", res)
    cmp_counter(table_rows(a), table_rows(b), "table rows", res)

    la, lb = list_items(a), list_items(b)
    res["list_items"] = {"en": la, "es": lb, "equal": la == lb}
    print(f"  list items         EN={la} ES={lb} equal={la == lb}")

    sa, sb = sections(a), sections(b)
    bad = []
    for k in sorted(set(sa) | set(sb)):
        pa = len([p for p in re.split(r"\n\s*\n", sa.get(k, "")) if len(p.strip()) > 120])
        pb = len([p for p in re.split(r"\n\s*\n", sb.get(k, "")) if len(p.strip()) > 120])
        if pa != pb:
            bad.append({"section": k, "en_long_paragraphs": pa, "es_long_paragraphs": pb})
    res["long_paragraph_parity"] = {"sections_compared": len(set(sa) | set(sb)),
                                    "mismatches": bad, "ok": not bad}
    print(f"  long paragraphs    sections={len(set(sa) | set(sb))} mismatches={len(bad)}")
    for x in bad:
        print(f"      section {x['section']}: EN={x['en_long_paragraphs']} "
              f"ES={x['es_long_paragraphs']}")

    checks = {"headings_count": len(ha) == len(hb),
              "heading_levels": res["headings"]["level_sequence_equal"],
              "displays": seq_eq,
              "equation_tags": res["equation tags"]["ok"],
              "citations": res["citations"]["ok"],
              "lean_identifiers": res["lean identifiers"]["ok"],
              "table_rows": res["table rows"]["ok"],
              "list_items": la == lb,
              "long_paragraphs": not bad}
    res["verdict"] = {"checks": checks, "all_pass": all(checks.values())}
    print(f"\n  ALL STRUCTURAL CHECKS PASS: {all(checks.values())}")
    print(f"  failing: {[k for k, v in checks.items() if not v] or 'none'}")
    json.dump(res, open(OUT, "w", encoding="utf-8"), indent=1, ensure_ascii=False)
    print(f"\n  -> {OUT}")


if __name__ == "__main__":
    main()
