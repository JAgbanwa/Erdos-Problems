#!/usr/bin/env python3
"""E5 (part 1) - bilingual loss/duplication on the v1.5 pair, and N02/N03 propagation
through Markdown -> TeX -> PDF in both languages.

The comparator is the one written for the v1.4 challenger run, carried forward deliberately:
it was validated there, and reusing it makes the v1.4/v1.5 results directly comparable. The
three known benign classes -- translated \\text{...} operands, Spanish digit-group separators,
and paragraph-threshold effects -- are adjudicated automatically rather than reported raw.
"""
import collections
import hashlib
import io
import json
import os
import re
import subprocess
import sys

sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding="utf-8", errors="replace")

M = "C:/p3v15/01_manuscript"
EN_MD, ES_MD = f"{M}/PAPER_III_preprint_v1.5.md", f"{M}/PAPER_III_preprint_v1.5_es.md"
OUT = "C:/v15r/20_EVIDENCE/E5_BILINGUAL"

# The five clarification strings that must reach every layer, per language.
CLARIF = {
    # The inline math \(D\) renders to an astral-plane mathematical-italic glyph that
    # pdftotext (Xpdf 4.00) emits as a run of replacement characters, so the gap between
    # "subdigraph of" and "kernel-perfect" must be generously bounded in the PDF layer.
    "EN": {"N02_simple": r"simple bipartite graph with maximum degree",
           "N03_kernel": r"induced subdigraph of .{0,60}?and hence is kernel-perfect",
           "N03_induction": r"bipartite graphs of maximum degree at most",
           "N03_deg_two": r"maximum degree at most two",
           "N03_simple_path": r"well-defined simple path"},
    "ES": {"N02_simple": r"grafo bipartito simple de grado m[aá]ximo",
           "N03_kernel": r"subdigrafo inducido de .{0,60}?y, por tanto, es kernel-perfect",
           "N03_induction": r"grafos bipartitos de grado m[aá]ximo a lo sumo",
           "N03_deg_two": r"grado m[aá]ximo a lo sumo dos",
           "N03_simple_path": r"camino simple bien definido"},
}
LAYERS = {"EN": {"md": EN_MD, "tex": f"{M}/PAPER_III_preprint_v1.5_en.tex",
                 "pdf": f"{M}/PAPER_III_preprint_v1.5_en.pdf"},
          "ES": {"md": ES_MD, "tex": f"{M}/PAPER_III_preprint_v1.5_es.tex",
                 "pdf": f"{M}/PAPER_III_preprint_v1.5_es.pdf"}}


def rd(p):
    return open(p, encoding="utf-8", errors="replace").read()


def pdftext(p):
    r = subprocess.run(["pdftotext", "-enc", "UTF-8", p, "-"], capture_output=True)
    return r.stdout.decode("utf-8", "replace")


def norm(s):
    return re.sub(r"\s+", " ", s)


def strip_text_ops(s):
    for cmd in ("text", "textrm", "textit", "textbf", "mbox", "operatorname", "mathrm"):
        s = re.sub(r"\\" + cmd + r"\{[^{}]*\}", "\\\\" + cmd + "{@}", s)
    return s


def displays(t):
    return [re.sub(r"\s+", "", x) for x in re.findall(r"\\\[(.+?)\\\]", t, re.S)]


def headings(t):
    return [(len(m.group(1)), norm(m.group(2)).strip())
            for m in re.finditer(r"^(#{1,6})\s+(.+?)\s*$", t, re.M)]


def tags(t):
    return collections.Counter(re.findall(r"\\tag\{([^}]*)\}", t))


def cites(t):
    c = collections.Counter()
    for m in re.finditer(r"\[(\d+(?:\s*,\s*\d+)*)\]", t):
        for x in m.group(1).split(","):
            c[x.strip()] += 1
    return c


def lean_ids(t):
    return collections.Counter(
        re.findall(r"`([A-Z][A-Za-z0-9_]*(?:\.[A-Za-z0-9_']+)+)`", t))


def table_rows(t):
    out = collections.Counter()
    for line in t.splitlines():
        s = line.strip()
        if s.startswith("|") and s.endswith("|") and not re.fullmatch(r"\|[\s:|-]+\|", s):
            inv = re.findall(r"`[^`]+`|\b\d+(?:[.,]\d+)*\b|[0-9a-f]{16,}", s)
            if inv:
                out["|".join(re.sub(r"(?<=\d)[.,](?=\d{3}\b)", "", x) for x in inv)] += 1
    return out


def list_items(t):
    return len([l for l in t.splitlines() if re.match(r"^\s*(?:[-*+]|\d+\.)\s+\S", l)])


def theorem_blocks(t):
    return [norm(m.group(1)).strip() for m in re.finditer(
        r"^#{2,6}\s+((?:Theorem|Lemma|Proposition|Corollary|Remark|Claim|Teorema|Lema|"
        r"Proposici[oó]n|Corolario|Observaci[oó]n|Afirmaci[oó]n)[^\n]*)$", t, re.M)]


def sections(t):
    out, hs = {}, [(m.start(), m.group(1))
                   for m in re.finditer(r"^#+\s+(\d+(?:\.\d+)?)", t, re.M)]
    for i, (pos, num) in enumerate(hs):
        end = hs[i + 1][0] if i + 1 < len(hs) else len(t)
        out[num] = t[pos:end]
    return out


def anchors(s):
    return {"inline_math": len(re.findall(r"\\\((.+?)\\\)", s, re.S)),
            "displays": len(re.findall(r"\\\[(.+?)\\\]", s, re.S)),
            "citations": len(re.findall(r"\[\d+(?:\s*,\s*\d+)*\]", s)),
            "code": len(re.findall(r"`[^`]+`", s)),
            "tags": len(re.findall(r"\\tag\{[^}]*\}", s))}


def cmp_counter(a, b, label, res):
    lost = {k: a[k] - b.get(k, 0) for k in a if a[k] > b.get(k, 0)}
    extra = {k: b[k] - a.get(k, 0) for k in b if b[k] > a.get(k, 0)}
    res[label] = {"en": len(a), "es": len(b), "missing_in_es": lost,
                  "extra_in_es": extra, "ok": not lost and not extra}
    print(f"  {label:20} EN={len(a):<5} ES={len(b):<5} "
          f"{'OK' if not lost and not extra else 'DIFF'}")
    if lost:
        print(f"      missing in ES: {dict(list(lost.items())[:8])}")
    if extra:
        print(f"      extra in ES  : {dict(list(extra.items())[:8])}")
    return not lost and not extra


def main():
    os.makedirs(OUT, exist_ok=True)
    a, b = rd(EN_MD), rd(ES_MD)
    res = {"en_sha256": hashlib.sha256(a.encode()).hexdigest(),
           "es_sha256": hashlib.sha256(b.encode()).hexdigest(),
           "structural": {}}
    print(f"EN {len(a.encode()):,} bytes   ES {len(b.encode()):,} bytes\n")
    print("=== E5.1 structural loss / duplication, EN vs ES (v1.5)")

    ok = {}
    ha, hb = headings(a), headings(b)
    ok["headings"] = [x[0] for x in ha] == [x[0] for x in hb] and len(ha) == len(hb)
    print(f"  {'headings':20} EN={len(ha):<5} ES={len(hb):<5} "
          f"{'OK' if ok['headings'] else 'DIFF'}")

    # Theorem blocks are counted positionally over the aligned heading sequence, not by
    # leading keyword. Counting by keyword gave EN=34 ES=36 purely from Spanish word order:
    # "Packing-form corollaries" / "Corolarios en forma de empaquetamiento" and
    # "Algorithmic remark 12.3" / "Observacion algoritmica 12.3" are the same headings in the
    # same positions, but only the Spanish ones begin with a theorem word.
    ta, tb = theorem_blocks(a), theorem_blocks(b)
    kw_en = re.compile(r"(Theorem|Lemma|Proposition|Corollary|Remark|Claim)\b")
    kw_es = re.compile(r"(Teorema|Lema|Proposici[oó]n|Corolario|Observaci[oó]n|"
                       r"Afirmaci[oó]n)")
    disagree = [(i, x, y) for i, (x, y) in enumerate(zip([h[1] for h in ha],
                                                         [h[1] for h in hb]))
                if bool(kw_en.match(x)) != bool(kw_es.match(y))]
    ok["theorem_blocks"] = len(ha) == len(hb) and len(ta) - len(tb) == -len(disagree)
    print(f"  {'theorem blocks':20} EN={len(ta):<5} ES={len(tb):<5} "
          f"keyword-classification disagreements={len(disagree)} "
          f"(word order only) {'OK' if ok['theorem_blocks'] else 'DIFF'}")
    for i, x, y in disagree:
        print(f"      heading {i}: EN=\"{x[:52]}\"  ES=\"{y[:52]}\"")
    res["structural"]["theorem_blocks"] = {
        "en_keyword_count": len(ta), "es_keyword_count": len(tb),
        "heading_positions_aligned": len(ha) == len(hb),
        "keyword_disagreements": [{"index": i, "en": x, "es": y}
                                  for i, x, y in disagree],
        "note": "same headings, same positions; Spanish word order puts the theorem word "
                "first where English does not"}

    da, db = displays(a), displays(b)
    raw = sum(1 for x, y in zip(da, db) if x != y)
    resid = [(i, da[i], db[i]) for i in range(min(len(da), len(db)))
             if strip_text_ops(da[i]) != strip_text_ops(db[i])]
    ok["displays"] = len(da) == len(db) and not resid
    print(f"  {'displays':20} EN={len(da):<5} ES={len(db):<5} "
          f"raw diffs={raw} after masking \\text{{}}={len(resid)} "
          f"{'OK' if ok['displays'] else 'DIFF'}")
    for i, x, y in resid[:8]:
        print(f"      [{i}] EN {x[:120]}\n           ES {y[:120]}")
    res["structural"]["displays"] = {"count_en": len(da), "count_es": len(db),
                                     "raw_positional_diffs": raw,
                                     "residual_after_masking": len(resid),
                                     "residual": [{"i": i, "en": x[:200], "es": y[:200]}
                                                  for i, x, y in resid[:10]]}

    ok["equation_tags"] = cmp_counter(tags(a), tags(b), "equation tags",
                                      res["structural"])
    ok["citations"] = cmp_counter(cites(a), cites(b), "citations", res["structural"])
    ok["lean_identifiers"] = cmp_counter(lean_ids(a), lean_ids(b), "lean identifiers",
                                         res["structural"])
    ok["table_rows"] = cmp_counter(table_rows(a), table_rows(b), "table rows",
                                   res["structural"])
    la_, lb_ = list_items(a), list_items(b)
    ok["list_items"] = la_ == lb_
    print(f"  {'list items':20} EN={la_:<5} ES={lb_:<5} "
          f"{'OK' if ok['list_items'] else 'DIFF'}")

    sa, sb = sections(a), sections(b)
    mism = []
    for k in sorted(set(sa) | set(sb)):
        x, y = sa.get(k, ""), sb.get(k, "")
        pa = len([p for p in re.split(r"\n\s*\n", x) if len(p.strip()) > 120])
        pb = len([p for p in re.split(r"\n\s*\n", y) if len(p.strip()) > 120])
        if pa != pb:
            ax, ay = anchors(x), anchors(y)
            ratio = len(norm(y)) / max(1, len(norm(x)))
            mism.append({"section": k, "en_paras": pa, "es_paras": pb,
                         "anchors_identical": ax == ay, "length_ratio": round(ratio, 3),
                         "benign": ax == ay or 0.9 <= ratio <= 1.25})
    hard = [m for m in mism if not m["benign"]]
    ok["paragraphs"] = not hard
    print(f"  {'long paragraphs':20} sections flagged={len(mism)} "
          f"not-benign={len(hard)} {'OK' if not hard else 'DIFF'}")
    for m in mism:
        print(f"      sec {m['section']:>5}: EN={m['en_paras']} ES={m['es_paras']} "
              f"anchors_identical={m['anchors_identical']} ratio={m['length_ratio']} "
              f"{'benign' if m['benign'] else 'NEEDS REVIEW'}")
    res["structural"]["paragraphs"] = {"flagged": mism, "not_benign": hard}

    res["structural_pass"] = all(ok.values())
    print(f"\n  structural checks failing: "
          f"{[k for k, v in ok.items() if not v] or 'none'}")
    print(f"  --> E5.1 {'PASS' if all(ok.values()) else 'FAIL'}")

    print("\n=== E5.2 N02/N03 propagation through md -> tex -> pdf, both languages")
    prop = {}
    for lang, layers in LAYERS.items():
        prop[lang] = {}
        txt = {"md": rd(layers["md"]), "tex": rd(layers["tex"]),
               "pdf": pdftext(layers["pdf"])}
        for cname, pat in CLARIF[lang].items():
            row = {}
            for layer, t in txt.items():
                # LaTeX escapes and pandoc line-wrapping: compare on whitespace-normalised
                # text with LaTeX escape artifacts neutralised
                probe = norm(t).replace("\\_", "_").replace("{[}", "[").replace("{]}", "]")
                probe = re.sub(r"\\allowbreak\{\}", "", probe)
                row[layer] = bool(re.search(pat, probe, re.I))
            prop[lang][cname] = row
            print(f"  {lang} {cname:16} md={'y' if row['md'] else 'N'} "
                  f"tex={'y' if row['tex'] else 'N'} pdf={'y' if row['pdf'] else 'N'}")
    res["propagation"] = prop
    res["propagation_pass"] = all(v for l in prop.values() for r in l.values()
                                  for v in r.values())
    print(f"  --> E5.2 {'PASS' if res['propagation_pass'] else 'FAIL'}")

    res["E5_bilingual_pass"] = res["structural_pass"] and res["propagation_pass"]
    print(f"\nE5 (bilingual + propagation) "
          f"{'PASS' if res['E5_bilingual_pass'] else 'FAIL'}")
    with open(f"{OUT}/E5_bilingual.json", "w", encoding="utf-8", newline="\n") as f:
        json.dump(res, f, indent=1, ensure_ascii=False)
        f.write("\n")


if __name__ == "__main__":
    main()
