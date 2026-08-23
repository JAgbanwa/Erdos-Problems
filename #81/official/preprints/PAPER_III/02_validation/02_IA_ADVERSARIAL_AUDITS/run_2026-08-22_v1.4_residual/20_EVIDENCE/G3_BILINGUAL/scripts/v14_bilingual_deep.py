#!/usr/bin/env python3
"""Paper III v1.4, gate 3 -- deep EN/ES comparison of the MD/TeX/PDF chains.

Counting totals cannot detect a paragraph that was lost in one place and duplicated in
another: the totals stay equal. So this aligns the two manuscripts BLOCK BY BLOCK on their
heading structure and compares, inside each aligned block:

  display formulas, inline formulas, table rows, bracketed citations, Lean identifiers,
  equation tags, and paragraph count

and separately looks for duplicated and reordered content inside each language.
"""
import json
import re
from collections import Counter

T = "C:/p3v14/01_manuscript"
OUT = "C:/erdos_audit/v14/E5/bilingual_deep.json"
DOCS = {
    "EN": (f"{T}/PAPER_III_preprint_draft_v1.4.md",
           f"{T}/PAPER_III_preprint_draft_v1.4_en.tex"),
    "ES": (f"{T}/PAPER_III_preprint_draft_v1.4_es.md",
           f"{T}/PAPER_III_preprint_draft_v1.4_es.tex"),
}


def rd(p):
    return open(p, encoding="utf-8", errors="replace").read()


def blocks(t):
    """Split into (level, title, body) at every heading."""
    hs = [(m.start(), len(m.group(1)), m.group(2).strip())
          for m in re.finditer(r"^(#{1,6})\s+(.+)$", t, re.M)]
    out = []
    for i, (pos, lvl, title) in enumerate(hs):
        end = hs[i + 1][0] if i + 1 < len(hs) else len(t)
        out.append({"level": lvl, "title": title, "body": t[pos:end]})
    return out


def features(b):
    return {
        "display_math": len(re.findall(r"\\\[", b)),
        "inline_math": len(re.findall(r"\\\(", b)),
        "table_rows": len([l for l in b.split("\n")
                           if l.strip().startswith("|") and set(l.strip()) != set("|- ")]),
        "citations": len(re.findall(r"\[\d+(?:\s*[,;]\s*\d+)*\]", b)),
        "lean_names": len(re.findall(r"`[A-Za-z][A-Za-z0-9_.]*\.[A-Za-z0-9_.]+`", b)),
        "eq_tags": len(re.findall(r"\\tag\{", b)),
        "paragraphs": len([x for x in re.split(r"\n\s*\n", b) if x.strip()]),
        "boxed": len(re.findall(r"\\boxed", b)),
    }


def norm_para(x):
    """Normalize a paragraph for duplicate detection."""
    x = re.sub(r"\s+", " ", x).strip()
    return x


def main():
    res = {"gate": "3", "check": "deep EN/ES block alignment plus duplication/reordering"}
    en, es = rd(DOCS["EN"][0]), rd(DOCS["ES"][0])
    ent, est = rd(DOCS["EN"][1]), rd(DOCS["ES"][1])
    be, bs = blocks(en), blocks(es)

    res["block_counts"] = {"EN": len(be), "ES": len(bs), "equal": len(be) == len(bs)}
    res["level_sequence_identical"] = [b["level"] for b in be] == [b["level"] for b in bs]

    # aligned per-block feature comparison
    diffs = []
    if len(be) == len(bs):
        for i, (x, y) in enumerate(zip(be, bs)):
            fx, fy = features(x["body"]), features(y["body"])
            d = {k: (fx[k], fy[k]) for k in fx if fx[k] != fy[k]}
            if d:
                diffs.append({"block": i, "EN_title": x["title"][:70],
                              "ES_title": y["title"][:70], "differences": d})
    res["per_block_differences"] = diffs
    res["blocks_with_differences"] = len(diffs)

    # duplicated paragraphs inside each language
    dup = {}
    for lang, t in (("EN", en), ("ES", es)):
        paras = [norm_para(x) for x in re.split(r"\n\s*\n", t)
                 if len(norm_para(x)) > 120 and not norm_para(x).startswith("#")]
        c = Counter(paras)
        dup[lang] = [{"count": n, "text": p[:160]} for p, n in c.items() if n > 1]
    res["duplicated_paragraphs"] = dup

    # reordering: the sequence of equation tags and theorem numbers must match in order
    def seq_tags(t):
        return re.findall(r"\\tag\{([^}]+)\}", t)

    def seq_thms(t):
        return re.findall(
            r"(?:Theorem|Teorema|Lemma|Lema|Corollary|Corolario|Proposition|"
            r"Proposici[oó]n)\s+(\d+\.\d+[a-z]?)", t)
    res["ordering"] = {
        "eq_tag_sequence_identical": seq_tags(en) == seq_tags(es),
        "eq_tags_EN": len(seq_tags(en)), "eq_tags_ES": len(seq_tags(es)),
        "theorem_sequence_identical": seq_thms(en) == seq_thms(es),
        "first_divergence_tag": next((i for i, (a, b) in
                                      enumerate(zip(seq_tags(en), seq_tags(es))) if a != b),
                                     None),
        "first_divergence_thm": next((i for i, (a, b) in
                                      enumerate(zip(seq_thms(en), seq_thms(es))) if a != b),
                                     None)}

    # MD -> TeX faithfulness per language, accounting for escaped underscores
    md_tex = {}
    for lang, (md, tex) in DOCS.items():
        m, x = rd(md), rd(tex)
        ids = sorted(set(re.findall(r"`([A-Za-z][A-Za-z0-9_.]*\.[A-Za-z0-9_.]+)`", m)))
        tags = sorted(set(re.findall(r"\\tag\{([^}]+)\}", m)))
        thms = sorted(set(re.findall(
            r"(?:Theorem|Teorema|Lemma|Lema|Corollary|Corolario|Proposition|"
            r"Proposici[oó]n)\s+(\d+\.\d+[a-z]?)", m)))
        md_tex[lang] = {
            "identifiers": len(ids),
            "identifiers_in_tex": sum(1 for i in ids
                                      if i in x or i.replace("_", r"\_") in x),
            "eq_tags": len(tags), "eq_tags_in_tex": sum(1 for t in tags if t in x),
            "theorems": len(thms), "theorems_in_tex": sum(1 for t in thms if t in x)}
    res["md_to_tex"] = md_tex

    json.dump(res, open(OUT, "w", encoding="utf-8"), indent=1, ensure_ascii=False)

    print(f"bloques: EN {res['block_counts']['EN']} / ES {res['block_counts']['ES']}  "
          f"iguales={res['block_counts']['equal']}  "
          f"secuencia de niveles identica={res['level_sequence_identical']}")
    print(f"\nbloques con diferencias de contenido: {res['blocks_with_differences']}")
    for d in diffs[:14]:
        print(f"  [{d['block']:>3}] {d['EN_title'][:52]:52} {d['differences']}")
    print(f"\nparrafos duplicados: EN {len(dup['EN'])}  ES {len(dup['ES'])}")
    for lang in ("EN", "ES"):
        for x in dup[lang][:4]:
            print(f"  {lang} x{x['count']}: {x['text'][:120]}")
    o = res["ordering"]
    print(f"\norden de etiquetas identico: {o['eq_tag_sequence_identical']} "
          f"({o['eq_tags_EN']}/{o['eq_tags_ES']})   "
          f"primera divergencia: {o['first_divergence_tag']}")
    print(f"orden de teoremas identico : {o['theorem_sequence_identical']}   "
          f"primera divergencia: {o['first_divergence_thm']}")
    print("\nMD -> TeX por idioma:")
    for lang, v in md_tex.items():
        print(f"  {lang}: identificadores {v['identifiers_in_tex']}/{v['identifiers']}  "
              f"etiquetas {v['eq_tags_in_tex']}/{v['eq_tags']}  "
              f"teoremas {v['theorems_in_tex']}/{v['theorems']}")


if __name__ == "__main__":
    main()
