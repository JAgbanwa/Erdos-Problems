#!/usr/bin/env python3
"""Paper III v1.3 -- textual items of the mandatory regression matrix, plus E5 EN/ES.

Regression items decided here:
  - overbroad "resolves the split case" wording
  - A_{2,J} / A_{2J} inconsistency
  - combined-citation divergence, specifically [3,8] and [11,17]
  - the corrected split-case scope
  - stale version/axiom labels in the publication artifacts
  - EN/ES structural agreement: headings, equation tags, numbered references,
    theorem numbering, formal identifiers
"""
import json
import re
import unicodedata

T = "C:/p3v13/01_manuscript"
EN_MD = f"{T}/PAPER_III_preprint_draft_v1.3.md"
ES_MD = f"{T}/PAPER_III_preprint_draft_v1.3_es.md"
EN_TEX = f"{T}/PAPER_III_preprint_draft_v1.3_en.tex"
ES_TEX = f"{T}/PAPER_III_preprint_draft_v1.3_es.tex"
OUT = "C:/erdos_audit/v13/E5/regression_text.json"


def rd(p):
    return open(p, encoding="utf-8", errors="replace").read()


def main():
    en, es = rd(EN_MD), rd(ES_MD)
    ent, est = rd(EN_TEX), rd(ES_TEX)
    r = {}

    # --- overbroad scope wording
    OVER = [r"resolv\w*[^.]{0,80}split case", r"solv\w*[^.]{0,80}split case",
            r"settl\w*[^.]{0,80}split case", r"resuelv\w*[^.]{0,80}caso split",
            r"resolv\w*[^.]{0,60}(Erd[oő]s|Problem\s*#?\s*81)",
            r"(resuelve|resolvemos)[^.]{0,60}(Erd[oő]s|Problema\s*#?\s*81)"]
    r["overbroad_scope"] = {
        "EN": [m.group(0)[:140] for p in OVER for m in re.finditer(p, en, re.I)],
        "ES": [m.group(0)[:140] for p in OVER for m in re.finditer(p, es, re.I)]}

    # --- the corrected scope must be present and explicit
    KEEP = {"chordal remains open": r"chordal[^.]{0,80}remains open",
            "cordal sigue abierto": r"cordal[^.]{0,90}(abierto|abierta)",
            "sharp quadratic 1/6": r"sharp[^.]{0,40}(1/6|\\frac\{1\}\{6\})",
            "coeficiente agudo 1/6": r"(agudo|exacto)[^.]{0,40}(1/6|\\frac\{1\}\{6\})",
            "least uniform linear undetermined": r"(undetermined|not determined)[^.]{0,60}linear",
            "lineal no determinado": r"(no determinad\w+|indeterminad\w+)[^.]{0,60}lineal"}
    r["corrected_scope_present"] = {
        k: {"EN": len(re.findall(p, en, re.I)), "ES": len(re.findall(p, es, re.I))}
        for k, p in KEEP.items()}

    # --- A_{2,J} vs A_{2J}
    r["A2J"] = {}
    for name, txt in (("EN_md", en), ("ES_md", es), ("EN_tex", ent), ("ES_tex", est)):
        r["A2J"][name] = {
            "A_{2,J}": len(re.findall(r"A_\{2,\s*J\}", txt)),
            "A_{2J}": len(re.findall(r"A_\{2J\}", txt)),
            "A_{2,j}": len(re.findall(r"A_\{2,\s*j\}", txt)),
            "other_A2": sorted(set(re.findall(r"A_\{2[^}]{0,6}\}", txt)))}

    # --- combined citations
    def cites(txt):
        return sorted(set(re.findall(r"\[(\d+(?:\s*[,;]\s*\d+)+)\]", txt)))
    r["combined_citations"] = {
        "EN": cites(en), "ES": cites(es),
        "EN_only": sorted(set(cites(en)) - set(cites(es))),
        "ES_only": sorted(set(cites(es)) - set(cites(en))),
        "3_8_EN": len(re.findall(r"\[3\s*,\s*8\]", en)),
        "3_8_ES": len(re.findall(r"\[3\s*,\s*8\]", es)),
        "11_17_EN": len(re.findall(r"\[11\s*,\s*17\]", en)),
        "11_17_ES": len(re.findall(r"\[11\s*,\s*17\]", es))}

    # --- structural EN/ES agreement
    def heads(txt):
        return [h.strip() for h in re.findall(r"^(#{1,6})\s", txt, re.M)]
    def tags(txt):
        return sorted(re.findall(r"\\tag\{([^}]+)\}", txt))
    def refs(txt):
        return sorted(set(re.findall(r"^\s*\[(\d+)\]", txt, re.M)), key=int)
    def thms(txt):
        return sorted(set(re.findall(
            r"(?:Theorem|Teorema|Lemma|Lema|Corollary|Corolario|Proposition|"
            r"Proposici[oó]n)\s+(\d+\.\d+[a-z]?)", txt)))
    def idents(txt):
        return sorted(set(re.findall(r"`([A-Za-z][A-Za-z0-9_.]*\.[A-Za-z0-9_.]+)`", txt)))

    r["structure"] = {
        "headings": {"EN": len(heads(en)), "ES": len(heads(es)),
                     "level_sequence_identical": heads(en) == heads(es)},
        "equation_tags": {"EN": len(tags(en)), "ES": len(tags(es)),
                          "identical": tags(en) == tags(es),
                          "EN_only": sorted(set(tags(en)) - set(tags(es))),
                          "ES_only": sorted(set(tags(es)) - set(tags(en)))},
        "numbered_refs": {"EN": len(refs(en)), "ES": len(refs(es)),
                          "identical": refs(en) == refs(es)},
        "theorem_numbers": {"EN": thms(en), "ES": thms(es),
                            "identical": thms(en) == thms(es),
                            "EN_only": sorted(set(thms(en)) - set(thms(es))),
                            "ES_only": sorted(set(thms(es)) - set(thms(en)))},
        "formal_identifiers": {"EN": len(idents(en)), "ES": len(idents(es)),
                               "EN_only": sorted(set(idents(en)) - set(idents(es))),
                               "ES_only": sorted(set(idents(es)) - set(idents(en)))}}

    # --- stale labels inside the publication artifacts only
    r["stale_labels_in_artifacts"] = {}
    for name, txt in (("EN_md", en), ("ES_md", es), ("EN_tex", ent), ("ES_tex", est)):
        r["stale_labels_in_artifacts"][name] = {
            lab: len(re.findall(re.escape(lab), txt))
            for lab in ("v1.2", "v1.1", "v1_2", "lean_v1.2", "draft v1.0")}

    # --- release-status wording (E7)
    REL = {"first formal public release": r"first formal public release",
           "primera publicaci": r"primera (publicaci[oó]n|liberaci[oó]n)",
           "candidate": r"candidate", "candidata": r"candidat[oa]",
           "unpublished": r"unpublished", "no publicad": r"no publicad",
           "preprint": r"preprint", "draft": r"draft"}
    r["release_status"] = {k: {"EN": len(re.findall(p, en, re.I)),
                               "ES": len(re.findall(p, es, re.I))}
                           for k, p in REL.items()}

    json.dump(r, open(OUT, "w"), indent=1, ensure_ascii=False)

    # ---- print
    print("== alcance sobreamplio ('resuelve el caso split')")
    print(f"   EN: {len(r['overbroad_scope']['EN'])} coincidencias")
    for x in r["overbroad_scope"]["EN"][:4]:
        print(f"      {x}")
    print(f"   ES: {len(r['overbroad_scope']['ES'])} coincidencias")
    for x in r["overbroad_scope"]["ES"][:4]:
        print(f"      {x}")
    print("\n== alcance corregido presente")
    for k, v in r["corrected_scope_present"].items():
        print(f"   {k:38} EN {v['EN']}  ES {v['ES']}")
    print("\n== A_2J")
    for k, v in r["A2J"].items():
        print(f"   {k:8} A_{{2,J}}={v['A_{2,J}']}  A_{{2J}}={v['A_{2J}']}  "
              f"variantes={v['other_A2']}")
    c = r["combined_citations"]
    print(f"\n== citas combinadas: EN {len(c['EN'])} formas, ES {len(c['ES'])}")
    print(f"   solo EN: {c['EN_only']}")
    print(f"   solo ES: {c['ES_only']}")
    print(f"   [3,8]: EN {c['3_8_EN']} / ES {c['3_8_ES']}   "
          f"[11,17]: EN {c['11_17_EN']} / ES {c['11_17_ES']}")
    s = r["structure"]
    print("\n== estructura EN/ES")
    print(f"   encabezados      EN {s['headings']['EN']} / ES {s['headings']['ES']}  "
          f"secuencia identica: {s['headings']['level_sequence_identical']}")
    print(f"   etiquetas de ec. EN {s['equation_tags']['EN']} / "
          f"ES {s['equation_tags']['ES']}  identicas: {s['equation_tags']['identical']}")
    if s["equation_tags"]["EN_only"] or s["equation_tags"]["ES_only"]:
        print(f"      solo EN {s['equation_tags']['EN_only'][:8]}")
        print(f"      solo ES {s['equation_tags']['ES_only'][:8]}")
    print(f"   referencias      EN {s['numbered_refs']['EN']} / "
          f"ES {s['numbered_refs']['ES']}  identicas: {s['numbered_refs']['identical']}")
    print(f"   teoremas         identicos: {s['theorem_numbers']['identical']}  "
          f"solo EN {s['theorem_numbers']['EN_only']}  "
          f"solo ES {s['theorem_numbers']['ES_only']}")
    print(f"   identificadores  EN {s['formal_identifiers']['EN']} / "
          f"ES {s['formal_identifiers']['ES']}")
    print(f"      solo EN {s['formal_identifiers']['EN_only'][:6]}")
    print(f"      solo ES {s['formal_identifiers']['ES_only'][:6]}")
    print("\n== etiquetas obsoletas en los artefactos de publicacion")
    for k, v in r["stale_labels_in_artifacts"].items():
        nz = {a: b for a, b in v.items() if b}
        print(f"   {k:8} {nz if nz else 'ninguna'}")
    print("\n== estado de publicacion")
    for k, v in r["release_status"].items():
        if v["EN"] or v["ES"]:
            print(f"   {k:32} EN {v['EN']}  ES {v['ES']}")


if __name__ == "__main__":
    main()
