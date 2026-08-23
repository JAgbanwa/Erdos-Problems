#!/usr/bin/env python3
"""E1 - independent delta review, v1.4 -> v1.5, both languages.

Two separate obligations:
  (a) invariance: every displayed formula, equation tag, heading/theorem order and citation
      reference must be unchanged. Checked as ordered sequences, not multisets, so a
      reordering is caught as well as an addition or a loss.
  (b) containment: every changed line must fall inside the declared delta set. Each changed
      hunk is classified; anything unclassified is reported as an undeclared change.
"""
import collections
import difflib
import hashlib
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

PAIRS = {
    "EN_md": (f"{OLD}/PAPER_III_preprint_draft_v1.4.md",
              f"{NEW}/PAPER_III_preprint_v1.5.md"),
    "ES_md": (f"{OLD}/PAPER_III_preprint_draft_v1.4_es.md",
              f"{NEW}/PAPER_III_preprint_v1.5_es.md"),
}

# Declared delta set of Section 4 of the request, as classifiers on changed text.
CLASSIFIERS = [
    ("N02_simple_bipartite",
     r"simple bipartite|bipartito simple"),
    # note: the Spanish text keeps "kernel-perfect" as a term of art rather than translating it
    ("N03_kernel_perfect_induced",
     r"induced subdigraph|kernel-perfect|subdigrafo inducido"),
    ("N03_bounded_degree_induction",
     r"maximum degree at most \\\(\\Delta\\\)|grado m[aá]ximo a lo (m[aá]s|sumo)"),
    ("N03_two_colour_simple_path",
     r"maximum degree at most two|well-defined simple path|grado m[aá]ximo a lo (m[aá]s|sumo) "
     r"dos|camino simple bien definido"),
    ("release_state_promotion",
     r"version 1\.5|versi[oó]n 1\.5|Release date|Fecha de publicaci|first formal public|"
     r"primer .*p[uú]blic|official author preprint|preprint oficial|Status:|Estado:|"
     r"Preprint:|externally AI-audited|auditado externamente|Review boundary|"
     r"L[ií]mite de la revisi|external ad(versarial|)|revisi[oó]n externa|"
     r"external audit|auditor[ií]a externa|public tag|etiqueta p[uú]blica|"
     r"repository level|nivel de repositorio|corpus-bounded|acotad. al corpus|"
     r"Prior-art and novelty status|Estado de anterioridad|peer review|revisi[oó]n por pares|"
     r"canonical repository package|paquete can[oó]nico del repositorio|"
     r"frozen Lean snapshots|instant[aá]neas Lean|audit boundary|frontera de auditor[ií]a|"
     r"frozen artifact|artefacto congelado|8,455|8\.455|8,444|8\.444|"
     r"Estado del arte previo|arte previo y novedad|repositorio can[oó]nico|"
     r"instant[aá]neas Lean congeladas|snapshots Lean|reproducci[oó]n (de archivo |)"
     r"independiente|no (son |es )?sustitut|determinaci[oó]n de prioridad|"
     r"suplementarias|Paper IV|release p[uú]blico|no reemplaza"),
]


def rd(p):
    return open(p, encoding="utf-8", errors="replace").read()


def displays(t):
    return [re.sub(r"\s+", "", x) for x in re.findall(r"\\\[(.+?)\\\]", t, re.S)]


def tags(t):
    return re.findall(r"\\tag\{([^}]*)\}", t)


def headings(t):
    return [(len(m.group(1)), re.sub(r"\s+", " ", m.group(2)).strip())
            for m in re.finditer(r"^(#{1,6})\s+(.+?)\s*$", t, re.M)]


def cites(t):
    out = []
    for m in re.finditer(r"\[(\d+(?:\s*,\s*\d+)*)\]", t):
        out.append(m.group(1).replace(" ", ""))
    return out


def theorem_blocks(t):
    """Ordered list of theorem/lemma/proposition/corollary/remark headings."""
    return [re.sub(r"\s+", " ", m.group(1)).strip() for m in re.finditer(
        r"^#{2,6}\s+((?:Theorem|Lemma|Proposition|Corollary|Remark|Claim|Teorema|Lema|"
        r"Proposici[oó]n|Corolario|Observaci[oó]n|Afirmaci[oó]n)[^\n]*)$", t, re.M)]


def classify(line):
    hit = [n for n, pat in CLASSIFIERS if re.search(pat, line, re.I)]
    return hit


def main():
    os.makedirs(OUT, exist_ok=True)
    res = {"pairs": {}}
    overall = True

    for lang, (op, np_) in PAIRS.items():
        a, b = rd(op), rd(np_)
        print(f"\n{'=' * 68}\n=== {lang}: {os.path.basename(op)} -> {os.path.basename(np_)}")
        print(f"  bytes {len(a.encode()):,} -> {len(b.encode()):,}")
        r = {"old": {"path": op, "sha256": hashlib.sha256(a.encode()).hexdigest()},
             "new": {"path": np_, "sha256": hashlib.sha256(b.encode()).hexdigest()}}

        # ---- (a) invariance of mathematical and bibliographic structure
        inv = {}
        for name, fn in (("displayed_formulas", displays), ("equation_tags", tags),
                         ("citation_references", cites), ("theorem_blocks", theorem_blocks)):
            xa, xb = fn(a), fn(b)
            same = xa == xb
            inv[name] = {"old_count": len(xa), "new_count": len(xb),
                         "sequence_identical": same,
                         "only_old": [str(x)[:120] for x in xa if x not in xb][:10],
                         "only_new": [str(x)[:120] for x in xb if x not in xa][:10]}
            print(f"  {name:22} {len(xa):>4} -> {len(xb):>4}  "
                  f"sequence identical: {same}")
            if not same:
                print(f"      only in v1.4: {inv[name]['only_old']}")
                print(f"      only in v1.5: {inv[name]['only_new']}")
        ha, hb = headings(a), headings(b)
        same_h = ha == hb
        inv["headings"] = {"old_count": len(ha), "new_count": len(hb),
                           "sequence_identical": same_h,
                           "only_old": [x[1] for x in ha if x not in hb][:10],
                           "only_new": [x[1] for x in hb if x not in ha][:10]}
        print(f"  {'headings':22} {len(ha):>4} -> {len(hb):>4}  "
              f"sequence identical: {same_h}")
        if not same_h:
            print(f"      only in v1.4: {inv['headings']['only_old']}")
            print(f"      only in v1.5: {inv['headings']['only_new']}")
        r["invariance"] = inv
        inv_ok = all(v["sequence_identical"] for v in inv.values())
        r["invariance_pass"] = inv_ok
        print(f"  --> structural invariance: {'PASS' if inv_ok else 'FAIL'}")

        # ---- (b) containment of every changed line in the declared delta set
        la, lb = a.splitlines(), b.splitlines()
        sm = difflib.SequenceMatcher(None, la, lb, autojunk=False)
        changed, unclassified = [], []
        for tag, i1, i2, j1, j2 in sm.get_opcodes():
            if tag == "equal":
                continue
            old_l = [x for x in la[i1:i2] if x.strip()]
            new_l = [x for x in lb[j1:j2] if x.strip()]
            hunk_cls = sorted(set(sum((classify(x) for x in old_l + new_l), [])))
            rec = {"op": tag, "classes": hunk_cls,
                   "old_lines": len(old_l), "new_lines": len(new_l),
                   "old": [x[:300] for x in old_l], "new": [x[:300] for x in new_l]}
            changed.append(rec)
            if not hunk_cls:
                unclassified.append(rec)
        counts = collections.Counter(c for rec in changed for c in rec["classes"])
        r["changed_hunks"] = len(changed)
        r["changed_lines"] = sum(x["old_lines"] + x["new_lines"] for x in changed)
        r["hunks"] = changed
        r["classified_counts"] = dict(counts)
        r["unclassified"] = unclassified
        print(f"  changed hunks: {len(changed)}  "
              f"(non-blank lines touched: {r['changed_lines']})")
        for k, v in sorted(counts.items()):
            print(f"      {k:34} {v}")
        print(f"  unclassified (undeclared) changes: {len(unclassified)}")
        for u in unclassified[:12]:
            print(f"      [{u['op']}] {(u['new'] or u['old'])[0][:170]}")
        r["containment_pass"] = not unclassified
        print(f"  --> delta containment: {'PASS' if not unclassified else 'FAIL'}")

        # ---- the four N02/N03 clarifications must actually be present in v1.5
        need = {
            "N02_simple_in_theorem_2_2": bool(
                re.search(r"(simple bipartite graph|grafo bipartito simple)[^\n]*"
                          r"maximum degree|(simple bipartite graph|grafo bipartito simple)",
                          b)),
            "N03_kernel_perfect_sentence": bool(
                re.search(r"(induced subdigraph of|subdigrafo inducido de)"
                          r".{0,60}kernel-perfect", b, re.S | re.I)),
            "N03_bounded_degree_induction": bool(
                re.search(r"maximum degree at most \\\(\\Delta\\\)|"
                          r"grado m[aá]ximo a lo (m[aá]s|sumo) \\\(\\Delta\\\)", b, re.I)),
            "N03_two_colour_max_degree_two": bool(
                re.search(r"maximum degree at most two|"
                          r"grado m[aá]ximo a lo (m[aá]s|sumo) dos", b, re.I)),
            "N03_well_defined_simple_path": bool(
                re.search(r"well-defined simple path|camino simple bien definido", b, re.I)),
        }
        r["clarifications_present"] = need
        print("  clarifications present in v1.5:")
        for k, v in need.items():
            print(f"      {'yes' if v else 'NO '} {k}")
        r["clarifications_pass"] = all(need.values())

        r["pass"] = inv_ok and not unclassified and all(need.values())
        overall &= r["pass"]
        res["pairs"][lang] = r
        print(f"  ===> {lang}: {'PASS' if r['pass'] else 'FAIL'}")

    res["E1_pass"] = overall
    print(f"\n{'=' * 68}\nE1 {'PASS' if overall else 'FAIL'}")
    with open(f"{OUT}/E1_delta.json", "w", encoding="utf-8", newline="\n") as f:
        json.dump(res, f, indent=1, ensure_ascii=False)
        f.write("\n")


if __name__ == "__main__":
    main()
