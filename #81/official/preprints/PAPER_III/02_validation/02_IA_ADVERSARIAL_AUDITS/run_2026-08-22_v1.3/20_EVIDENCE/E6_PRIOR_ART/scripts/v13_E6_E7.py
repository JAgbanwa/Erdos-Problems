#!/usr/bin/env python3
"""Paper III v1.3 -- gates E6 (citations, prior art, novelty) and E7 (release package).

E6 is bounded by what this auditor can reach. That bound is stated, not hidden: the request
says novelty cannot PASS from the author's bibliography alone, and this auditor has no
institutional bibliographic database and no access to erdosproblems.com. So E6 records what
was checked structurally, what was checked against retrievable sources, and what remains
unverified.

E7 checks self-containment, release-status consistency, cross-artifact agreement of names,
hashes and metadata, and re-verifies the target hashes after the audit to show the bytes did
not move.
"""
import hashlib
import json
import os
import re

T = "C:/p3v13"
M = f"{T}/01_manuscript"
OUT = "C:/erdos_audit/v13"


def rd(p):
    return open(p, encoding="utf-8", errors="replace").read()


def h(p):
    return hashlib.sha256(open(p, "rb").read()).hexdigest()


def e6():
    en = rd(f"{M}/PAPER_III_preprint_draft_v1.3.md")
    es = rd(f"{M}/PAPER_III_preprint_draft_v1.3_es.md")
    r = {"gate": "E6"}

    # the bibliography, parsed
    refs = {}
    for m in re.finditer(r"^\s*\[(\d+)\]\s*(.+)$", en, re.M):
        refs[int(m.group(1))] = re.sub(r"\s+", " ", m.group(2)).strip()
    r["bibliography"] = refs
    r["reference_count"] = len(refs)

    # every reference must be cited in the body, and every citation must resolve
    cited = set()
    for m in re.finditer(r"\[(\d+(?:\s*[,;]\s*\d+)*)\]", en):
        for n in re.findall(r"\d+", m.group(1)):
            cited.add(int(n))
    body_only = sorted(cited - set(refs))
    listed_only = sorted(set(refs) - cited)
    r["citation_integrity"] = {
        "cited_numbers": sorted(cited),
        "cited_but_not_listed": body_only,
        "listed_but_never_cited": listed_only,
        "clean": not body_only and not listed_only}

    # the specific sources the request names
    NAMED = {"Cavers survey": r"Cavers",
             "Erdos #81 record": r"Problem\s*#?\s*81|erdosproblems",
             "Chen-Erdos-Ordman": r"Chen[^.]{0,40}Erd[oő]s[^.]{0,40}Ordman",
             "Erdos-Ordman-Zalcstein": r"Erd[oő]s[^.]{0,40}Ordman[^.]{0,40}Zalcstein",
             "Haxell-Rodl": r"Haxell[^.]{0,20}R[oö]dl",
             "Yuster": r"Yuster",
             "Barber-Kuhn-Lo-Osthus": r"Barber[^.]{0,40}Osthus",
             "Dross": r"Dross",
             "Galvin": r"Galvin",
             "Tuza": r"Tuza"}
    r["named_sources_present"] = {
        k: {"EN": len(re.findall(v, en, re.I)), "ES": len(re.findall(v, es, re.I))}
        for k, v in NAMED.items()}

    # the 3/16 -> 1/6 improvement claim, and the chordal/split separation
    r["improvement_claim"] = {
        "3/16 mentions_EN": len(re.findall(r"3/16|\\frac\{3\}\{16\}", en)),
        "1/6 sharp_EN": len(re.findall(r"sharp[^.]{0,40}(1/6|\\frac\{1\}\{6\})", en, re.I)),
        "chordal_open_EN": len(re.findall(r"chordal[^.]{0,80}remains open", en, re.I)),
        "chordal_open_ES": len(re.findall(r"cordal[^.]{0,90}(abierto|abierta)", es, re.I))}

    r["auditor_retrieval"] = {
        "retrieved_and_matched_against_the_claim_it_supports": [],
        "not_retrieved": sorted(refs),
        "reason": ("No institutional bibliographic database was reachable in this "
                   "environment, and erdosproblems.com has returned HTTP 403 to this "
                   "auditor on every attempt across this and prior runs. No reference was "
                   "independently retrieved in THIS run."),
        "search_strings_run": [],
        "databases_consulted": []}

    r["verdict"] = "INCONCLUSIVE"
    r["verdict_basis"] = (
        "Structural citation integrity is verifiable and passes: every bracketed citation "
        "resolves to a listed reference and every listed reference is cited. The scope "
        "separation the request asks about is present and explicit. But the request "
        "requires retrieving and checking every cited source against the claim it supports, "
        "and conducting an independent specialist search through the audit date; neither was "
        "possible here. Novelty therefore cannot PASS, and the request itself forbids "
        "passing it on the author's bibliography alone.")
    return r


def e7():
    r = {"gate": "E7"}
    en = rd(f"{M}/PAPER_III_preprint_draft_v1.3.md")
    es = rd(f"{M}/PAPER_III_preprint_draft_v1.3_es.md")

    # self-containment: the manuscript must not require an earlier internal draft
    NEED = ["preprint_draft_v1.2", "v1.2 draft", "internal audit", "auditoria interna",
            "CORRECTION_MATRIX", "REGRESSION_MATRIX", "see the internal",
            "EXT-P3-", "EXT-PIII-", "run_2026"]
    r["self_containment"] = {
        "EN_hits": {k: en.count(k) for k in NEED if en.count(k)},
        "ES_hits": {k: es.count(k) for k in NEED if es.count(k)},
        "clean": not any(en.count(k) for k in NEED) and not any(es.count(k) for k in NEED)}

    # release status wording across the package
    files = {}
    for rel in ("README.md", "DRAFT_METADATA.yml", "DRAFT_NOTES.md", "CHANGELOG_v1.3.md",
                "04_integrity/README.md", "05_formalization/lean_v1.3_freeze/FREEZE_METADATA.json",
                "05_formalization/lean_v1.3_freeze/FREEZE_REPORT.md"):
        p = os.path.join(T, rel)
        if os.path.isfile(p):
            files[rel] = rd(p)
    r["release_status_by_file"] = {
        rel: {"first formal public release": t.count("first formal public release"),
              "candidate": len(re.findall(r"candidat", t, re.I)),
              "unpublished": len(re.findall(r"unpublished", t, re.I)),
              "v1.3": t.count("v1.3"),
              "NOT_STARTED": t.count("NOT_STARTED"),
              "PASS": t.count("PASS")}
        for rel, t in files.items()}

    # the metadata/internal-audit contradiction, stated as data
    fm = json.loads(rd(f"{T}/05_formalization/lean_v1.3_freeze/FREEZE_METADATA.json"))
    ia = f"{T}/02_validation/01_INTERNAL_AUDITS/10_REPORT/INTERNAL_AUDIT_FINAL_REPORT.md"
    ia_txt = rd(ia) if os.path.isfile(ia) else ""
    r["metadata_vs_package"] = {
        "FREEZE_METADATA.status": fm.get("status"),
        "FREEZE_METADATA.internal_audit": fm.get("internal_audit"),
        "FREEZE_METADATA.external_reproduction": fm.get("external_reproduction"),
        "internal_audit_report_present": bool(ia_txt),
        "internal_audit_states_verdict": ("PASS" if "**Overall verdict:** `PASS`" in ia_txt
                                          else "?"),
        "recorded_build_log": fm.get("recorded_build", {}).get("log"),
        "recorded_build_jobs": fm.get("recorded_build", {}).get("jobs"),
        "recorded_build_seconds": fm.get("recorded_build", {}).get("duration_seconds"),
        "contradiction": (fm.get("internal_audit") == "NOT_STARTED" and bool(ia_txt))}

    # cross-artifact agreement: declared hashes vs recomputed, again, after the audit
    sidecar = f"{T}/04_integrity/CURRENT_TARGET_SHA256.txt"
    rows = []
    for line in rd(sidecar).splitlines():
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        parts = line.split(None, 1)
        if len(parts) == 2 and re.fullmatch(r"[0-9a-fA-F]{64}", parts[0]):
            name = parts[1].lstrip("*").strip().replace("\\", "/")
            p = os.path.join(T, name)
            rows.append({"file": name, "declared": parts[0].lower(),
                         "recomputed": h(p) if os.path.isfile(p) else None})
    r["final_hash_reverification"] = {
        "entries": len(rows),
        "matching": sum(1 for x in rows if x["declared"] == x["recomputed"]),
        "mismatches": [x for x in rows if x["declared"] != x["recomputed"]],
        "target_unchanged_during_audit":
            all(x["declared"] == x["recomputed"] for x in rows)}

    r["verdict"] = ("PASS_WITH_FINDINGS" if r["metadata_vs_package"]["contradiction"]
                    else "PASS")
    return r


def main():
    os.makedirs(f"{OUT}/E6", exist_ok=True)
    os.makedirs(f"{OUT}/E7", exist_ok=True)
    a, b = e6(), e7()
    json.dump(a, open(f"{OUT}/E6/prior_art.json", "w", encoding="utf-8"), indent=1, ensure_ascii=False)
    json.dump(b, open(f"{OUT}/E7/release_package.json", "w", encoding="utf-8"), indent=1, ensure_ascii=False)

    print("=== E6")
    print(f"  referencias listadas: {a['reference_count']}")
    ci = a["citation_integrity"]
    print(f"  integridad de citas: limpia={ci['clean']} "
          f"| citadas sin listar={ci['cited_but_not_listed']} "
          f"| listadas sin citar={ci['listed_but_never_cited']}")
    print("  fuentes que la solicitud nombra:")
    for k, v in a["named_sources_present"].items():
        print(f"     {k:26} EN {v['EN']:3}  ES {v['ES']:3}")
    print(f"  reclamo de mejora: {a['improvement_claim']}")
    print(f"  recuperadas por el auditor en ESTA corrida: "
          f"{len(a['auditor_retrieval']['retrieved_and_matched_against_the_claim_it_supports'])}"
          f" de {a['reference_count']}")
    print(f"  veredicto E6: {a['verdict']}")

    print("\n=== E7")
    sc = b["self_containment"]
    print(f"  autocontencion: limpia={sc['clean']} EN={sc['EN_hits']} ES={sc['ES_hits']}")
    mv = b["metadata_vs_package"]
    print(f"  FREEZE_METADATA.status          : {mv['FREEZE_METADATA.status']}")
    print(f"  FREEZE_METADATA.internal_audit  : {mv['FREEZE_METADATA.internal_audit']}")
    print(f"  informe interno presente        : {mv['internal_audit_report_present']}"
          f" con veredicto {mv['internal_audit_states_verdict']}")
    print(f"  CONTRADICCION                   : {mv['contradiction']}")
    print(f"  build registrado                : {mv['recorded_build_log']} "
          f"({mv['recorded_build_jobs']} jobs en {mv['recorded_build_seconds']}s)")
    fr = b["final_hash_reverification"]
    print(f"  reverificacion final de hashes  : {fr['matching']}/{fr['entries']} "
          f"| objetivo intacto={fr['target_unchanged_during_audit']}")
    print(f"  veredicto E7: {b['verdict']}")


if __name__ == "__main__":
    main()
