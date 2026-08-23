#!/usr/bin/env python3
"""E0 - intake and sealing for the Paper III v1.5 external residual audit.

Recomputes every declared hash, checks sidecar hygiene and ZIP CRC, verifies the six
preserved authorities, confirms the v1.4 target is preserved under superseded/, and confirms
that only v1.5 manuscript artifacts are active. Nothing is trusted from a declaration.
"""
import hashlib
import io
import json
import os
import sys
import zipfile

sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding="utf-8", errors="replace")

T = "C:/p3v15"
OUT = "C:/v15r/20_EVIDENCE/E0_INTAKE"

TARGET = {
    "01_manuscript/PAPER_III_preprint_v1.5.md":
        "a98e9313bfe5f1f98cc92bb29ba97386e8178e38c0201854cf40bd255066c99a",
    "01_manuscript/PAPER_III_preprint_v1.5_en.tex":
        "6a97bc718df81d1cf91ab88ccffd9a9f701482fb898fbeca9240d19b4124195c",
    "01_manuscript/PAPER_III_preprint_v1.5_en.pdf":
        "077a12da4db42ecbe6bcc25333539bf7ee3e63fa20bc7a46d8e801120ac9bb27",
    "01_manuscript/PAPER_III_preprint_v1.5_es.md":
        "ee5a3ef2614316d573f622633d3ac5c544a262a43f36d0a8bacfe149b7beca3e",
    "01_manuscript/PAPER_III_preprint_v1.5_es.tex":
        "cfc2cac78ce2495207e300c7f184c04b0aa778d91f077f25d4481b68dfb8ebcd",
    "01_manuscript/PAPER_III_preprint_v1.5_es.pdf":
        "5ed3f83b97f6c900d63d09dd3eb491ed903693df1b90fe0dbac5df2e1e93ec92",
}
LEAN_ZIP = ("05_formalization/lean_v1.4_freeze/PAPER_III_lean_v1.4_freeze.zip",
            "79ee24c38fd776bc2585a0c3c996e30817f0829fc5064463bdbde0fa2d3d7104")

AUTHORITIES = {
    "v1.4 internal final report":
        ("1cb57678b44eebf937fac0cd2aade4c46b51d75d8f68308aa22d742b946d760f",
         "02_validation/01_INTERNAL_AUDITS/run_2026-08-22_v1.4/10_REPORT/"
         "INTERNAL_AUDIT_FINAL_REPORT.md"),
    "v1.4 external residual final report":
        ("2c19bf1ca74f77cc409b8d0102adf01b92d13db885ac81d15d156477abed8842",
         "02_validation/02_IA_ADVERSARIAL_AUDITS/run_2026-08-22_v1.4_residual/30_REPORT/"
         "FINAL_AUDIT_REPORT.md"),
    "v1.4 final external challenger report":
        ("a196479b8b2adde5077669ec5e398dfc4d640e006bd97b10ef0f72696bdfb5f3",
         "02_validation/02_IA_ADVERSARIAL_AUDITS/run_2026-08-23_v1.4_challenger/30_REPORT/"
         "FINAL_AUDIT_REPORT.md"),
    "v1.5 internal residual final report":
        ("a641e7ed3f8b57eced09027f0937622ff1bd1e12ef289de81b1bdc0e0eeefeae",
         "02_validation/01_INTERNAL_AUDITS/run_2026-08-23_v1.5_internal_residual/10_REPORT/"
         "FINAL_INTERNAL_RESIDUAL_AUDIT_REPORT.md"),
    "v1.5 semantic-integrity report":
        ("4b467ea829c4bb8643948055bb6b0369d3fcd50752531e6ded222096e27de48d",
         "04_integrity/SEMANTIC_INTEGRITY_REPORT_v1.5.md"),
    "v1.5 changelog":
        ("d247e08f3b9837a6e4de582e2c4e93eb8e6665b2caf10ead5062f0e71b5cdd9f",
         "CHANGELOG_v1.5.md"),
}

# the auditor's own copy of the challenger report, for provenance of that authority
OWN_CHALLENGER = "C:/v14c/30_REPORT/FINAL_AUDIT_REPORT.md"


def h(p):
    return hashlib.sha256(open(p, "rb").read()).hexdigest() if os.path.isfile(p) else None


def main():
    os.makedirs(OUT, exist_ok=True)
    res = {"target": {}, "lean_zip": {}, "authorities": {}, "checks": {}}

    print("=== E0.1 six declared manuscript hashes")
    ok = True
    for rel, want in TARGET.items():
        got = h(f"{T}/{rel}")
        m = got == want
        ok &= m
        res["target"][rel] = {"declared": want, "computed": got, "match": m,
                              "bytes": os.path.getsize(f"{T}/{rel}")}
        print(f"  {'MATCH   ' if m else 'MISMATCH'} {os.path.basename(rel)}")
    res["checks"]["target_hashes"] = ok

    print("\n=== E0.2 Lean archive")
    rel, want = LEAN_ZIP
    got = h(f"{T}/{rel}")
    res["lean_zip"] = {"declared": want, "computed": got, "match": got == want}
    print(f"  {'MATCH' if got == want else 'MISMATCH'}  {want}")
    with zipfile.ZipFile(f"{T}/{rel}") as z:
        bad = z.testzip()
        names = z.namelist()
    res["lean_zip"].update({"members": len(names), "crc_bad_member": bad,
                            "source_only": not any(
                                n.endswith((".olean", ".ilean", ".c", ".o", ".a"))
                                or "/.lake/" in n or n.startswith(".lake/")
                                for n in names)})
    print(f"  members={len(names)}  CRC bad member={bad}  "
          f"source-only={res['lean_zip']['source_only']}")
    res["checks"]["lean_zip"] = (got == want and bad is None
                                 and res["lean_zip"]["source_only"])

    print("\n=== E0.3 manuscript sidecar hygiene")
    sc = f"{T}/01_manuscript/PAPER_III_preprint_v1.5_SHA256.txt"
    raw = open(sc, "rb").read()
    lines = [l for l in raw.decode().splitlines() if l.strip()]
    parsed = {}
    for l in lines:
        a, b = l.split(None, 1)
        parsed[b.strip().lstrip("*")] = a.lower()
    agree = all(parsed.get(os.path.basename(r)) == w for r, w in TARGET.items())
    res["sidecar"] = {"path": sc, "sha256": h(sc), "lf_only": b"\r" not in raw,
                      "entries": len(parsed), "agrees_with_declared": agree}
    print(f"  LF-only={b'\r' not in raw}  entries={len(parsed)}  "
          f"agrees with declared={agree}")
    res["checks"]["sidecar"] = (b"\r" not in raw) and agree and len(parsed) == 6

    print("\n=== E0.4 six preserved authorities")
    aok = True
    for name, (want, rel) in AUTHORITIES.items():
        p = f"{T}/{rel}"
        got = h(p)
        m = got == want
        aok &= m
        res["authorities"][name] = {"path": rel, "declared": want, "computed": got,
                                    "match": m, "present": os.path.isfile(p)}
        print(f"  {'MATCH   ' if m else 'MISMATCH'} {name}")
        if not m:
            print(f"           declared {want}\n           computed {got}")
    res["checks"]["authorities"] = aok

    print("\n=== E0.5 provenance of the challenger authority")
    own = h(OWN_CHALLENGER)
    decl = AUTHORITIES["v1.4 final external challenger report"][0]
    res["challenger_provenance"] = {
        "auditor_own_copy": OWN_CHALLENGER, "auditor_own_sha256": own,
        "declared_in_target": decl, "identical": own == decl}
    print(f"  auditor's own copy : {own}")
    print(f"  copy in the target : {decl}")
    print(f"  byte-identical     : {own == decl}")

    print("\n=== E0.6 only v1.5 manuscript artifacts active; v1.4 preserved")
    act = sorted(os.listdir(f"{T}/01_manuscript"))
    stray = [f for f in act if ("v1.4" in f or "v1.3" in f or "v1.2" in f)]
    sup = f"{T}/superseded/unpublished_audited_draft_v1.4"
    sup_files = sorted(os.listdir(sup)) if os.path.isdir(sup) else []
    res["active_manuscript_dir"] = act
    res["stray_old_versions_in_active_dir"] = stray
    res["superseded_v1_4"] = {"present": os.path.isdir(sup), "entries": sup_files}
    print(f"  active 01_manuscript entries: {len(act)}; stray older versions: {stray or 'none'}")
    print(f"  superseded/unpublished_audited_draft_v1.4 present: {os.path.isdir(sup)}")
    print(f"    entries: {sup_files}")
    res["checks"]["no_stray_versions"] = not stray
    res["checks"]["v1_4_preserved"] = os.path.isdir(sup) and bool(sup_files)

    print("\n=== E0 verdict")
    for k, v in res["checks"].items():
        print(f"  {k:22} {'PASS' if v else 'FAIL'}")
    res["E0_pass"] = all(res["checks"].values())
    print(f"  => E0 {'PASS' if res['E0_pass'] else 'FAIL'}")

    with open(f"{OUT}/E0_intake.json", "w", encoding="utf-8", newline="\n") as f:
        json.dump(res, f, indent=1, ensure_ascii=False)
        f.write("\n")


if __name__ == "__main__":
    main()
