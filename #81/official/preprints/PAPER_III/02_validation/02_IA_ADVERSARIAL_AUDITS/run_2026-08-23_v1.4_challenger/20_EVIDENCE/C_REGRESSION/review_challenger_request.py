#!/usr/bin/env python3
"""Review the challenger-correction-review request by checking every factual claim it makes
that is checkable: the two hashes it declares for the prior audit's own artifacts, the six
corrected-target hashes, and its claim that the English artifacts and the Lean archive are
byte-identical to what the prior audit examined."""
import hashlib
import io
import os
import sys

sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding="utf-8", errors="replace")

T = "C:/p3v14"
M = f"{T}/01_manuscript"
PRIOR = f"{T}/02_validation/02_IA_ADVERSARIAL_AUDITS/run_2026-08-22_v1.4_residual"

DECLARED_PRIOR = {
    "30_REPORT/FINAL_AUDIT_REPORT.md":
        "2c19bf1ca74f77cc409b8d0102adf01b92d13db885ac81d15d156477abed8842",
    "10_LEDGER/FINDINGS_LEDGER.csv":
        "17db6da295c4e8bed225b20dd676fa09a2b766a4a84ccce0fd74810f35fe2b39",
}

DECLARED_TARGET = {
    "PAPER_III_preprint_draft_v1.4.md":
        "eea753a4c352bafcb36f8bd09c262de0bfcae5379318264aa76c21628965136f",
    "PAPER_III_preprint_draft_v1.4_en.tex":
        "5e3cf6da1d43a213bd5b2991c0916e045192b0574cf759129de009d99b64f90f",
    "PAPER_III_preprint_draft_v1.4_en.pdf":
        "afd00647f22b97fd2f761ed052857e4273bc88cb265b9d1af8dad347ba943702",
    "PAPER_III_preprint_draft_v1.4_es.md":
        "83e3844e5b62ddeb8cebed46d1557e692f94b5ed25bb683f6b6e173f8ebfe15c",
    "PAPER_III_preprint_draft_v1.4_es.tex":
        "fbf30d758c849fb062f1619f18e2c2ca68b0e6ddaf69f8741b9fde8eee756910",
    "PAPER_III_preprint_draft_v1.4_es.pdf":
        "5804253aabc815bc0092048c47289f2956273a0a477b4e1b5a7c8906987ee8d4",
}

LEAN = "79ee24c38fd776bc2585a0c3c996e30817f0829fc5064463bdbde0fa2d3d7104"

# what the prior audit actually recorded for the target, from its own manifest
PRIOR_MANIFEST = f"{PRIOR}/00_CONTROL/TARGET_SHA256.txt"


def h(p):
    return hashlib.sha256(open(p, "rb").read()).hexdigest() if os.path.isfile(p) else None


def main():
    print("=== 1. the two hashes the request declares for the PRIOR AUDIT's own artifacts")
    for rel, want in DECLARED_PRIOR.items():
        p = os.path.join(PRIOR, rel)
        got = h(p)
        print(f"  {rel}")
        print(f"    exists   : {os.path.isfile(p)}")
        print(f"    declared : {want}")
        print(f"    computed : {got}")
        print(f"    MATCH    : {got == want}")

    print("\n=== 2. the six corrected-target hashes")
    for name, want in DECLARED_TARGET.items():
        got = h(os.path.join(M, name))
        print(f"  {'MATCH ' if got == want else 'MISMATCH'} {name}")
        if got != want:
            print(f"      declared {want}")
            print(f"      computed {got}")

    print("\n=== 3. the Lean archive")
    got = h(f"{T}/05_formalization/lean_v1.4_freeze/PAPER_III_lean_v1.4_freeze.zip")
    print(f"  declared {LEAN}")
    print(f"  computed {got}")
    print(f"  MATCH    {got == LEAN}")

    print("\n=== 4. the claim 'the English artifacts are byte-identical to the prior "
          "external target'")
    prior = {}
    if os.path.isfile(PRIOR_MANIFEST):
        for line in open(PRIOR_MANIFEST, encoding="utf-8"):
            pr = line.split(None, 1)
            if len(pr) == 2 and len(pr[0]) == 64:
                prior[pr[1].strip().replace("\\", "/")] = pr[0].lower()
        print(f"  prior audit's own manifest: {len(prior)} entries")
        for name in DECLARED_TARGET:
            key = f"01_manuscript/{name}"
            was = prior.get(key)
            now = h(os.path.join(M, name))
            lang = "EN" if ("_en." in name or name.endswith("v1.4.md")) else "ES"
            verdict = ("unchanged" if was == now
                       else ("CHANGED" if was else "not in prior manifest"))
            print(f"    [{lang}] {name:44} {verdict}")
    else:
        print(f"  prior manifest NOT FOUND at {PRIOR_MANIFEST}")

    print("\n=== 5. are the prior audit's build logs and manifests still present and sealed?")
    for rel in ("20_EVIDENCE/G5_LEAN/results/03_build_PaperIII.log",
                "20_EVIDENCE/G5_LEAN/results/04_build_query_roots.log",
                "20_EVIDENCE/G5_LEAN/results/02_pre_build_clean.txt",
                "20_EVIDENCE/G5_LEAN/SHA256_MANIFEST.txt",
                "40_PACKAGE/EXTERNAL_AUDIT_PACKAGE.zip",
                "40_PACKAGE/EXTERNAL_AUDIT_PACKAGE_SHA256.txt",
                "30_REPORT/FINAL_AUDIT_SUMMARY.json"):
        p = os.path.join(PRIOR, rel)
        print("  %8s %s" % ("present" if os.path.isfile(p) else "MISSING", rel))

    # and does the prior package still verify against its own manifest?
    import json
    pm = os.path.join(PRIOR, "40_PACKAGE", "PACKAGE_MANIFEST.json")
    if os.path.isfile(pm):
        m = json.load(open(pm))
        bad = [i["path"] for i in m["files"]
               if h(os.path.join(PRIOR, i["path"])) != i["sha256"]]
        print(f"\n  prior package: {len(m['files']) - len(bad)}/{len(m['files'])} files "
              f"verify; problems={bad}")
        zp = os.path.join(PRIOR, "40_PACKAGE", "EXTERNAL_AUDIT_PACKAGE.zip")
        sc = zp + "_SHA256.txt"
        sc2 = os.path.join(PRIOR, "40_PACKAGE", "EXTERNAL_AUDIT_PACKAGE_SHA256.txt")
        side = sc if os.path.isfile(sc) else sc2
        if os.path.isfile(zp) and os.path.isfile(side):
            declared = open(side, encoding="utf-8").read().split()[0].lower()
            print(f"  prior ZIP sidecar matches: {h(zp) == declared}")


if __name__ == "__main__":
    main()
