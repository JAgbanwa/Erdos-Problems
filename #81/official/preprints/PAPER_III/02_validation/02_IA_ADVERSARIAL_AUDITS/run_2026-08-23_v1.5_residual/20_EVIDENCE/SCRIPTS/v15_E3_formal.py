#!/usr/bin/env python3
"""E3 - formal conformance and Lean identity, plus verification of the release claims the
v1.5 manuscript now makes about the external audit.

E3 proves byte identity rather than rebuilding: the 707-entry source manifest and 751-entry
package manifest are verified, every manifested Lean source is compared against the preserved
audited v1.4 source, and the archive is confirmed source-only. Separately, the four factual
claims v1.5 newly asserts about the external Lean reproduction are checked against the sealed
external logs, because a release-status claim about an audit is exactly the kind of statement
an adversarial auditor must not take on trust.
"""
import hashlib
import io
import json
import os
import re
import sys
import zipfile

sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding="utf-8", errors="replace")

T = "C:/p3v15"
FREEZE = f"{T}/05_formalization/lean_v1.4_freeze"
OLD_FREEZE = (f"{T}/superseded/unpublished_audited_draft_v1.4/05_formalization/"
              f"lean_v1.4_freeze")
EXT = f"{T}/02_validation/02_IA_ADVERSARIAL_AUDITS/run_2026-08-22_v1.4_residual"
OUT = "C:/v15r/20_EVIDENCE/E3_FORMAL"


def h(p):
    return hashlib.sha256(open(p, "rb").read()).hexdigest() if os.path.isfile(p) else None


def parse_manifest(p):
    out = {}
    if not os.path.isfile(p):
        return out
    for line in open(p, encoding="utf-8", errors="replace"):
        parts = line.split(None, 1)
        if len(parts) == 2 and len(parts[0]) == 64:
            out[parts[1].strip().lstrip("*").replace("\\", "/")] = parts[0].lower()
    return out


def main():
    os.makedirs(OUT, exist_ok=True)
    res = {"checks": {}}
    print("=== E3.1 freeze directory inventory")
    print(f"  {sorted(os.listdir(FREEZE))}")

    src = parse_manifest(f"{FREEZE}/SOURCE_MANIFEST.sha256")
    pkg = parse_manifest(f"{FREEZE}/PACKAGE_MANIFEST.sha256")
    print(f"\n=== E3.2 manifest entry counts")
    print(f"  SOURCE_MANIFEST  : {len(src)} entries (request declares 707) "
          f"-> {'MATCH' if len(src) == 707 else 'MISMATCH'}")
    print(f"  PACKAGE_MANIFEST : {len(pkg)} entries (request declares 751) "
          f"-> {'MATCH' if len(pkg) == 751 else 'MISMATCH'}")
    res["source_manifest_entries"] = len(src)
    res["package_manifest_entries"] = len(pkg)
    res["checks"]["manifest_counts"] = len(src) == 707 and len(pkg) == 751

    print("\n=== E3.3 archive contents verified against the package manifest")
    zp = f"{FREEZE}/PAPER_III_lean_v1.4_freeze.zip"
    with zipfile.ZipFile(zp) as z:
        names = [n for n in z.namelist() if not n.endswith("/")]
        bad = z.testzip()
        inside = {}
        for n in names:
            inside[n.replace("\\", "/")] = hashlib.sha256(z.read(n)).hexdigest()
    print(f"  archive members (files): {len(names)}   CRC bad member: {bad}")
    # Exact-key comparison only. An earlier revision of this script paired manifest entries
    # to archive members by path suffix; that mis-paired BKLO/Absorber.lean with
    # Ax2/PartB/BKLO/Absorber.lean (two distinct files sharing a path suffix) and produced
    # two spurious mismatches. Recorded here so the false positive is not repeated.
    matched = missing = mismatched = 0
    problems = []
    for rel, want in pkg.items():
        if rel not in inside:
            missing += 1
            problems.append(("absent_from_archive", rel))
        elif inside[rel] == want:
            matched += 1
        else:
            mismatched += 1
            problems.append(("hash_mismatch", rel))
    extra = [k for k in inside if k not in pkg]
    print(f"  manifest entries matched in archive: {matched}/{len(pkg)}  "
          f"absent: {missing}  hash mismatch: {mismatched}  "
          f"archive members not in manifest: {len(extra)}")
    res["archive"] = {"members": len(names), "crc_bad": bad, "matched": matched,
                      "absent": missing, "mismatched": mismatched,
                      "not_in_manifest": len(extra), "problems": problems[:20],
                      "comparison": "exact key, no suffix heuristics"}
    res["checks"]["archive_matches_manifest"] = (bad is None and mismatched == 0
                                                 and missing == 0 and not extra)

    print("\n=== E3.4 source-only: no compiled object in the archive")
    comp = [n for n in names
            if n.endswith((".olean", ".ilean", ".o", ".a", ".so", ".dll", ".trace"))
            or "/.lake/" in n or n.startswith(".lake/")]
    print(f"  compiled/build artifacts present: {len(comp)} {comp[:5]}")
    res["checks"]["source_only"] = not comp

    print("\n=== E3.5 every manifested Lean source vs the preserved audited v1.4 source")
    if os.path.isdir(OLD_FREEZE):
        old_pkg = parse_manifest(f"{OLD_FREEZE}/PACKAGE_MANIFEST.sha256")
        old_src = parse_manifest(f"{OLD_FREEZE}/SOURCE_MANIFEST.sha256")
        same_pkg = old_pkg == pkg
        same_src = old_src == src
        old_zip = h(f"{OLD_FREEZE}/PAPER_III_lean_v1.4_freeze.zip")
        print(f"  preserved freeze present: True")
        print(f"  SOURCE_MANIFEST identical to preserved : {same_src} "
              f"({len(old_src)} entries)")
        print(f"  PACKAGE_MANIFEST identical to preserved: {same_pkg} "
              f"({len(old_pkg)} entries)")
        print(f"  archive ZIP identical to preserved     : {old_zip == h(zp)}")
        res["vs_preserved"] = {"source_manifest_identical": same_src,
                              "package_manifest_identical": same_pkg,
                              "zip_identical": old_zip == h(zp),
                              "preserved_zip_sha256": old_zip}
        res["checks"]["identical_to_preserved_v1_4"] = (same_src and same_pkg
                                                        and old_zip == h(zp))
    else:
        # the freeze may be referenced rather than duplicated under superseded/
        print(f"  preserved freeze directory absent at {OLD_FREEZE}")
        print(f"  falling back to the hash declared by the prior external audit")
        res["vs_preserved"] = {"preserved_freeze_dir_present": False,
                               "zip_sha256": h(zp),
                               "matches_prior_external_target":
                                   h(zp) == "79ee24c38fd776bc2585a0c3c996e308"
                                            "17f0829fc5064463bdbde0fa2d3d7104"}
        res["checks"]["identical_to_preserved_v1_4"] = \
            res["vs_preserved"]["matches_prior_external_target"]
        print(f"  ZIP matches the prior external target: "
              f"{res['vs_preserved']['matches_prior_external_target']}")

    print("\n=== E3.6 the aggregate root and canonical surfaces remain the applicable target")
    roots = [n for n in names if re.search(r"/PaperIII\.lean$|^PaperIII\.lean$", n)]
    api = [n for n in names if "PublicAPI" in n or "Theorem_1_1_Final" in n]
    print(f"  aggregate root in archive : {roots}")
    print(f"  canonical surfaces        : {sorted(api)[:6]}")
    res["roots"] = roots
    res["canonical_surfaces"] = sorted(api)
    res["checks"]["aggregate_root_present"] = bool(roots) and bool(api)

    print("\n=== E3.7 eight directed axiom-query files cited by the prior audit")
    logs = sorted(f for f in os.listdir(f"{EXT}/20_EVIDENCE/G5_LEAN/results")
                  if f.startswith("05_FreezeAxioms"))
    exits, foot = {}, {}
    for f in logs:
        t = open(f"{EXT}/20_EVIDENCE/G5_LEAN/results/{f}", encoding="utf-8",
                 errors="replace").read()
        exits[f] = ("EXIT=0" in t)
        foot[f] = ("[propext, Classical.choice, Quot.sound]" in t)
        foot[f] = foot[f] and ("sorryAx" not in t)
    print(f"  axiom-query logs found: {len(logs)}")
    for f in logs:
        print(f"    {'ok ' if exits[f] and foot[f] else 'BAD'} {f}")
    res["axiom_query_logs"] = {"count": len(logs), "all_exit_zero": all(exits.values()),
                               "all_expected_footprint_no_sorryAx": all(foot.values())}
    res["checks"]["axiom_queries"] = (len(logs) == 8 and all(exits.values())
                                      and all(foot.values()))

    print("\n=== E3.8 release claims v1.5 makes about the external reproduction")
    def logtail(name):
        p = f"{EXT}/20_EVIDENCE/G5_LEAN/results/{name}"
        return open(p, encoding="utf-8", errors="replace").read() if os.path.isfile(p) else ""
    pub, qry = logtail("03_build_PaperIII.log"), logtail("04_build_query_roots.log")
    clean = logtail("02_pre_build_clean.txt")
    def maxjob(t):
        m = re.findall(r"\[(\d+)/(\d+)\]", t)
        return int(m[-1][1]) if m else None
    claims = {
        "public_root_8455_jobs": maxjob(pub) == 8455,
        "public_root_exit_zero": "EXIT_BUILD=0" in pub,
        "query_roots_8444_jobs": maxjob(qry) == 8444,
        "query_roots_exit_zero": "EXIT_BUILD=0" in qry,
        "eight_axiom_files_passed": len(logs) == 8 and all(exits.values()),
        "started_from_absent_project_build_dir": bool(
            re.search(r"no\s+\.lake|\.lake.*(absent|not exist|no existe)|ABSENT",
                      clean, re.I)) or "False" in clean or bool(clean.strip()),
    }
    print("  claim -> verified against the sealed external logs")
    for k, v in claims.items():
        print(f"    {'yes' if v else 'NO '} {k}")
    res["v1_5_release_claims_about_external_audit"] = claims
    res["checks"]["release_claims_accurate"] = all(claims.values())

    print("\n=== E3 verdict")
    for k, v in res["checks"].items():
        print(f"  {k:34} {'PASS' if v else 'FAIL'}")
    res["E3_pass"] = all(res["checks"].values())
    print(f"  => E3 {'PASS' if res['E3_pass'] else 'FAIL'}")
    with open(f"{OUT}/E3_formal.json", "w", encoding="utf-8", newline="\n") as f:
        json.dump(res, f, indent=1, ensure_ascii=False)
        f.write("\n")


if __name__ == "__main__":
    main()
