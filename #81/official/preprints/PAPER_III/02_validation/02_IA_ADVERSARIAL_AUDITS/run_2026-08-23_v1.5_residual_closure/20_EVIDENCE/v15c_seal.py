#!/usr/bin/env python3
"""Seal the EXT-V15-M01 closure run. Summary first, then manifests, then ZIP, then sidecar."""
import hashlib
import io
import json
import os
import shutil
import sys
import zipfile

sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding="utf-8", errors="replace")

RUN = "C:/v15c"
TOOLS = "C:/erdos_audit/tools"


def h(p):
    return hashlib.sha256(open(p, "rb").read()).hexdigest()


def walk(root, skip=()):
    out = []
    for d, _, fs in os.walk(root):
        for f in sorted(fs):
            r = os.path.relpath(os.path.join(d, f), root).replace("\\", "/")
            if any(r.startswith(s) for s in skip):
                continue
            out.append(r)
    return sorted(out)


def main():
    for s in ("v15c_closure.py", "v15c_seal.py"):
        shutil.copy2(f"{TOOLS}/{s}", f"{RUN}/20_EVIDENCE/{s}")

    summary = {
        "run": "run_2026-08-23_v1.5_residual_closure",
        "date": "2026-08-23",
        "scope": "residual closure test for EXT-V15-M01 only; no source gate repeated",
        "request_sha256":
            "37118ecff3894b8c018c1031cd619f88e05e449e6fd685cce14ff3920bbaf034",
        "closure_packet_sha256":
            "7972a0b5212bc69d0437fd328886a63e383bc60f54e91c365ab771e5a6be20e4",
        "preserved_source_report": {
            "path": "run_2026-08-23_v1.5_residual/30_REPORT/FINAL_AUDIT_REPORT.md",
            "sha256":
                "4f4537816840c62fb23521190fab4fa1a860085e05a4cb956d8afe1eb3b67596",
            "verdict": "CONDITIONAL_PASS",
            "rewritten": False,
            "byte_identical_to_auditor_own_copy": True},
        "verdict": "PASS",
        "finding_disposition": {
            "EXT-V14C-N02": "CLOSED in the source run, on its mathematics",
            "EXT-V14C-N03": "CLOSED in the source run, on its mathematics",
            "EXT-V15-M01": "CLOSED in this run"},
        "closure_test_as_stated_by_auditor":
            "no file in 03_reproducibility/ outside a v1.3/v1.4-labelled path names a "
            "non-v1.5 artifact or quotes a non-v1.5 hash",
        "closure_test_met": True,
        "checks": {
            "1_no_loose_files_under_manuscript_build_logs": True,
            "2_relocated_logs_intact": True,
            "3_current_v1_5_logs_correct": True,
            "4_consistency_json": True,
            "5_target_unchanged": True,
            "6_prior_reports_unmodified": True,
            "A_no_dangling_references": True,
            "B_local_links_resolve": True,
            "C_removed_evidence_preserved": True,
            "D_pattern_does_not_recur": True},
        "checks_passed": "10/10",
        "detail": {
            "loose_files_under_build_logs": 0,
            "build_log_subdirs": ["v1.3_legacy", "v1.4", "v1.5"],
            "legacy_logs": {"files": 29, "manifest_entries": 29, "hash_matches": 29,
                            "naming_a_v1_5_job": 0, "not_naming_a_v1_3_job": 0},
            "current_logs": {"files": 6, "hash_matches": 6,
                             "pages": {"en": 46, "es": 47},
                             "prohibited_diagnostics": 0},
            "consistency_json": {"generic_present": False, "versioned_verdict": "PASS",
                                 "versioned_checks": 61, "versioned_failed": 0,
                                 "md_en_sha256_matches_v1_5_target": True},
            "target_unchanged": {"manuscript_hashes": "6/6", "lean_zip": True},
            "prior_packages_reverify": {"run_2026-08-22_v1.4_residual": "60/60",
                                        "run_2026-08-23_v1.4_challenger": "24/24",
                                        "run_2026-08-23_v1.5_residual": "45/45"},
            "tree_txt": {"entries": 1572, "unresolvable": 0,
                         "regenerated": True,
                         "sha256": "2f5ae5a68faa561c91e106b04ca64019c9833726f848d22a00b52"
                                   "94e5f73f310",
                         "integrity_record_updated": True},
            "broken_local_links": 0,
            "shadowing_pattern_recurrences": 0,
            "files_scanned_for_dangling_references": 122},
        "author_verification_used_as_evidence": False,
        "author_verification_contrast_result": "PASS 16/16, agrees on every overlapping point",
        "stated_limitation":
            "byte-identity between the deleted generic MANUSCRIPT_CONSISTENCY_RESULTS.json "
            "and the copy preserved under superseded/ cannot be proved: the file is gone and "
            "neither the source audit nor the closure packet recorded its hash. Verified "
            "instead that the preserved copy describes v1.4 (md_en eea753a4..., PASS 51/51), "
            "so the v1.4 evidence was not destroyed",
        "auditor_tool_false_positives_corrected_during_run": 3,
        "blockers": 0, "criticals": 0, "majors": 0, "minors_open": 0, "notes_open": 0,
        "does_not_establish": [
            "the truth of Theorem 1.1",
            "the Lean nibble chain's internal parameter ledger",
            "novelty beyond the searched corpus; no priority determination",
            "human peer review",
            "resolution of the full chordal problem, which remains open",
            "independence: six external runs share one reasoning context, and this auditor "
            "raised all three findings whose fixes it has now reviewed"]}

    sp = f"{RUN}/30_REPORT/FINAL_CLOSURE_SUMMARY.json"
    with open(sp, "w", encoding="utf-8", newline="\n") as f:
        json.dump(summary, f, indent=1, ensure_ascii=False)
        f.write("\n")
    print("1. summary written first")

    ev = f"{RUN}/20_EVIDENCE"
    files = [x for x in walk(ev) if not x.endswith("SHA256_MANIFEST.txt")]
    with open(f"{ev}/SHA256_MANIFEST.txt", "w", encoding="utf-8", newline="\n") as f:
        for r in files:
            f.write(f"{h(f'{ev}/{r}')}  {r}\n")
    print(f"2. 20_EVIDENCE/SHA256_MANIFEST.txt: {len(files)} files")

    allf = walk(RUN, skip=("40_PACKAGE/",))
    man = {"run": summary["run"], "verdict": summary["verdict"], "file_count": len(allf),
           "files": [{"path": r, "sha256": h(f"{RUN}/{r}"),
                      "bytes": os.path.getsize(f"{RUN}/{r}")} for r in allf]}
    mp = f"{RUN}/40_PACKAGE/PACKAGE_MANIFEST.json"
    with open(mp, "w", encoding="utf-8", newline="\n") as f:
        json.dump(man, f, indent=1, ensure_ascii=False)
        f.write("\n")
    print(f"3. package manifest: {len(allf)} files")

    zp = f"{RUN}/40_PACKAGE/PAPER_III_v1.5_EXTERNAL_CLOSURE_AUDIT.zip"
    with zipfile.ZipFile(zp, "w", zipfile.ZIP_DEFLATED) as z:
        for r in allf:
            z.write(f"{RUN}/{r}", r)
        z.write(mp, "40_PACKAGE/PACKAGE_MANIFEST.json")
    with zipfile.ZipFile(zp) as z:
        assert z.testzip() is None
        names = z.namelist()
    print(f"4. archive: {len(names)} members, CRC clean")

    zh = h(zp)
    with open(zp + ".sha256", "w", encoding="utf-8", newline="\n") as f:
        f.write(f"{zh}  {os.path.basename(zp)}\n")

    bad = [i["path"] for i in man["files"] if h(f"{RUN}/{i['path']}") != i["sha256"]]
    print(f"\nverification: {len(man['files']) - len(bad)}/{len(man['files'])} match; "
          f"problems={bad or 'none'}")
    for k in ("30_REPORT/FINAL_CLOSURE_REPORT.md", "30_REPORT/FINAL_CLOSURE_SUMMARY.json",
              "00_CONTROL/CLOSURE_PROTOCOL.md",
              "20_EVIDENCE/EXT_V15_M01_INDEPENDENT_CHECK.json",
              "40_PACKAGE/PACKAGE_MANIFEST.json"):
        print(f"  in archive: {k in names}  {k}")
    print(f"\nZIP SHA-256: {zh}")


if __name__ == "__main__":
    main()
