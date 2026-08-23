#!/usr/bin/env python3
"""Seal the challenger run: summary first, then manifest, then ZIP, then sidecar.

The ordering matters. Defect XP-001, found by the cross-paper sweep, was a summary written
after the manifest and ZIP, so the sealed archive did not contain the summary it declared.
Here the summary is written first and is therefore inside both the manifest and the archive.
All manifests are LF-only.
"""
import hashlib
import io
import json
import os
import sys
import zipfile

sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding="utf-8", errors="replace")

RUN = "C:/v14c"
PRIOR = ("C:/p3v14/02_validation/02_IA_ADVERSARIAL_AUDITS/"
         "run_2026-08-22_v1.4_residual")
ADDENDUM = f"{PRIOR}/30_REPORT/ADDENDUM_CORPUS_BOUNDED_NOVELTY.md"


def h(p):
    return hashlib.sha256(open(p, "rb").read()).hexdigest()


def walk(root):
    out = []
    for d, _, fs in os.walk(root):
        for f in sorted(fs):
            p = os.path.join(d, f).replace("\\", "/")
            out.append(os.path.relpath(p, root).replace("\\", "/"))
    return sorted(out)


def main():
    # ---- 1. summary, written first so it is inside the manifest and the archive
    summary = {
        "run": "run_2026-08-23_v1.4_challenger",
        "target": "Paper III preprint draft v1.4 (corrected)",
        "date": "2026-08-23",
        "mandate_sha256":
            "06051b3fb31ba05b36c83ddae736f108fd04a374b9765531d976d48be2919ac5",
        "instructions_zip_sha256":
            "e88cd5e8ff2a742023176a37efd642aacef0bdc66b7b6af1d9f1acb92983419e",
        "verdict": "PASS",
        "verdict_rule_applied":
            "no stronger than the weakest mandatory gate; residuals disclosed, not concealed",
        "reviews": {
            "A_EXT-V14-M01": {
                "result": "CLOSED",
                "checks": {
                    "en_es_section_2_4_equivalent": True,
                    "propagated_to_tex": True,
                    "rendered_on_pdf_page_8": True,
                    "bilingual_no_loss_or_duplication": True,
                    "es_pdf_47_pages": True,
                    "es_pdf_fonts_embedded": "13/13",
                    "es_pdf_no_clipping": True,
                    "auditor_rebuild_text_identical_pages": "47/47",
                    "auditor_log_fatal_undefined_missingchar_overfull": 0}},
            "B_EXT-V14-M02": {
                "result": "CLOSED",
                "checks_discharged": 6,
                "appendix_D_self_contained": True,
                "dependency_order_acyclic": True,
                "koenig_reproved_not_cited": True,
                "section_7_2_recomputed_from_definitions": True,
                "derived_before_opening_author_ledger": True}},
        "regression_boundary": {
            "declared_baseline_hashes_match": True,
            "declared_target_hashes_match": "6/6",
            "english_artifacts_unchanged": True,
            "spanish_artifacts_changed": 3,
            "lean_archive_unchanged": True,
            "prior_package_reverifies": "60/60",
            "prior_zip_matches_sidecar": True},
        "carry_forward": {
            "E2": "PASS on verified byte identity; corroborated by 205/205 formula agreement",
            "E6": "PASS on verified byte identity; restated in corpus-bounded form",
            "Lean": "PASS on byte-identical archive and sealed prior build logs; no rebuild"},
        "findings": [
            {"id": "EXT-V14-M01", "severity": "MINOR", "status": "CLOSED"},
            {"id": "EXT-V14-M02", "severity": "MINOR", "status": "CLOSED"},
            {"id": "EXT-V14-N01", "severity": "NOTE", "status": "OPEN_ACCEPTED"},
            {"id": "EXT-V14C-N02", "severity": "NOTE", "status": "OPEN_NEW",
             "title": "Theorem 2.2 omits 'simple' while Theorem D.3 proves the simple case"},
            {"id": "EXT-V14C-N03", "severity": "NOTE", "status": "OPEN_NEW",
             "title": "three standard steps left unstated in Appendix D"}],
        "blockers": 0, "criticals": 0, "majors": 0, "minors_open": 0, "notes_open": 3,
        "prior_report_corrected_by_addendum": {
            "path": "run_2026-08-22_v1.4_residual/30_REPORT/"
                    "ADDENDUM_CORPUS_BOUNDED_NOVELTY.md",
            "reason": "two absolute novelty formulations replaced by corpus-bounded form",
            "sealed_report_rewritten": False,
            "sealed_report_sha256":
                "2c19bf1ca74f77cc409b8d0102adf01b92d13db885ac81d15d156477abed8842"},
        "prior_conditional_pass_ground_withdrawn": {
            "ground": "no adversarial challenger had examined the package",
            "why_withdrawn": "category error: reviewer count is a property of the review "
                             "programme, not a defect of the target; conditioning closure on "
                             "a further reviewer makes external closure unreachable",
            "restated_as": "declared limitation on this review's own weight"},
        "does_not_establish": [
            "the truth of Theorem 1.1",
            "the Lean nibble chain's internal parameter ledger",
            "novelty beyond the searched corpus",
            "human peer review",
            "independence: five external runs share one reasoning context"]}

    sp = f"{RUN}/30_REPORT/FINAL_AUDIT_SUMMARY.json"
    with open(sp, "w", encoding="utf-8", newline="\n") as f:
        json.dump(summary, f, indent=1, ensure_ascii=False)
        f.write("\n")
    print(f"1. summary written first -> {os.path.relpath(sp, RUN)}")

    # ---- 1b. record the addendum filed against the sealed prior run
    if os.path.isfile(ADDENDUM):
        with open(f"{RUN}/00_CONTROL/ADDENDUM_FILED.txt", "w",
                  encoding="utf-8", newline="\n") as f:
            f.write("Addendum filed against the sealed prior external report.\n\n"
                    "path   : run_2026-08-22_v1.4_residual/30_REPORT/"
                    "ADDENDUM_CORPUS_BOUNDED_NOVELTY.md\n"
                    f"sha256 : {h(ADDENDUM)}\n"
                    "note   : the sealed report was not rewritten; its SHA-256 remains\n"
                    "         2c19bf1ca74f77cc409b8d0102adf01b92d13db885ac81d15d1"
                    "56477abed8842\n"
                    "         and the prior package still re-verifies 60/60 against its own\n"
                    "         manifest, because the addendum is filed alongside it, not "
                    "inside it.\n")
        print(f"   addendum recorded, sha256 {h(ADDENDUM)[:16]}...")

    # ---- 2. evidence manifest per directory, then the run manifest
    for sub in ("20_EVIDENCE",):
        files = [x for x in walk(f"{RUN}/{sub}") if not x.endswith("SHA256_MANIFEST.txt")]
        with open(f"{RUN}/{sub}/SHA256_MANIFEST.txt", "w",
                  encoding="utf-8", newline="\n") as f:
            for r in files:
                f.write(f"{h(f'{RUN}/{sub}/{r}')}  {r}\n")
        print(f"2. {sub}/SHA256_MANIFEST.txt: {len(files)} files")

    files = [x for x in walk(RUN)
             if not x.startswith("40_PACKAGE/")]
    man = {"run": summary["run"], "verdict": summary["verdict"],
           "file_count": len(files),
           "files": [{"path": r, "sha256": h(f"{RUN}/{r}"),
                      "bytes": os.path.getsize(f"{RUN}/{r}")} for r in files]}
    mp = f"{RUN}/40_PACKAGE/PACKAGE_MANIFEST.json"
    with open(mp, "w", encoding="utf-8", newline="\n") as f:
        json.dump(man, f, indent=1, ensure_ascii=False)
        f.write("\n")
    print(f"3. manifest: {len(files)} files")

    # ---- 3. archive, containing the manifest and the summary
    zp = f"{RUN}/40_PACKAGE/EXTERNAL_CHALLENGER_REVIEW_PACKAGE.zip"
    with zipfile.ZipFile(zp, "w", zipfile.ZIP_DEFLATED) as z:
        for r in files:
            z.write(f"{RUN}/{r}", r)
        z.write(mp, "40_PACKAGE/PACKAGE_MANIFEST.json")
    with zipfile.ZipFile(zp) as z:
        assert z.testzip() is None
        n = len(z.namelist())
    print(f"4. archive: {n} members, testzip clean")

    # ---- 4. sidecar
    zh = h(zp)
    with open(zp + ".sha256", "w", encoding="utf-8", newline="\n") as f:
        f.write(f"{zh}  {os.path.basename(zp)}\n")
    print(f"5. sidecar written")

    # ---- 5. verify every declared member against the manifest
    bad = [i["path"] for i in man["files"] if h(f"{RUN}/{i['path']}") != i["sha256"]]
    print(f"\nverification: {len(man['files']) - len(bad)}/{len(man['files'])} "
          f"files match the manifest; problems={bad or 'none'}")
    print(f"ZIP SHA-256: {zh}")
    print(f"summary inside archive: "
          f"{'30_REPORT/FINAL_AUDIT_SUMMARY.json' in zipfile.ZipFile(zp).namelist()}")
    print(f"manifest inside archive: "
          f"{'40_PACKAGE/PACKAGE_MANIFEST.json' in zipfile.ZipFile(zp).namelist()}")


if __name__ == "__main__":
    main()
