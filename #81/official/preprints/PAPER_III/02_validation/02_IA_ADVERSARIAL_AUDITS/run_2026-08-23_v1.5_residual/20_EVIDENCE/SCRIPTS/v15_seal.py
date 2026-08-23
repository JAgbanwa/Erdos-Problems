#!/usr/bin/env python3
"""Seal the v1.5 external residual audit run.

Order matters: summary first, then per-directory manifests, then the package manifest, then
the ZIP, then the sidecar. Defect XP-001 from the cross-paper sweep was a summary written
after the manifest and ZIP, so the archive did not contain the summary it declared.
"""
import hashlib
import io
import json
import os
import shutil
import sys
import zipfile

sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding="utf-8", errors="replace")

RUN = "C:/v15r"
TOOLS = "C:/erdos_audit/tools"
VIS = "C:/erdos_audit/v15/render/visual"
MINE = "C:/erdos_audit/v15/render"

SCRIPTS = ["v15_E0_intake.py", "v15_E1_delta.py", "v15_E1_sections.py", "v15_E3_formal.py",
           "v15_E3_probe.py", "v15_E5_bilingual.py", "v15_E5_render.py", "v15_E6_E7.py",
           "v15_stale_sweep.py", "v15_seal.py"]


def h(p):
    return hashlib.sha256(open(p, "rb").read()).hexdigest()


def walk(root, skip_prefix=()):
    out = []
    for d, _, fs in os.walk(root):
        for f in sorted(fs):
            r = os.path.relpath(os.path.join(d, f), root).replace("\\", "/")
            if any(r.startswith(s) for s in skip_prefix):
                continue
            out.append(r)
    return sorted(out)


def main():
    # ---- collect scripts, visual evidence and the auditor's own build logs
    sd = f"{RUN}/20_EVIDENCE/SCRIPTS"
    os.makedirs(sd, exist_ok=True)
    for s in SCRIPTS:
        if os.path.isfile(f"{TOOLS}/{s}"):
            shutil.copy2(f"{TOOLS}/{s}", f"{sd}/{s}")
    vd = f"{RUN}/20_EVIDENCE/E5_RENDER/visual"
    os.makedirs(vd, exist_ok=True)
    for f in sorted(os.listdir(VIS)):
        if f.endswith(".png"):
            shutil.copy2(f"{VIS}/{f}", f"{vd}/{f}")
    for lang in ("en", "es"):
        p = f"{MINE}/{lang}.log"
        if os.path.isfile(p):
            shutil.copy2(p, f"{RUN}/20_EVIDENCE/E5_RENDER/auditor_rebuild_{lang}.log")
    print(f"collected {len(SCRIPTS)} scripts, "
          f"{len([f for f in os.listdir(vd)])} visual evidence files")

    # ---- 1. summary first
    summary = {
        "run": "run_2026-08-23_v1.5_residual",
        "target": "Paper III preprint v1.5 (first formal public preprint)",
        "date": "2026-08-23",
        "request_sha256":
            "75c82bd4cbb027408218bcc8e758ebc96b70c9fb0297544ba6f7394a76f1931c",
        "instructions_zip_sha256":
            "e6a1445330ff8d602313fd2e7e6bdf00d1fba0ce2be052b23e1174c0e49f225c",
        "verdict": "CONDITIONAL_PASS",
        "verdict_reason": "E0-E7 pass and both clarifications close on their mathematics; "
                          "one open MINOR (EXT-V15-M01), non-mathematical, with owner and "
                          "closure test stated",
        "gates": {"E0": "PASS", "E1": "PASS", "E2": "PASS_CARRIED_FORWARD",
                  "E3": "PASS", "E4": "PASS_CARRIED_FORWARD_NO_REBUILD",
                  "E5": "PASS", "E6": "PASS_CARRIED_FORWARD", "E7": "PASS"},
        "E0": {"manuscript_hashes_matched": "6/6", "lean_zip_matched": True,
               "lean_zip_members": 751, "lean_zip_source_only": True,
               "sidecar_lf_only": True, "authorities_matched": "6/6",
               "challenger_authority_byte_identical_to_auditor_copy": True,
               "only_v1_5_active": True, "v1_4_preserved_under_superseded": True},
        "E1": {"changed_hunks_per_language": 14,
               "unclassified_changes": 0,
               "hunks_in_mathematical_core": 0,
               "hunks_in_appendix_D": 2,
               "displayed_formula_sequence_identical": True,
               "equation_tag_sequence_identical": True,
               "citation_sequence_identical": True,
               "heading_sequence_identical": True,
               "bibliography_entries": {"v1_4": 17, "v1_5": 17, "identical": True},
               "clarifications_present_all_languages": True,
               "release_claims_about_external_audit_verified": True},
        "E3": {"source_manifest_entries": 707, "package_manifest_entries": 751,
               "archive_vs_manifest_exact_key": "751/751",
               "identical_to_preserved_v1_4_freeze": True,
               "axiom_query_logs": 8, "axiom_queries": 42,
               "distinct_axiom_surfaces": 35, "sorryAx": 0,
               "footprint_outlier": {
                   "constant": "PaperIII.isTrianglePacking_iff_yuster",
                   "axioms": ["propext", "Quot.sound"],
                   "note": "strict subset of the expected footprint; stronger, not weaker"}},
        "E4": {"rebuild_performed": False,
               "prior_v1_4_residual_package_reverify": "60/60",
               "prior_v1_4_challenger_package_reverify": "24/24"},
        "E5": {"pages": {"en": 46, "es": 47},
               "fonts_non_embedded": {"en": 0, "es": 0},
               "author_blocks_per_pdf": 1, "authorblock_placeholder_tokens": 0,
               "pdf_author_metadata": "Juan Pablo Traverso Gianini",
               "pages_with_margin_ink": {"en": 0, "es": 0},
               "auditor_rebuild_text_identical_pages": {"en": "46/46", "es": "47/47"},
               "auditor_rebuild_fatal_undefined_missingchar_overfull": 0,
               "clarification_layer_language_combinations_confirmed": "30/30",
               "bilingual_structural_loss_or_duplication": False},
        "E6": {"bibliography_identical": True, "citation_sequence_identical": True,
               "bounded_statement_retained_both_languages": True,
               "full_chordal_stated_open_both_languages": True,
               "human_peer_review_disclaimed_both_languages": True,
               "absolute_priority_claims_found": 0,
               "bounded_statement": "No published integral upper bound for split graphs at "
                                    "or below n^2/6 + O(n) was identified in the searched "
                                    "corpus."},
        "E7": {"surfaces_present": 7, "all_reference_v1_5": True,
               "quoted_hashes_resolving": "4/4", "broken_local_links": 0,
               "html_scope_and_disclosure_ok": True,
               "framed_as_first_public_preprint": True,
               "claims_superseding_a_public_release": False,
               "v1_4_evidence_preserved_unrewritten": True},
        "findings": [
            {"id": "EXT-V14C-N02", "severity": "NOTE", "status": "CLOSED",
             "title": "Theorem 2.2 now states 'simple bipartite graph'"},
            {"id": "EXT-V14C-N03", "severity": "NOTE", "status": "CLOSED",
             "title": "three standard Appendix D steps now stated"},
            {"id": "EXT-V15-M01", "severity": "MINOR", "status": "OPEN",
             "title": "generically-named stale evidence copies shadow the current ones",
             "instances": [
                 "03_reproducibility/manuscript_build_logs/LUALATEX_FINAL_{en,es}.log and "
                 "LUALATEX_{en,es}_PASS{1,2}.txt are v1.3 artifacts (45/46 pages, 2 overfull) "
                 "shadowing manuscript_build_logs/v1.5/ (46/47 pages, clean)",
                 "03_reproducibility/MANUSCRIPT_CONSISTENCY_RESULTS.json records the v1.4 "
                 "English markdown hash eea753a4..., alongside the correct "
                 "MANUSCRIPT_CONSISTENCY_RESULTS_v1.5.json recording a98e9313..."],
             "owner": "author",
             "closure_test": "no file in 03_reproducibility/ outside a v1.3/v1.4-labelled "
                             "path names a non-v1.5 artifact or quotes a non-v1.5 hash"}],
        "blockers": 0, "criticals": 0, "majors": 0,
        "minors_open": 1, "notes_open": 0,
        "auditor_tool_false_positives_corrected_during_run": 6,
        "does_not_establish": [
            "the truth of Theorem 1.1",
            "the Lean nibble chain's internal parameter ledger",
            "novelty beyond the searched corpus; no priority determination",
            "human peer review",
            "independence: five external runs share one reasoning context, and this auditor "
            "raised the two findings whose fixes it has now reviewed"]}

    sp = f"{RUN}/30_REPORT/FINAL_AUDIT_SUMMARY.json"
    with open(sp, "w", encoding="utf-8", newline="\n") as f:
        json.dump(summary, f, indent=1, ensure_ascii=False)
        f.write("\n")
    print("1. summary written first")

    # ---- 2. per-evidence-directory manifests
    ev = f"{RUN}/20_EVIDENCE"
    for sub in sorted(os.listdir(ev)):
        d = f"{ev}/{sub}"
        if not os.path.isdir(d):
            continue
        files = [x for x in walk(d) if not x.endswith("SHA256_MANIFEST.txt")]
        with open(f"{d}/SHA256_MANIFEST.txt", "w", encoding="utf-8", newline="\n") as f:
            for r in files:
                f.write(f"{h(f'{d}/{r}')}  {r}\n")
        print(f"   {sub}/SHA256_MANIFEST.txt: {len(files)} files")
    files = [x for x in walk(ev) if not x.endswith("SHA256_MANIFEST.txt")]
    with open(f"{ev}/SHA256_MANIFEST.txt", "w", encoding="utf-8", newline="\n") as f:
        for r in files:
            f.write(f"{h(f'{ev}/{r}')}  {r}\n")
    print(f"2. 20_EVIDENCE/SHA256_MANIFEST.txt: {len(files)} files")

    # ---- 3. package manifest
    allf = walk(RUN, skip_prefix=("40_PACKAGE/",))
    man = {"run": summary["run"], "verdict": summary["verdict"],
           "file_count": len(allf),
           "files": [{"path": r, "sha256": h(f"{RUN}/{r}"),
                      "bytes": os.path.getsize(f"{RUN}/{r}")} for r in allf]}
    mp = f"{RUN}/40_PACKAGE/PACKAGE_MANIFEST.json"
    with open(mp, "w", encoding="utf-8", newline="\n") as f:
        json.dump(man, f, indent=1, ensure_ascii=False)
        f.write("\n")
    print(f"3. package manifest: {len(allf)} files")

    # ---- 4. archive
    zp = f"{RUN}/40_PACKAGE/PAPER_III_v1.5_EXTERNAL_RESIDUAL_AUDIT.zip"
    with zipfile.ZipFile(zp, "w", zipfile.ZIP_DEFLATED) as z:
        for r in allf:
            z.write(f"{RUN}/{r}", r)
        z.write(mp, "40_PACKAGE/PACKAGE_MANIFEST.json")
    with zipfile.ZipFile(zp) as z:
        assert z.testzip() is None
        names = z.namelist()
    print(f"4. archive: {len(names)} members, CRC clean")

    # ---- 5. sidecar
    zh = h(zp)
    with open(zp + ".sha256", "w", encoding="utf-8", newline="\n") as f:
        f.write(f"{zh}  {os.path.basename(zp)}\n")

    # ---- 6. verification
    bad = [i["path"] for i in man["files"] if h(f"{RUN}/{i['path']}") != i["sha256"]]
    print(f"\nverification: {len(man['files']) - len(bad)}/{len(man['files'])} files match "
          f"the manifest; problems={bad or 'none'}")
    print(f"summary in archive : {'30_REPORT/FINAL_AUDIT_SUMMARY.json' in names}")
    print(f"report in archive  : {'30_REPORT/FINAL_AUDIT_REPORT.md' in names}")
    print(f"ledger in archive  : {'10_LEDGER/FINDINGS_LEDGER.csv' in names}")
    print(f"manifest in archive: {'40_PACKAGE/PACKAGE_MANIFEST.json' in names}")
    print(f"\nZIP SHA-256: {zh}")


if __name__ == "__main__":
    main()
