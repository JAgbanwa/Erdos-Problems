"""Validate the bilingual artifact identity; this is not an internal mathematical audit."""
from pathlib import Path
import difflib
import hashlib
import json
import re
import sys

ROOT = Path(__file__).resolve().parent
PAPER = ROOT.parent.parent
sys.path.insert(0, "C:/Users/jtraverso/.cache/e81-editorial-tools/python-libs")
import pymupdf
from assemble_bilingual import mask
from check_bilingual import report as parity

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def read_json(p):
    return json.loads(p.read_text(encoding="utf-8"))

base = ROOT / "review_history/before-bilingual-20260929/PAPER_IV_preprint_v1.2_en.md"
en = ROOT / "PAPER_IV_preprint_v1.2_en.md"
old, new = base.read_text(encoding="utf-8"), en.read_text(encoding="utf-8")
# Only the two exact evidence locators may change; no mathematical token is normalized.
normalize = lambda s: s.replace("build_piv-stability-fe9bb18343da/SOURCE_MANIFEST.json",
                               "build_piv-v12-fb459343d234/SOURCE_MANIFEST.json").replace(
                               "`03_reproducibility/build_piv-v12-fb459343d234/`",
                               "`03_reproducibility/full_rebuild_v12_20260929_resume/`")
checks = {
    "approved_english_input": sha(base) == "7881b035b73cac09ad84da55090002788cd7da8cae238baa0c742ed6d71f5298",
    "protected_inline_display_and_code": list(map(normalize, mask(old)[1])) == mask(new)[1],
    "bilingual_blocks": parity["block_counts"][0] == parity["block_counts"][1],
    "bilingual_math_code": not parity["math_and_code_mismatches"],
    "bilingual_headings": parity["headings_match"],
    "bilingual_equation_labels": parity["equation_labels_match"],
    "bilingual_figures": parity["image_counts"] == [4, 4],
    "status_not_english_only": not parity["english_only_metadata_remaining"],
}
fence = chr(96) * 3
checks["five_literal_lean_blocks"] = re.findall(fence + r"lean\n.*?" + fence, old, re.S) == re.findall(fence + r"lean\n.*?" + fence, new, re.S)
(ROOT / "BILINGUAL_APPROVED_EN.diff").write_text("".join(difflib.unified_diff(
    old.splitlines(True), new.splitlines(True), fromfile=str(base.relative_to(ROOT)),
    tofile=en.name)), encoding="utf-8")

freeze = read_json(PAPER / "04_integrity/FREEZE_piv-v12-fb459343d234.json")
evidence = PAPER / "03_reproducibility/build_piv-v12-fb459343d234"
manifest_path = evidence / "SOURCE_MANIFEST.json"
source = PAPER / "05_formalization/lean_piv-v12-fb459343d234"
sources = read_json(manifest_path)
source_bad = [x["path"] for x in sources if not (source / x["path"]).is_file()
              or sha(source / x["path"]) != x["sha256"]]
evidence_bad = [x["path"] for x in read_json(evidence / "EVIDENCE_MANIFEST.json")
                if not (evidence / x["path"]).is_file()
                or sha(evidence / x["path"]) != x["sha256"]]
summary = read_json(evidence / "combined/SUMMARY.json")
results = read_json(evidence / "combined/RESULTS.json")
checks.update({
    "source_manifest": sha(manifest_path) == freeze["manifest_sha256"],
    "source_files": not source_bad and len(sources) == 615,
    "source_archive": sha(Path(freeze["archive"])) == freeze["archive_sha256"],
    "recorded_evidence_files": not evidence_bad,
    "recorded_build_complete": summary == freeze["build_summary"],
    "recorded_build_exit": (evidence / "combined/BUILD.exit").read_text().strip() == "EXIT_CODE=0",
    "recorded_modules_complete": len(results) == 607 and all(r["status"] in ("PASS", "UP-TO-DATE") for r in results),
    "recorded_targets_executed": {r["module"] for r in results if r["status"] == "PASS"} == set(freeze["targets"]),
})
fresh_evidence = PAPER / '03_reproducibility/full_rebuild_v12_20260929_seal'
fresh_seal = read_json(fresh_evidence / 'EVIDENCE_SEAL.json')
fresh_manifest = read_json(fresh_evidence / 'EVIDENCE_MANIFEST.json')
fresh_bad = [r['path'] for r in fresh_manifest['files']
             if sha(PAPER / '03_reproducibility' / r['path']) != r['sha256']]
checks.update({
    'full_reconstruction_seal': fresh_seal['status'] == 'PASS_LOCAL_RECORDED_BUILD_REVALIDATION',
    'full_reconstruction_manifest': sha(fresh_evidence / 'EVIDENCE_MANIFEST.json') == fresh_seal['manifest_sha256'],
    'full_reconstruction_evidence_unchanged': not fresh_bad,
    'full_reconstruction_archive': sha(Path(fresh_seal['archive'])) == fresh_seal['archive_sha256'],
    'full_reconstruction_scope': fresh_seal['unique_fresh_modules'] == 607 and fresh_seal['export_checks'] == 224
        and fresh_seal['axiom_records'] == 461 and len(fresh_seal['targets']) == 19,
})
revision = {}
for lang in ('en', 'es'):
    name = f'PAPER_IV_preprint_v1.2_{lang}.md'
    prior_path = ROOT / 'review_history/before-full-rebuild-reseal' / name
    current_path = ROOT / name
    prior, current = prior_path.read_text(encoding='utf-8'), current_path.read_text(encoding='utf-8')
    a, b = prior.splitlines(), current.splitlines()
    changed = [i for i, (x, y) in enumerate(zip(a, b), 1) if x != y]
    checks[lang + '_only_authorized_status_and_build_edits'] = len(a) == len(b) and changed == [11, 1179]
    checks[lang + '_mathematical_displays_preserved'] = re.findall(r'\\\[.*?\\\]', prior, re.S) == re.findall(r'\\\[.*?\\\]', current, re.S)
    revision[lang] = {'input_sha256': sha(prior_path), 'output_sha256': sha(current_path),
                      'changed_lines': changed, 'allowed_edit': 'Formal evidence/status prose and evidence locator only'}
    (ROOT / f'FULL_REBUILD_RESEAL_{lang.upper()}.diff').write_text(''.join(difflib.unified_diff(
        prior.splitlines(True), current.splitlines(True), fromfile=str(prior_path.relative_to(ROOT)),
        tofile=name)), encoding='utf-8')
artifacts = {}
for lang in ("en", "es"):
    stem = f"PAPER_IV_preprint_v1.2_{lang}"
    md, tex, pdf = [ROOT / (stem + ext) for ext in (".md", ".tex", ".pdf")]
    log = (ROOT / (stem + ".log")).read_text(encoding="utf-8")
    console = (ROOT / ("compiler_console_en.log" if lang == "en" else "compiler_console.log")).read_text(encoding="utf-8")
    t = tex.read_text(encoding="utf-8")
    d = pymupdf.open(pdf)
    checks[lang + "_compiler_output"] = stem + ".pdf" in console and "Running xdvipdfmx" in console
    checks[lang + "_two_tex_passes"] = "Rerunning TeX because I was told to" in console
    checks[lang + "_no_fatal_or_overflow"] = not re.search(r"Overfull|Missing character|Undefined control sequence|undefined references|^! ", log, re.M)
    checks[lang + "_fresh_pdf"] = pdf.stat().st_mtime >= tex.stat().st_mtime >= md.stat().st_mtime
    checks[lang + "_renders_bound"] = (ROOT / f"qa_{lang}/pdf_sha256.txt").read_text().strip() == sha(pdf)
    checks[lang + "_four_figures"] = t.count(r"\begin{figure}") == 4 and t.count(r"\caption{") == 4
    checks[lang + "_page_renders"] = all((ROOT / f"qa_{lang}/page_{i+1:02d}.png").is_file() for i in range(len(d)))
    artifacts[lang] = {
        "pages": len(d), "md_sha256": sha(md), "tex_sha256": sha(tex), "pdf_sha256": sha(pdf),
        "underfull_warnings": log.count("Underfull"),
        "fontconfig_environment_notice": "Fontconfig error" in console,
        "all_pdf_fonts_embedded_or_type3_charprocs": all(
            bool(d.extract_font(font[0])[3]) if font[2] != "Type3"
            else d.xref_get_key(font[0], "CharProcs")[0] in ("dict", "xref")
            for p in d for font in p.get_fonts()),
    }
report = {
    "scope": "Editorial artifact validation and existing-source identity; no new Lean build or internal/adversarial audit.",
    "status": "PASS_ARTIFACT_CHECKS" if all(checks.values()) else "FAIL",
    "checks": checks, "artifacts": artifacts,
    "english_displays": len(re.findall(r"\\\[", new)),
    "literal_lean_blocks": len(re.findall(fence + "lean", new)),
    "source_freeze": freeze["freeze_id"], "source_mismatches": source_bad,
    "recorded_evidence_mismatches": evidence_bad,
    "full_reconstruction_evidence_mismatches": fresh_bad,
    "full_reconstruction_seal_sha256": sha(fresh_evidence / 'EVIDENCE_SEAL.json'),
    "authorized_revision": revision,
    "mathematical_audit": "PENDING", "publication": "NOT_AUTHORIZED",
}
(ROOT / "ARTIFACT_CHECKS.json").write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
print(json.dumps(report, ensure_ascii=False, indent=2))
raise SystemExit(0 if all(checks.values()) else 1)
