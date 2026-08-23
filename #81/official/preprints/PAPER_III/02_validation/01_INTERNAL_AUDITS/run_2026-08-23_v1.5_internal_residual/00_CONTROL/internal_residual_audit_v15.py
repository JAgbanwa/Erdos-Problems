from __future__ import annotations

import hashlib
import json
import re
import shutil
import subprocess
import zipfile
from collections import Counter
from pathlib import Path


RUN = Path(__file__).resolve().parents[1]
PACKAGE = Path(__file__).resolve().parents[4]
MANUSCRIPT = PACKAGE / "01_manuscript"
FREEZE = PACKAGE / "05_formalization" / "lean_v1.4_freeze"
BASELINE = PACKAGE / "superseded" / "unpublished_audited_draft_v1.4"
BASELINE_MANUSCRIPT = BASELINE / "01_manuscript"
BASELINE_FREEZE = BASELINE / "05_formalization" / "lean_v1.4_freeze"
OUTPUT = RUN / "20_EVIDENCE" / "internal_residual_results_v1.5.json"
STEM = "PAPER_III_preprint_v1.5"
ARCHIVE_HASH = "79ee24c38fd776bc2585a0c3c996e30817f0829fc5064463bdbde0fa2d3d7104"


def read(path: Path) -> str:
    return path.read_text(encoding="utf-8", errors="replace")


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def parse_manifest(path: Path) -> list[tuple[str, str]]:
    entries = []
    for line in read(path).splitlines():
        if not line.strip():
            continue
        match = re.fullmatch(r"([0-9a-fA-F]{64})\s+\*?(.+)", line)
        if not match:
            raise AssertionError(f"malformed manifest line: {line!r}")
        entries.append((match.group(1).lower(), match.group(2).strip()))
    return entries


def verify_manifest(path: Path, base: Path) -> bool:
    for expected, relative in parse_manifest(path):
        target = base / Path(relative.replace("/", "\\"))
        if not target.is_file() or sha256(target) != expected:
            return False
    return True


def normalized_displays(text: str) -> list[str]:
    blocks = re.findall(r"\$\$(.*?)\$\$|\\\[(.*?)\\\]", text, re.S)
    return [re.sub(r"\s+", "", left or right) for left, right in blocks]


def equation_tags(text: str) -> list[str]:
    return re.findall(r"\\tag\{([^}]+)\}", text)


def headings(text: str) -> list[tuple[int, str]]:
    return [(len(level), title.strip()) for level, title in re.findall(r"(?m)^(#{1,6})\s+(.+)$", text)]


def citations(text: str) -> list[str]:
    return re.findall(r"\[(\d+(?:\s*[-,]\s*\d+)*)\]", text)


def long_paragraphs(text: str) -> list[str]:
    return [
        re.sub(r"\s+", " ", block.strip())
        for block in re.split(r"\n\s*\n", text)
        if len(re.sub(r"\s+", " ", block.strip())) >= 180
        and not block.lstrip().startswith(("|", "```"))
    ]


checks: dict[str, list[dict[str, object]]] = {f"G{i}": [] for i in range(9)}


def require(gate: str, condition: bool, label: str, detail: str = "") -> None:
    checks[gate].append({"pass": bool(condition), "label": label, "detail": detail})


def command(args: list[str]) -> str:
    result = subprocess.run(args, check=True, capture_output=True)
    return result.stdout.decode("utf-8", errors="replace")


def main() -> int:
    paths = {
        "md_en": MANUSCRIPT / f"{STEM}.md",
        "tex_en": MANUSCRIPT / f"{STEM}_en.tex",
        "pdf_en": MANUSCRIPT / f"{STEM}_en.pdf",
        "md_es": MANUSCRIPT / f"{STEM}_es.md",
        "tex_es": MANUSCRIPT / f"{STEM}_es.tex",
        "pdf_es": MANUSCRIPT / f"{STEM}_es.pdf",
    }
    for key, path in paths.items():
        require("G0", path.is_file() and path.stat().st_size > 0, f"v1.5 artifact exists: {key}")
    sidecar = MANUSCRIPT / f"{STEM}_SHA256.txt"
    require("G0", sidecar.is_file(), "v1.5 six-artifact sidecar exists")
    require("G0", sidecar.is_file() and b"\r" not in sidecar.read_bytes(), "v1.5 sidecar is LF-only")
    require("G0", len(parse_manifest(sidecar)) == 6 and verify_manifest(sidecar, MANUSCRIPT), "all six v1.5 hashes verify")
    require("G0", not list(MANUSCRIPT.glob("*draft*")), "active manuscript directory contains no draft-named artifact")

    en, es = read(paths["md_en"]), read(paths["md_es"])
    base_en = read(BASELINE_MANUSCRIPT / "PAPER_III_preprint_draft_v1.4.md")
    base_es = read(BASELINE_MANUSCRIPT / "PAPER_III_preprint_draft_v1.4_es.md")
    require("G1", normalized_displays(en) == normalized_displays(base_en), "English displayed mathematics is unchanged from audited v1.4")
    require("G1", normalized_displays(es) == normalized_displays(base_es), "Spanish displayed mathematics is unchanged from audited v1.4")
    require("G1", equation_tags(en) == equation_tags(base_en) and equation_tags(es) == equation_tags(base_es), "equation-tag sequences are unchanged")
    require("G1", headings(en) == headings(base_en) and headings(es) == headings(base_es), "heading and theorem order is unchanged")
    require("G1", Counter(citations(en)) == Counter(citations(base_en)) and Counter(citations(es)) == Counter(citations(base_es)), "citation-reference multisets are unchanged")
    for token in (
        "simple bipartite graph with maximum degree",
        "remaining digraph is an induced subdigraph of",
        "bipartite graphs of maximum degree at most",
        "subgraph formed by the \\(\\alpha\\)- and \\(\\beta\\)-colored edges has maximum degree at most two",
        "well-defined simple path",
    ):
        require("G1", token in en, f"English N02/N03 clarification present: {token}")
    for token in (
        "grafo bipartito simple de grado máximo",
        "digrafo restante es un subdigrafo inducido de",
        "grafos bipartitos de grado máximo a lo sumo",
        "subgrafo formado por las aristas de colores \\(\\alpha\\) y \\(\\beta\\) tiene grado máximo a lo sumo dos",
        "camino simple bien definido",
    ):
        require("G1", token in es, f"Spanish N02/N03 clarification present: {token}")
    integrity = read(PACKAGE / "04_integrity" / "SEMANTIC_INTEGRITY_REPORT_v1.5.md")
    require("G1", "Unresolved content queries:** none" in integrity and "EDITORIALLY_READY" in integrity, "semantic-integrity report closes without content query")

    prior_internal = read(PACKAGE / "02_validation" / "01_INTERNAL_AUDITS" / "run_2026-08-22_v1.4" / "10_REPORT" / "INTERNAL_AUDIT_FINAL_REPORT.md")
    prior_external = read(PACKAGE / "02_validation" / "02_IA_ADVERSARIAL_AUDITS" / "run_2026-08-23_v1.4_challenger" / "30_REPORT" / "FINAL_AUDIT_REPORT.md")
    require("G2", "Overall verdict:** `PASS`" in prior_internal and "144/144" in prior_internal, "v1.4 full internal audit PASS is preserved")
    require("G2", "> **`PASS`**" in prior_external, "v1.4 final external challenger PASS is preserved")
    require("G2", "E2 — `PASS`" in prior_external and "Sections 4–9" in prior_external, "external E2 rederivation PASS is preserved")
    require("G2", "EXT-V14C-N02" in prior_external and "EXT-V14C-N03" in prior_external, "external origin and NOTE classification of v1.5 clarifications are preserved")

    archive = FREEZE / "PAPER_III_lean_v1.4_freeze.zip"
    archive_sidecar = FREEZE / "PAPER_III_lean_v1.4_freeze.zip.sha256"
    require("G3", sha256(archive) == ARCHIVE_HASH, "Lean archive hash remains the audited v1.4 hash")
    require("G3", parse_manifest(archive_sidecar) == [(ARCHIVE_HASH, archive.name)], "Lean archive sidecar agrees")
    with zipfile.ZipFile(archive) as frozen:
        require("G3", frozen.testzip() is None and len(frozen.infolist()) == 751, "Lean archive CRC and 751-entry count verify")
        require("G3", not any("/.lake/" in n or n.endswith((".olean", ".ilean")) for n in frozen.namelist()), "Lean archive remains source-only")
    source_manifest = FREEZE / "SOURCE_MANIFEST.sha256"
    package_manifest = FREEZE / "PACKAGE_MANIFEST.sha256"
    require("G3", len(parse_manifest(source_manifest)) == 707 and verify_manifest(source_manifest, FREEZE), "707-entry Lean source manifest verifies")
    require("G3", len(parse_manifest(package_manifest)) == 751 and verify_manifest(package_manifest, FREEZE), "751-entry Lean package manifest verifies")
    same_sources = True
    for expected, relative in parse_manifest(source_manifest):
        archived = BASELINE_FREEZE / Path(relative.replace("/", "\\"))
        active = FREEZE / Path(relative.replace("/", "\\"))
        if not archived.is_file() or sha256(archived) != expected or sha256(active) != expected:
            same_sources = False
            break
    require("G3", same_sources, "every manifested Lean source is byte-identical to the preserved audited v1.4 source")

    external_run = PACKAGE / "02_validation" / "02_IA_ADVERSARIAL_AUDITS" / "run_2026-08-22_v1.4_residual"
    require("G4", (external_run / "30_REPORT" / "FINAL_AUDIT_REPORT.md").is_file(), "independent external clean-room report is present")
    external_report = read(external_run / "30_REPORT" / "FINAL_AUDIT_REPORT.md")
    require("G4", "8,455" in external_report and "8,444" in external_report, "external build job counts are recorded")
    require("G4", "42" in external_report and "35" in external_report and "sorryAx" in external_report, "external axiom-surface closure is recorded")
    require("G4", "uninterrupted" in external_report.lower(), "external uninterrupted-run classification is recorded")
    author_clean = PACKAGE / "03_reproducibility" / "author_build_evidence" / "run_2026-08-23_clean_PASS" / "README.md"
    require("G4", author_clean.is_file() and "PASS" in read(author_clean), "separate clean author reproduction is preserved")
    require("G4", True, "Lean was not rebuilt in the v1.5 internal residual", "static identity review only")

    consistency_script = PACKAGE / "03_reproducibility" / "check_manuscript_consistency.py"
    rerun = subprocess.run(["python", str(consistency_script)], capture_output=True, text=True, encoding="utf-8", errors="replace")
    consistency_path = PACKAGE / "03_reproducibility" / "MANUSCRIPT_CONSISTENCY_RESULTS_v1.5.json"
    consistency = json.loads(read(consistency_path))
    require("G5", rerun.returncode == 0, "v1.5 consistency suite reruns successfully")
    require("G5", consistency["verdict"] == "PASS" and consistency["checks"] == 61, "all 61 v1.5 consistency checks pass")
    require("G5", consistency["heading_counts"] == {"en": 144, "es": 144}, "bilingual heading counts agree at 144")
    for language, text in (("English", en), ("Spanish", es)):
        paragraphs = long_paragraphs(text)
        require("G5", len(paragraphs) == len(set(paragraphs)), f"no duplicated long paragraph in {language} Markdown")
    require("G5", "full chordal problem remains open" in en and "problema cordal completo sigue abierto" in es, "split-case scope and open chordal boundary are synchronized")
    require("G5", "reviewed corpus" in en and "corpus revisado" in es, "novelty claims remain corpus-bounded in both languages")

    log_dir = PACKAGE / "03_reproducibility" / "manuscript_build_logs" / "v1.5"
    render_dir = PACKAGE / "03_reproducibility" / "manuscript_render_qa_v1.5"
    for language, pages in (("en", 46), ("es", 47)):
        pdf, tex = paths[f"pdf_{language}"], paths[f"tex_{language}"]
        info = command([shutil.which("pdfinfo") or "pdfinfo", str(pdf)])
        fonts = command([shutil.which("pdffonts") or "pdffonts", str(pdf)])
        font_rows = [line for line in fonts.splitlines()[2:] if line.strip()]
        require("G6", re.search(rf"(?m)^Pages:\s+{pages}\s*$", info) is not None, f"{language} PDF has {pages} pages")
        require("G6", font_rows and all(re.search(r"\byes\s+yes\s", row) for row in font_rows), f"{language} PDF fonts are embedded and subset")
        require("G6", pdf.stat().st_mtime_ns >= tex.stat().st_mtime_ns, f"{language} PDF does not predate delivered TeX")
        log = read(log_dir / f"LUALATEX_FINAL_{language}.log")
        require("G6", "Output written on" in log and not re.search(r"(?m)^!", log), f"{language} final compiler log identifies output and has no fatal error")
        require("G6", not re.search(r"undefined references|undefined citations|Missing character|Overfull", log, re.I), f"{language} final compiler log has no prohibited diagnostic")
        require("G6", len(list((render_dir / language).glob("page-*.png"))) == pages, f"all {pages} {language} pages were rendered")
    qa = read(PACKAGE / "03_reproducibility" / "RENDERED_PDF_QA_REPORT_v1.5.md")
    require("G6", "**Verdict:** `PASS`" in qa and "All 46 English pages and all 47 Spanish pages" in qa, "all-page visual QA is recorded")
    require("G6", not list(MANUSCRIPT.glob("*.aux")) and not list(MANUSCRIPT.glob("*.log")), "manuscript directory contains no TeX residue")

    require("G7", "E6 — `PASS`" in prior_external and "searched corpus" in prior_external, "external E6 prior-art PASS uses corpus-bounded language")
    require("G7", "3/16" in en and "1/6" in en and "3/16" in es and "1/6" in es, "prior split bound and sharp coefficient are stated in both languages")
    require("G7", "not human peer-reviewed" in en and "sin revisión humana por pares" in es, "human-peer-review limitation is explicit")
    require("G7", "split-graph case" in en and "accompanying Lean 4 / Mathlib development" in en and "full chordal problem remains open" in en, "formal split-case positioning is precise")

    active_names = sorted(p.name for p in MANUSCRIPT.iterdir() if p.is_file())
    expected_names = sorted([
        "PAPER_III_preprint_v1.5.md", "PAPER_III_preprint_v1.5_en.tex", "PAPER_III_preprint_v1.5_en.pdf",
        "PAPER_III_preprint_v1.5_es.md", "PAPER_III_preprint_v1.5_es.tex", "PAPER_III_preprint_v1.5_es.pdf",
        "PAPER_III_preprint_v1.5_SHA256.txt", "README.md",
    ])
    require("G8", active_names == expected_names, "active manuscript directory contains exactly the v1.5 target and README", str(active_names))
    require("G8", not (PACKAGE / "DRAFT_METADATA.yml").exists() and not (PACKAGE / "DRAFT_NOTES.md").exists(), "active package contains no draft metadata")
    require("G8", not (PACKAGE / "CHANGELOG_v1.5_PROPOSED.md").exists() and not (PACKAGE / "RELEASE_PREPARATION_v1.5.md").exists(), "active package contains no provisional v1.5 control file")
    require("G8", 'version: "1.5"' in read(PACKAGE / "CITATION.cff") and "version = {1.5}" in read(PACKAGE / "CITATION.bib"), "citation metadata names v1.5")
    html = read(PACKAGE / "PaperIII_explained_4_levels.html")
    require("G8", "v1.5" in html and "split-graph case" in html and "full chordal problem remains open" in html, "HTML explainer has current version and precise scope")
    hrefs = re.findall(r'href=["\']([^"\']+)["\']', html)
    broken = []
    for href in hrefs:
        if href.startswith(("http://", "https://", "mailto:", "#")):
            continue
        target = PACKAGE / href.split("#", 1)[0]
        if not target.exists():
            broken.append(href)
    require("G8", not broken, "all local HTML links resolve", str(broken))
    root_readme = read(PACKAGE / "README.md")
    require("G8", "Audit continuity from v1.4 to v1.5" in root_readme and "CHANGELOG_v1.5.md" in root_readme, "release README explains audit continuity and links the changelog")
    generic_logs = sorted(path.name for path in (PACKAGE / "03_reproducibility" / "manuscript_build_logs").iterdir() if path.is_file())
    require("G8", not generic_logs, "no generic compiler log shadows the versioned v1.5 logs", str(generic_logs))
    require("G8", not (PACKAGE / "03_reproducibility" / "MANUSCRIPT_CONSISTENCY_RESULTS.json").exists(), "no generic consistency result shadows the v1.5 result")
    current_logs = sorted((PACKAGE / "03_reproducibility" / "manuscript_build_logs" / "v1.5").glob("*"))
    require("G8", len(current_logs) == 6 and all("PAPER_III_preprint_v1.5" in read(path) for path in current_logs), "all six current compiler logs are version-scoped and name v1.5")
    legacy_logs = sorted((PACKAGE / "03_reproducibility" / "manuscript_build_logs" / "v1.3_legacy").glob("*"))
    require("G8", len(legacy_logs) == 29 and all("v1.3" in read(path) for path in legacy_logs), "historical v1.3 logs are preserved only in an explicitly labelled path")

    verdicts = {gate: "PASS" if all(item["pass"] for item in entries) else "FAIL" for gate, entries in checks.items()}
    failed = {gate: [item for item in entries if not item["pass"]] for gate, entries in checks.items() if any(not item["pass"] for item in entries)}
    result = {
        "paper": "PAPER_III",
        "target": "preprint_v1.5",
        "date": "2026-08-23",
        "audit_class": "INTERNAL_AUTHOR_SIDE_RESIDUAL_NON_INDEPENDENT",
        "lean_rebuild_during_audit": False,
        "baseline": "unpublished externally audited v1.4",
        "gate_verdicts": verdicts,
        "checks_passed": sum(bool(item["pass"]) for entries in checks.values() for item in entries),
        "checks_total": sum(len(entries) for entries in checks.values()),
        "failed": failed,
        "overall": "PASS" if not failed else "FAIL",
        "checks": checks,
    }
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    OUTPUT.write_text(json.dumps(result, indent=2, ensure_ascii=False) + "\n", encoding="utf-8", newline="\n")
    print(json.dumps(result, indent=2, ensure_ascii=True))
    return 0 if result["overall"] == "PASS" else 1


if __name__ == "__main__":
    raise SystemExit(main())
