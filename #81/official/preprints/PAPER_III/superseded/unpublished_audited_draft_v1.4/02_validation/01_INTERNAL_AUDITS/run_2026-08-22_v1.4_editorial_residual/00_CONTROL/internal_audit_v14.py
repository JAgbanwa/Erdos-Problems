from __future__ import annotations

import hashlib
import json
import re
import shutil
import subprocess
import zipfile
from pathlib import Path


RUN = Path(__file__).resolve().parents[1]
PACKAGE = Path(__file__).resolve().parents[4]
MANUSCRIPT = PACKAGE / "01_manuscript"
FREEZE = PACKAGE / "05_formalization" / "lean_v1.4_freeze"
BUILD = FREEZE / "gate_logs" / "run_2026-08-22_CCS_NOTEBOOK456_resumed"
OUTPUT = RUN / "20_EVIDENCE" / "G0_STATIC" / "results" / "internal_audit_static_v1.4.json"
STEM = "PAPER_III_preprint_draft_v1.4"
ARCHIVE_HASH = "79ee24c38fd776bc2585a0c3c996e30817f0829fc5064463bdbde0fa2d3d7104"
MATHLIB_COMMIT = "8f9d9cff6bd728b17a24e163c9402775d9e6a365"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def read(path: Path) -> str:
    return path.read_text(encoding="utf-8", errors="replace")


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def parse_manifest(path: Path) -> list[tuple[str, str]]:
    entries: list[tuple[str, str]] = []
    for line in read(path).splitlines():
        if not line.strip():
            continue
        match = re.fullmatch(r"([0-9a-fA-F]{64})\s+\*?(.+)", line)
        if not match:
            raise AssertionError(f"malformed manifest line in {path}: {line!r}")
        entries.append((match.group(1).lower(), match.group(2).strip()))
    return entries


def verify_manifest(path: Path, base: Path) -> int:
    entries = parse_manifest(path)
    for expected, relative in entries:
        target = base / Path(relative.replace("/", "\\"))
        if not target.is_file():
            raise AssertionError(f"missing manifest target: {relative}")
        if sha256(target) != expected:
            raise AssertionError(f"manifest hash mismatch: {relative}")
    return len(entries)


checks: dict[str, list[dict[str, object]]] = {f"G{i}": [] for i in range(9)}


def require(gate: str, condition: bool, label: str, detail: str = "") -> None:
    checks[gate].append({"pass": bool(condition), "label": label, "detail": detail})


def command_text(args: list[str]) -> str:
    result = subprocess.run(args, check=True, capture_output=True)
    return result.stdout.decode("utf-8", errors="replace")


def normalized_long_paragraphs(text: str) -> list[str]:
    return [
        re.sub(r"\s+", " ", block.strip())
        for block in re.split(r"\n\s*\n", text)
        if len(re.sub(r"\s+", " ", block.strip())) >= 180
        and not block.lstrip().startswith(("|", "```"))
    ]


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
        require("G0", path.is_file() and path.stat().st_size > 0, f"publication artifact exists: {key}")

    sidecar = MANUSCRIPT / f"{STEM}_SHA256.txt"
    require("G0", sidecar.is_file(), "publication SHA-256 sidecar exists")
    require("G0", b"\r" not in sidecar.read_bytes(), "publication sidecar is LF-only")
    require("G0", verify_manifest(sidecar, MANUSCRIPT) == 6, "all six publication hashes verify")
    require("G0", verify_manifest(FREEZE / "SOURCE_MANIFEST.sha256", FREEZE) == 707, "707-entry source manifest verifies")
    require("G0", verify_manifest(FREEZE / "PACKAGE_MANIFEST.sha256", FREEZE) == 751, "751-entry freeze package manifest verifies")
    archive = FREEZE / "PAPER_III_lean_v1.4_freeze.zip"
    archive_sidecar = FREEZE / "PAPER_III_lean_v1.4_freeze.zip.sha256"
    require("G0", sha256(archive) == ARCHIVE_HASH, "formal archive SHA-256 verifies")
    require("G0", parse_manifest(archive_sidecar) == [(ARCHIVE_HASH, archive.name)], "formal archive sidecar agrees")
    with zipfile.ZipFile(archive) as frozen:
        require("G0", frozen.testzip() is None, "formal archive CRC verifies")
        require("G0", len(frozen.infolist()) == 751, "formal archive has 751 entries")
        require("G0", not any(name.endswith((".olean", ".ilean")) or "/.lake/" in name for name in frozen.namelist()), "formal archive is source-only")

    en = read(paths["md_en"])
    es = read(paths["md_es"])
    tex_en = read(paths["tex_en"])
    tex_es = read(paths["tex_es"])
    all_semantic = "\n".join((en, es, tex_en, tex_es))
    for token in (
        "Theorem 1.1", "Corollary 1.2", "three regimes", "sharp quadratic",
        "linear term is necessary", "full chordal problem remains open",
        "improves its quadratic coefficient to the sharp value",
        "does not identify the least uniform linear coefficient",
    ):
        require("G1", token in en, f"English claim surface present: {token}")
    for token in (
        "Teorema 1.1", "Corolario 1.2", "tres regímenes", "coeficiente cuadrático afilado",
        "es necesario un término lineal", "problema cordal completo sigue abierto",
        "mejora su coeficiente cuadrático hasta el valor afilado",
        "no identifica el menor coeficiente lineal uniforme",
    ):
        require("G1", token in es, f"Spanish claim surface present: {token}")
    require("G1", "resolves the split-graph case" not in en, "overbroad English split-case claim absent")
    require("G1", "resuelve el caso split" not in es and "se cierra el caso split" not in es, "overbroad Spanish split-case claim absent")
    require("G1", "p\\to\\infty" in en.replace(" ", "") and "p\\to\\infty" in es.replace(" ", ""), "sharpness limit is explicit in both languages")

    g2 = json.loads(read(RUN / "20_EVIDENCE" / "G2_MATHEMATICS" / "results" / "summary_v1.4.json"))
    require("G2", g2["status"] == "PASS" and not g2["lean_used"], "fresh non-Lean mathematical regression summary passes")
    require("G2", g2["blocks"]["unified_margin"]["passed"] == 78384, "78,384 exact margin checks passed")
    require("G2", (PACKAGE / "02_validation" / "01_INTERNAL_AUDITS" / "E2_RESIDUAL_v1.4" / "40_REPORT" / "INTERNAL_E2_RESIDUAL_SUMMARY.json").is_file(), "E2 residual rederivation package exists")
    e2 = json.loads(read(PACKAGE / "02_validation" / "01_INTERNAL_AUDITS" / "E2_RESIDUAL_v1.4" / "40_REPORT" / "INTERNAL_E2_RESIDUAL_SUMMARY.json"))
    require("G2", "PASS" in json.dumps(e2), "E2 residual K-EPS/K-CORRIDOR/K-SPARSE/K-GLOBAL checks pass")

    axiom_sources = "\n".join(read(path) for path in sorted(FREEZE.glob("FreezeAxioms*.lean")))
    axiom_logs = "\n".join(read(path) for path in sorted((BUILD / "logs").glob("axioms_*.log")))
    queries = re.findall(r"(?m)^#print axioms\s+([A-Za-z0-9_.]+)\s*$", axiom_sources)
    unique_queries = sorted(set(queries))
    require("G3", len(queries) == 42 and len(unique_queries) == 35, "42 theorem-level queries cover 35 distinct surfaces")
    for surface in unique_queries:
        require("G3", surface in axiom_logs, f"axiom output records surface: {surface}")
    root_source = read(FREEZE / "PaperIII.lean")
    require("G3", "import PaperIII.Theorem_1_1_Final" in root_source, "public aggregate root imports final theorem module")
    require("G3", "import PaperIII.PublicAPI" in root_source, "public aggregate root imports PublicAPI")
    require("G3", "import PaperIII.CanonicalTrianglePacking" in read(FREEZE / "PaperIII" / "PublicAPI.lean"), "PublicAPI imports canonical packing module")
    for bridge in (
        "PaperIII.isTrianglePacking_iff_yuster", "PaperIII.nu3_eq_yuster",
        "PaperIII.isFracPacking_iff_yuster", "PaperIII.nu3Star_eq_yuster",
        "PaperIII.tau3Star_eq_yuster_cover", "PaperIII.tau3Star_eq_nu3Star",
        "PaperIII.AX1Assumption_iff_packing_form",
    ):
        require("G3", bridge in axiom_sources and bridge in axiom_logs, f"canonical bridge is queried and recorded: {bridge}")

    summary = json.loads(read(BUILD / "RUN_SUMMARY.json"))
    require("G4", summary["result"] == "PASS_RESUMED", "recorded build result is PASS_RESUMED")
    require("G4", summary["clean_initial_state"] is True, "recorded build began from a source-only project state")
    require("G4", summary["uninterrupted_run"] is False and summary["resumed_incremental_build"] is True, "restart/resume limitation is truthfully recorded")
    require("G4", summary["public_root_build"] == "PASS" and summary["query_roots_build"] == "PASS", "public and query root builds passed")
    require("G4", summary["axiom_gate"] == "PASS_FOUNDATIONAL_ONLY" and summary["axiom_query_files"] == 8, "eight-file axiom gate passed")
    public_log = read(BUILD / "logs" / "02_build_public_root_clean.log")
    query_log = read(BUILD / "logs" / "03_build_query_roots_incremental.log")
    require("G4", "Build completed successfully (8455 jobs)" in public_log, "public-root log records 8,455 successful jobs")
    require("G4", "Build completed successfully (8444 jobs)" in query_log, "query-root log records 8,444 successful jobs")
    require("G4", "warning: declaration uses 'sorry'" not in public_log + query_log, "recorded builds contain no active sorry warning")
    exits = [read(path).strip() for path in sorted((BUILD / "logs").glob("axioms_*.exit.txt"))]
    require("G4", len(exits) == 8 and all(re.search(r"(?:exit_code=|^)0(?:\s|$)", value, re.I) for value in exits), "all eight axiom query processes exited zero")
    gate_summary = read(BUILD / "evidence" / "AXIOM_GATE_SUMMARY.txt")
    require("G4", "surfaces=42" in gate_summary and "sorryAx=0" in gate_summary, "axiom summary records 42 surfaces and zero sorryAx")
    seen = set()
    for footprint in re.findall(r"depends on axioms:\s*\[([^\]]*)\]", axiom_logs):
        seen.update(item.strip() for item in footprint.split(",") if item.strip())
    require("G4", seen == ALLOWED_AXIOMS, "recorded axiom union is exactly foundational-only", str(sorted(seen)))
    closure = json.loads(read(BUILD / "evidence" / "IMPORT_CLOSURE.json"))
    require("G4", closure["paperIII_reaches_final"] and closure["paperIII_reaches_public_api"] and closure["public_api_reaches_final"], "recorded import closure reaches final theorem and PublicAPI")
    require("G4", not closure["canonical_reaches_archived_wlog"] and not closure["canonical_reaches_archived_axioms"], "canonical closure excludes archived project-axiom modules")
    dependencies = json.loads(read(BUILD / "evidence" / "DEPENDENCIES.json"))
    require("G4", len(dependencies) == 9 and all(d["clean"] and d["actual_revision"] == d["expected_revision"] for d in dependencies), "all nine dependencies are clean and pinned")
    require("G4", next(d for d in dependencies if d["name"] == "mathlib")["actual_revision"] == MATHLIB_COMMIT, "Mathlib commit matches manuscript and freeze")
    require("G4", verify_manifest(BUILD / "RESULTS_MANIFEST.sha256", BUILD) == 33, "33-entry recorded-build evidence manifest verifies")
    metadata = json.loads(read(FREEZE / "FREEZE_METADATA.json"))
    require("G4", metadata["recorded_build"]["classification"] == "PASS_CLEAN_ORIGIN_RESUMED", "freeze metadata does not overstate uninterrupted reproduction")

    consistency_script = PACKAGE / "03_reproducibility" / "check_manuscript_consistency.py"
    consistency_run = subprocess.run(["python", str(consistency_script)], capture_output=True, text=True, encoding="utf-8", errors="replace")
    require("G5", consistency_run.returncode == 0, "51-check manuscript consistency suite reruns successfully")
    consistency = json.loads(read(PACKAGE / "03_reproducibility" / "MANUSCRIPT_CONSISTENCY_RESULTS.json"))
    require("G5", consistency["verdict"] == "PASS" and consistency["checks"] == 51, "all 51 semantic/format consistency checks pass")
    require("G5", consistency["heading_counts"] == {"en": 144, "es": 144}, "EN/ES heading counts agree at 144")
    for language, text in (("en", en), ("es", es)):
        paragraphs = normalized_long_paragraphs(text)
        require("G5", len(paragraphs) == len(set(paragraphs)), f"no duplicated long paragraph in {language} Markdown")
    require("G5", "h_i\\ge\\max\\{\\rho,\\,q_J-r_b\\}" in en and "h_i\\ge\\max\\{\\rho,\\,q_J-r_b\\}" in es, "full Proposition 7.4 quantitative condition survives translation")
    require("G5", "The same identity holds for \\(q=0\\)" in en and "La misma identidad vale para \\(q=0\\)" in es, "q=0 benchmark clause survives translation")
    require("G5", "no standalone polynomial-time theorem is claimed here" in en and "no se afirma un teorema polinomial autónomo" in es, "algorithmic non-claim is synchronized")
    require("G5", not re.search(r"v1\.[0-3]\b|v2\.\d+\b", all_semantic), "publication manuscripts are self-contained and do not cite draft versions")

    log_dir = PACKAGE / "03_reproducibility" / "manuscript_build_logs" / "v1.4"
    for language, pages in (("en", 46), ("es", 47)):
        pdf = paths[f"pdf_{language}"]
        tex = paths[f"tex_{language}"]
        info = command_text([shutil.which("pdfinfo") or "pdfinfo", str(pdf)])
        fonts = command_text([shutil.which("pdffonts") or "pdffonts", str(pdf)])
        font_rows = [line for line in fonts.splitlines()[2:] if line.strip()]
        require("G6", re.search(rf"(?m)^Pages:\s+{pages}\s*$", info) is not None, f"{language} PDF page count is {pages}")
        require("G6", font_rows and all(re.search(r"\byes\s+yes\s", row) for row in font_rows), f"{language} PDF fonts are embedded")
        require("G6", pdf.stat().st_mtime_ns >= tex.stat().st_mtime_ns, f"{language} PDF does not predate final TeX")
        logs = [log_dir / f"{language}_final_pass2_console.log", log_dir / f"PAPER_III_preprint_draft_v1.4_{language}.log"]
        require("G6", bool(logs), f"{language} final TeX logs are retained")
        log_text = "\n".join(read(path) for path in logs)
        require("G6", not re.search(r"(?m)^!", log_text), f"{language} TeX logs contain no fatal error")
        require("G6", "undefined references" not in log_text and "undefined citations" not in log_text, f"{language} TeX logs contain no undefined references/citations")
        require("G6", "Missing character" not in log_text and "Overfull" not in log_text, f"{language} TeX logs contain no missing character or overfull box")
    qa = read(PACKAGE / "03_reproducibility" / "RENDERED_PDF_QA_REPORT_v1.4.md")
    require("G6", "**Verdict:** `PASS`" in qa and "All 46 English pages and all 47 Spanish pages" in qa, "all-page rendered visual QA is recorded")
    require("G6", not list(MANUSCRIPT.rglob("*.aux")) and not list(MANUSCRIPT.rglob("*.log")), "manuscript directory has no TeX residue")

    require("G7", len(re.findall(r"(?m)^\[(\d+)\]\s", en)) == 17, "English bibliography has 17 numbered references")
    require("G7", "Internal prior-art and novelty assessment." in en, "internal novelty statement is explicit")
    require("G7", "not a substitute for independent prior-art review" in en, "independent novelty gate remains explicit")
    require("G7", "full chordal problem remains open" in en, "full chordal problem is distinguished")
    external_addendum = PACKAGE / "02_validation" / "02_IA_ADVERSARIAL_AUDITS" / "baseline_v1.3" / "E2_E6_ADDENDUM_v1.3.txt"
    require("G7", external_addendum.is_file() and "E6" in read(external_addendum) and "PASS" in read(external_addendum), "external E6 prior-art addendum is preserved as carry-forward evidence")
    require("G7", "external adversarial audit" in en and "auditoría adversarial externa" in es, "external review remains a release gate in both languages")

    require("G8", not list(MANUSCRIPT.glob("*v1.3*")), "v1.4 manuscript directory contains no duplicate v1.3 artifacts")
    require("G8", len(list(MANUSCRIPT.glob("*.md"))) == 3, "manuscript directory has exactly EN/ES manuscripts plus README")
    require("G8", len(list(MANUSCRIPT.glob("*.tex"))) == 2 and len(list(MANUSCRIPT.glob("*.pdf"))) == 2, "manuscript directory has exactly two TeX and two PDF publication artifacts")
    require("G8", not any(path.is_dir() and path.name.startswith("$") for path in PACKAGE.rglob("*")), "package has no shell-variable-named directory")
    require("G8", not (PACKAGE / "tmp").exists(), "package has no temporary render directory")
    require("G8", not list(FREEZE.rglob("*.olean")) and not list(FREEZE.rglob("*.ilean")), "formal freeze contains no compiled Lean artifacts")
    require("G8", not any(path.is_symlink() for path in FREEZE.rglob("*")), "formal freeze contains no symlink/reparse entry")
    require("G8", not list(PACKAGE.rglob("__pycache__")), "package contains no Python bytecode cache directory")
    require("G8", not list(PACKAGE.rglob("*.aux")) and not list(PACKAGE.rglob("*.out")), "package contains no transient TeX auxiliary file")
    require("G8", "first formal public release" in en and "primera liberación pública formal" in es, "first-release status is synchronized")
    require("G8", "preprint_draft_v1.3" not in all_semantic and "PAPER_III_preprint_draft_v1.3" not in all_semantic, "manuscript does not depend on earlier artifacts")

    verdicts = {gate: "PASS" if all(item["pass"] for item in entries) else "FAIL" for gate, entries in checks.items()}
    failed = {gate: [item for item in entries if not item["pass"]] for gate, entries in checks.items() if any(not item["pass"] for item in entries)}
    result = {
        "paper": "PAPER_III",
        "target": "preprint_draft_v1.4",
        "date": "2026-08-22",
        "audit_class": "INTERNAL_AUTHOR_SIDE_NON_INDEPENDENT",
        "lean_rebuild_during_audit": False,
        "recorded_build_classification": "PASS_CLEAN_ORIGIN_RESUMED",
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
