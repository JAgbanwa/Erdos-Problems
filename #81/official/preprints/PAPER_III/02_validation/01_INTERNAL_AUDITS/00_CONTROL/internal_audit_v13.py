from __future__ import annotations

import hashlib
import json
import re
import shutil
import subprocess
import zipfile
from pathlib import Path


PACKAGE = Path(__file__).resolve().parents[3]
MANUSCRIPT = PACKAGE / "01_manuscript"
FREEZE = PACKAGE / "05_formalization" / "lean_v1.3_freeze"
OUTPUT = Path(__file__).resolve().parents[1] / "20_EVIDENCE" / "G0_STATIC" / "results" / "internal_audit_static.json"
STEM = "PAPER_III_preprint_draft_v1.3"
EXPECTED_ARCHIVE_HASH = "2eb0ff20a9dae6610a46026355374570d5afdfea89837ea7f9dd29da10b9d300"
EXPECTED_MATHLIB = "8f9d9cff6bd728b17a24e163c9402775d9e6a365"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def parse_manifest(path: Path) -> list[tuple[str, str]]:
    entries = []
    for line in path.read_text(encoding="utf-8").splitlines():
        if not line.strip():
            continue
        match = re.fullmatch(r"([0-9a-fA-F]{64})\s+\*?(.+)", line)
        if not match:
            raise AssertionError(f"malformed manifest line: {path}: {line!r}")
        entries.append((match.group(1).lower(), match.group(2).strip()))
    return entries


def verify_manifest(path: Path, base: Path) -> int:
    entries = parse_manifest(path)
    for expected, relative in entries:
        target = base / Path(relative.replace("/", "\\"))
        if not target.is_file():
            raise AssertionError(f"manifest target missing: {relative}")
        if sha256(target) != expected:
            raise AssertionError(f"manifest mismatch: {relative}")
    return len(entries)


checks: dict[str, list[dict[str, object]]] = {f"G{i}": [] for i in range(9)}


def require(gate: str, condition: bool, label: str, detail: str = "") -> None:
    checks[gate].append({"pass": bool(condition), "label": label, "detail": detail})


def read(path: Path) -> str:
    return path.read_text(encoding="utf-8", errors="replace")


def command_text(args: list[str]) -> str:
    proc = subprocess.run(args, check=True, capture_output=True)
    return proc.stdout.decode("utf-8", errors="replace")


def main() -> int:
    paths = {
        "md_en": MANUSCRIPT / f"{STEM}.md",
        "tex_en": MANUSCRIPT / f"{STEM}_en.tex",
        "pdf_en": MANUSCRIPT / f"{STEM}_en.pdf",
        "md_es": MANUSCRIPT / f"{STEM}_es.md",
        "tex_es": MANUSCRIPT / f"{STEM}_es.tex",
        "pdf_es": MANUSCRIPT / f"{STEM}_es.pdf",
    }
    for name, path in paths.items():
        require("G0", path.is_file() and path.stat().st_size > 0, f"publication artifact exists: {name}")

    sidecar = MANUSCRIPT / f"{STEM}_SHA256.txt"
    require("G0", b"\r" not in sidecar.read_bytes(), "publication sidecar is LF-only")
    require("G0", verify_manifest(sidecar, MANUSCRIPT) == 6, "six publication hashes verify")
    require("G0", verify_manifest(FREEZE / "SOURCE_MANIFEST.sha256", FREEZE) == 707, "707-entry source manifest verifies")
    require("G0", verify_manifest(FREEZE / "PACKAGE_MANIFEST.sha256", FREEZE) == 742, "742-entry freeze package manifest verifies")
    archive = FREEZE / "PAPER_III_lean_v1.3_freeze.zip"
    archive_sidecar = FREEZE / "PAPER_III_lean_v1.3_freeze.zip.sha256"
    require("G0", sha256(archive) == EXPECTED_ARCHIVE_HASH, "formal archive has declared SHA-256")
    require("G0", parse_manifest(archive_sidecar)[0][0] == EXPECTED_ARCHIVE_HASH, "formal archive sidecar agrees")
    with zipfile.ZipFile(archive) as zf:
        require("G0", zf.testzip() is None, "formal archive CRC verifies")
        require("G0", len(zf.infolist()) == 743, "formal archive has 743 entries")

    en = read(paths["md_en"])
    es = read(paths["md_es"])
    combined = "\n".join(read(path) for path in paths.values() if path.suffix != ".pdf")
    for token in (
        "Theorem 1.1",
        "Corollary 1.2",
        "three regimes",
        "sharp quadratic",
        "linear term is necessary",
        "full chordal problem remains open",
    ):
        require("G1", token in en, f"English claim surface present: {token}")
    for token in (
        "Teorema 1.1",
        "Corolario 1.2",
        "tres regímenes",
        "coeficiente cuadrático afilado",
        "es necesario un término lineal",
        "problema cordal completo sigue abierto",
    ):
        require("G1", token in es, f"Spanish claim surface present: {token}")
    require("G1", "resolves the split-graph case" not in en, "overbroad split-case wording removed")
    require("G1", "resuelve el caso split" not in es and "se cierra el caso split" not in es, "Spanish overbroad split-case wording removed")
    require("G1", "determines the sharp quadratic coefficient for the split-graph case" in en, "precise split-case scope stated")

    # G2 is executed by the four independent non-Lean scripts and merged below.
    g2_summary = Path(__file__).resolve().parents[1] / "20_EVIDENCE" / "G2_MATHEMATICS" / "results" / "summary.json"
    require("G2", g2_summary.is_file(), "fresh G2 summary exists")
    if g2_summary.is_file():
        require("G2", json.loads(read(g2_summary))["status"] == "PASS", "fresh mathematical regressions pass")

    formal_surfaces = (
        "PaperIII.isFracPacking_iff_yuster",
        "PaperIII.nu3Star_eq_yuster",
        "PaperIII.tau3Star_eq_nu3Star",
        "PaperIII.AX1Assumption_iff_packing_form",
        "Nibble.AX1.boxAllocationResidual_holds",
        "Nibble.AX1.blockCoverResidualCoupled_holds",
        "Nibble.AX1.ax1_of_boxAllocation",
        "Nibble.AX1.ax1Statement_holds",
        "PaperIII.AX1_holds",
        "PaperIII.E_4_3_of_AX1",
        "PaperIII.E_5_1",
        "PaperIII.cor_5_3",
        "PaperIII.E_5_2",
        "PaperIII.Prop_10_1_low",
        "PaperIII.Prop_10_1_mid",
        "PaperIII.E_8_clique_packing_of_AX2",
        "PaperIII.E_8_of_AX1_AX2",
        "PaperIII.AX2_holds",
        "PaperIII.eventual_bound_of_high_degree_of_AX1_AX2",
        "PaperIII.global_bound_from_eventual_high_degree",
        "PaperIII.Theorem_1_1_of_AX1_AX2",
        "PaperIII.Theorem_1_1",
    )
    all_lean = "\n".join(read(path) for path in FREEZE.rglob("*.lean"))
    axiom_sources = "\n".join(read(path) for path in FREEZE.glob("FreezeAxioms*.lean"))
    axiom_outputs = "\n".join(read(path) for path in (FREEZE / "gate_logs").glob("AXIOMS_*.txt"))
    for surface in formal_surfaces:
        require("G3", surface.split(".")[-1] in all_lean, f"formal declaration occurs in source: {surface}")
        require("G3", surface in axiom_sources, f"formal surface explicitly queried: {surface}")
        require("G3", surface in axiom_outputs, f"formal surface recorded in axiom output: {surface}")
    require("G3", "import PaperIII.CanonicalTrianglePacking" in read(FREEZE / "PaperIII.lean"), "aggregate root imports canonical module")
    require("G3", "import PaperIII.CanonicalTrianglePacking" in read(FREEZE / "PaperIII" / "PublicAPI.lean"), "PublicAPI imports canonical module")

    build_log = read(FREEZE / "gate_logs" / "BUILD_LOG_FINAL_INCREMENTAL.txt")
    build_exit = read(FREEZE / "gate_logs" / "BUILD_EXIT_FINAL_INCREMENTAL.txt")
    require("G4", "exit_code=0" in build_exit.lower(), "recorded consolidated build exit is zero")
    require("G4", "Build completed successfully (8719 jobs)" in build_log, "recorded build reports 8719 successful jobs")
    require("G4", "warning: declaration uses 'sorry'" not in build_log, "recorded build has no active sorry warning")
    summary = json.loads(read(FREEZE / "gate_logs" / "AXIOM_CHECK_SUMMARY.json"))
    require("G4", summary["overall_exit_code"] == 0 and len(summary["checks"]) == 8, "all eight axiom query files exited zero")
    seen = set()
    for footprint in re.findall(r"depends on axioms:\s*\[([^\]]*)\]", axiom_outputs):
        seen.update(item.strip() for item in footprint.split(",") if item.strip())
    require("G4", seen == ALLOWED_AXIOMS, "recorded theorem footprints are exactly foundational-only", str(sorted(seen)))
    require("G4", "Two real project-local axioms remain in archived legacy modules" in read(FREEZE / "ESCAPE_HATCH_ASSESSMENT.md"), "legacy project axioms are disclosed and classified")
    imports = "\n".join(line for path in FREEZE.rglob("*.lean") for line in read(path).splitlines() if line.lstrip().startswith("import "))
    require("G4", "Ax2.PartA.Wlog" not in imports and "Ax2.PartB.Axioms" not in imports, "legacy axiom modules are unimported")
    require("G4", "draft v1.1" not in axiom_sources.lower(), "stale v1.1 axiom-file label absent")

    consistency = json.loads(read(PACKAGE / "03_reproducibility" / "MANUSCRIPT_CONSISTENCY_RESULTS.json"))
    require("G5", consistency["verdict"] == "PASS", "Markdown/TeX/PDF consistency suite passes")
    require("G5", consistency["heading_counts"] == {"en": 144, "es": 144}, "English/Spanish heading counts agree")
    require("G5", en.count("A_{2,J}") == 0 and en.count("A_{2J}") == 4, "English A_2J notation is normalized")
    require("G5", en.count("[3,8]") == es.count("[3,8]") == 2, "combined citation [3,8] is synchronized")
    require("G5", en.count("[11,17]") == es.count("[11,17]") == 2, "combined citation [11,17] is synchronized")

    final_logs = {
        lang: PACKAGE / "03_reproducibility" / "manuscript_build_logs" / f"LUALATEX_v1.3_FINAL_{lang}.log"
        for lang in ("en", "es")
    }
    for lang in ("en", "es"):
        pdf = paths[f"pdf_{lang}"]
        tex = paths[f"tex_{lang}"]
        pdfinfo = command_text([shutil.which("pdfinfo") or "pdfinfo", str(pdf)])
        fonts = command_text([shutil.which("pdffonts") or "pdffonts", str(pdf)])
        rows = [line for line in fonts.splitlines()[2:] if line.strip()]
        expected_pages = 45 if lang == "en" else 46
        require("G6", f"Pages:           {expected_pages}" in pdfinfo, f"{lang} PDF page count is {expected_pages}")
        require("G6", rows and all(re.search(r"\byes\s+yes\s", line) for line in rows), f"{lang} PDF fonts are embedded")
        log = read(final_logs[lang])
        require("G6", not re.search(r"(?m)^!", log), f"{lang} final TeX log has no fatal error")
        require("G6", "undefined references" not in log and "undefined citations" not in log, f"{lang} final TeX log has no undefined reference/citation")
        require("G6", pdf.stat().st_mtime_ns >= tex.stat().st_mtime_ns, f"{lang} PDF does not predate TeX")
    require("G6", not list(MANUSCRIPT.rglob("*.aux")) and not list(MANUSCRIPT.rglob("*.log")), "manuscript tree has no TeX residue")

    reference_count = len(re.findall(r"(?m)^\[(\d+)\]\s", en))
    require("G7", reference_count == 17, "English bibliography has 17 numbered references")
    require("G7", "Internal prior-art and novelty assessment." in en, "bounded internal novelty statement present")
    require("G7", "not a substitute for independent prior-art review" in en, "independent novelty gate remains explicit")
    require("G7", "full chordal problem remains open" in en, "full chordal problem distinguished from split asymptotic result")

    delivery_roots = [
        PACKAGE / "01_manuscript",
        PACKAGE / "02_validation",
        PACKAGE / "03_reproducibility",
        PACKAGE / "04_integrity",
        FREEZE,
    ]
    stray_shell_dirs = [
        path for root in delivery_roots for path in root.rglob("*")
        if path.is_dir() and path.name.startswith("$")
    ]
    require("G8", not stray_shell_dirs, "no shell-variable-named directory exists")
    require("G8", not (PACKAGE / "tmp").exists(), "temporary render tree removed")
    require("G8", not list(FREEZE.rglob("*.olean")) and not list(FREEZE.rglob("*.ilean")), "public freeze contains no compiled Lean artifacts")
    require("G8", not any(path.is_symlink() for path in FREEZE.rglob("*")), "public freeze contains no symlink/reparse entry")
    require("G8", "first formal public release" in en and "primera liberación pública formal" in es, "Paper III first-release status synchronized")
    require("G8", "preprint_draft_v1.2" not in combined and "PAPER_III_preprint_draft_v1.2" not in combined, "manuscripts do not depend on prior version artifacts")

    gate_verdicts = {
        gate: "PASS" if all(item["pass"] for item in entries) else "FAIL"
        for gate, entries in checks.items()
    }
    failed = {gate: [item for item in entries if not item["pass"]] for gate, entries in checks.items() if any(not item["pass"] for item in entries)}
    result = {
        "paper": "PAPER_III",
        "target": "preprint_draft_v1.3",
        "audit_class": "INTERNAL_AUTHOR_SIDE_NON_INDEPENDENT",
        "lean_rebuild_during_audit": False,
        "gate_verdicts": gate_verdicts,
        "checks_passed": sum(item["pass"] for entries in checks.values() for item in entries),
        "checks_total": sum(len(entries) for entries in checks.values()),
        "failed": failed,
        "overall": "PASS" if not failed else "FAIL",
        "checks": checks,
    }
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    OUTPUT.write_text(json.dumps(result, indent=2, ensure_ascii=False) + "\n", encoding="utf-8", newline="\n")
    print(json.dumps(result, indent=2, ensure_ascii=False))
    return 0 if result["overall"] == "PASS" else 1


if __name__ == "__main__":
    raise SystemExit(main())
