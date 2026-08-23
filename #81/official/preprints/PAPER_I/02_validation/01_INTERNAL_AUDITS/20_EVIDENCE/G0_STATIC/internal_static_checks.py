from __future__ import annotations

import argparse
import hashlib
import json
import re
import shutil
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
POPPLER = Path(
    r"C:\Users\jtrav\AppData\Local\Microsoft\WinGet\Packages\oschwartz10612.Poppler_Microsoft.Winget.Source_8wekyb3d8bbwe\poppler-25.07.0\Library\bin"
)
PAPERS = {
    "I": "PAPER_I",
    "II": "PAPER_II",
    "III": "PAPER_III",
}

FREEZE_VERSIONS = {
    "PAPER_I": "1.2",
    "PAPER_II": "1.2",
    "PAPER_III": "1.2",
}


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def parse_manifest(path: Path) -> list[tuple[str, str]]:
    entries: list[tuple[str, str]] = []
    for line in path.read_text(encoding="utf-8").splitlines():
        if not line.strip():
            continue
        match = re.fullmatch(r"([0-9a-fA-F]{64})\s+\*?(.+)", line)
        if not match:
            raise AssertionError(f"malformed manifest line in {path.name}: {line!r}")
        entries.append((match.group(1).lower(), match.group(2).strip()))
    return entries


def verify_manifest(path: Path, base: Path) -> int:
    count = 0
    for expected, relative in parse_manifest(path):
        target = base / Path(relative.replace("/", "\\"))
        if not target.is_file():
            raise AssertionError(f"manifest target missing: {relative}")
        actual = sha256(target)
        if actual != expected:
            raise AssertionError(f"manifest mismatch: {relative}")
        count += 1
    return count


def headings(text: str) -> list[int]:
    return [len(match.group(1)) for match in re.finditer(r"(?m)^(#{1,6})\s+.+$", text)]


def figures(text: str) -> list[str]:
    return re.findall(r"!\[[^\]]*\]\(([^)]+\.(?:png|svg|pdf))\)", text, re.I)


def normalized_figure(path: str) -> str:
    return path.replace("_en.", "_LANG.").replace("_es.", "_LANG.")


def identifiers(text: str) -> set[str]:
    values = re.findall(r"`([^`\n]+)`", text)
    return {
        value
        for value in values
        if re.fullmatch(r"[A-Za-z][A-Za-z0-9_.:*#/-]+", value)
        and ("_" in value or "." in value or value.startswith(("Paper", "Contrib", "Byproduct")))
    }


def run_text(command: list[str]) -> str:
    result = subprocess.run(command, check=True, capture_output=True)
    return result.stdout.decode("utf-8", errors="replace")


def poppler_tool(name: str) -> str:
    found = shutil.which(name) or shutil.which(f"{name}.exe")
    if found:
        return found
    fallback = POPPLER / f"{name}.exe"
    if fallback.is_file():
        return str(fallback)
    raise FileNotFoundError(f"Poppler tool not found: {name}")


def pdf_pages(pdf: Path) -> int:
    text = run_text([poppler_tool("pdfinfo"), str(pdf)])
    match = re.search(r"(?m)^Pages:\s+(\d+)", text)
    if not match:
        raise AssertionError(f"page count missing: {pdf.name}")
    return int(match.group(1))


def embedded_fonts(pdf: Path) -> bool:
    text = run_text([poppler_tool("pdffonts"), str(pdf)])
    rows = [line for line in text.splitlines()[2:] if line.strip()]
    return bool(rows) and all(re.search(r"\byes\s+yes\s", line) for line in rows)


def pdf_text(pdf: Path) -> str:
    return run_text([poppler_tool("pdftotext"), "-enc", "UTF-8", str(pdf), "-"])


def require(condition: bool, label: str, checks: list[str]) -> None:
    if not condition:
        raise AssertionError(label)
    checks.append(label)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--paper", choices=PAPERS, required=True)
    parser.add_argument("--draft-version", default="1.2")
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--log", type=Path, required=True)
    args = parser.parse_args()

    paper = PAPERS[args.paper]
    draft_version = args.draft_version
    package = ROOT / paper / "active" / f"preprint_draft_v{draft_version}"
    manuscript = package / "01_manuscript"
    freeze_version = FREEZE_VERSIONS[paper]
    freeze = package / "05_formalization" / f"lean_v{freeze_version}_freeze"
    stem = f"{paper}_preprint_draft_v{draft_version}"
    paths = {
        "en_md": manuscript / f"{stem}.md",
        "es_md": manuscript / f"{stem}_es.md",
        "en_tex": manuscript / f"{stem}_en.tex",
        "es_tex": manuscript / f"{stem}_es.tex",
        "en_pdf": manuscript / f"{stem}_en.pdf",
        "es_pdf": manuscript / f"{stem}_es.pdf",
    }
    checks: list[str] = []

    for name, path in paths.items():
        require(path.is_file() and path.stat().st_size > 0, f"artifact present: {name}", checks)

    artifact_manifest = manuscript / f"{stem}_SHA256.txt"
    require(b"\r" not in artifact_manifest.read_bytes(), "artifact manifest is LF-only", checks)
    artifact_count = verify_manifest(artifact_manifest, manuscript)
    require(artifact_count == 6, "artifact manifest contains exactly six publication artifacts", checks)
    checks.append(f"artifact manifest verified: {artifact_count} entries")
    source_count = verify_manifest(freeze / "SOURCE_MANIFEST.sha256", freeze)
    checks.append(f"source manifest verified: {source_count} entries")
    package_count = verify_manifest(freeze / "PACKAGE_MANIFEST.sha256", freeze)
    checks.append(f"package manifest verified: {package_count} entries")

    zip_file = freeze / f"{paper}_lean_v{freeze_version}_freeze.zip"
    zip_sidecar = freeze / f"{paper}_lean_v{freeze_version}_freeze.zip.sha256"
    zip_expected = parse_manifest(zip_sidecar)[0][0]
    require(sha256(zip_file) == zip_expected, "freeze archive sidecar verified", checks)

    metadata = json.loads((freeze / "FREEZE_METADATA.json").read_text(encoding="utf-8"))
    require(metadata["paper"] == paper, "freeze metadata paper matches", checks)
    require(metadata["draft_version"] == freeze_version, "freeze metadata version matches its formal freeze", checks)
    audit_status = metadata.get("audit_status", metadata.get("internal_audit", ""))
    require(audit_status in {"NOT_STARTED", "INTERNAL_PASS", "PENDING_V1_2_FULL_RERUN"}, "freeze audit status is recognized", checks)

    build_exit = (freeze / "gate_logs" / "BUILD_EXIT.txt").read_text(encoding="utf-8")
    build_log = (freeze / "gate_logs" / "BUILD_LOG.txt").read_text(encoding="utf-8", errors="replace")
    axiom_exit = (freeze / "gate_logs" / "AXIOMS_EXIT.txt").read_text(encoding="utf-8")
    axioms = (freeze / "gate_logs" / "AXIOMS_REPORT.txt").read_text(encoding="utf-8", errors="replace")
    require("EXIT_CODE=0" in build_exit, "recorded build exit is zero", checks)
    require("Build completed successfully" in build_log, "recorded build log reports success", checks)
    require("EXIT_CODE=0" in axiom_exit or axiom_exit.strip() == "0", "recorded axiom gate exit is zero", checks)
    require("sorryAx" not in axioms, "recorded axiom report contains no sorryAx", checks)
    allowed_axioms = {"propext", "Classical.choice", "Quot.sound"}
    seen_axioms: set[str] = set()
    for footprint in re.findall(r"depends on axioms:\s*\[([^\]]*)\]", axioms):
        seen_axioms.update(item.strip() for item in footprint.split(",") if item.strip())
    require(bool(seen_axioms) and seen_axioms <= allowed_axioms, "recorded axiom footprints are foundational-only", checks)

    if paper == "PAPER_II":
        supplement_exit = (freeze / "gate_logs" / "BUILD_SUPPLEMENT_EXIT.txt").read_text(encoding="utf-8")
        supplement_log = (freeze / "gate_logs" / "BUILD_SUPPLEMENT_EXTREMIZER_COPYDEFECT.txt").read_text(encoding="utf-8", errors="replace")
        require("EXIT_CODE=0" in supplement_exit, "recorded supplement build exit is zero", checks)
        require("Build completed successfully" in supplement_log, "recorded supplement build reports success", checks)
    if paper == "PAPER_III":
        require("warning: declaration uses 'sorry'" not in build_log, "recorded build has no active sorry warning", checks)
        assessment = (freeze / "ESCAPE_HATCH_ASSESSMENT.md").read_text(encoding="utf-8")
        require("block comments" in assessment or "block-commented" in assessment, "historical sorry tokens are assessed", checks)

    en = paths["en_md"].read_text(encoding="utf-8")
    es = paths["es_md"].read_text(encoding="utf-8")
    combined = "\n".join((en, es, paths["en_tex"].read_text(encoding="utf-8"), paths["es_tex"].read_text(encoding="utf-8")))
    allowed_version_tokens = {f"v{draft_version}", f"v{freeze_version}"}
    prior_version_tokens = sorted(set(re.findall(r"\bv(?:0|1|2)\.\d+\b", combined)) - allowed_version_tokens)
    require(not prior_version_tokens, "manuscripts contain no prior-version narrative or paths", checks)
    require(f"preprint_draft_v{freeze_version}" not in combined or draft_version == freeze_version, "manuscripts do not cite an earlier manuscript package", checks)
    archive_hash = sha256(zip_file)
    require(zip_file.name in combined, "manuscripts name the delivered formal archive", checks)
    require(archive_hash in combined, "manuscripts state the delivered formal archive SHA-256", checks)
    require(f"lean_v{freeze_version}_freeze" in combined, "manuscripts name the delivered formal-freeze directory", checks)

    if paper == "PAPER_I":
        freeze_axioms = (freeze / "FreezeAxioms.lean").read_text(encoding="utf-8")
        for declaration in (
            "PaperI.paperI_main",
            "PaperI.Split.paperI_main_sharp",
            "PaperI.assembly_sharp",
            "PaperI.Split.residual_duality",
        ):
            require(f"#print axioms {declaration}" in freeze_axioms, f"axiom gate covers {declaration}", checks)
            require(declaration in axioms, f"axiom report records {declaration}", checks)
        require("5a1b53324c4d8ee1d45ac22f1d127df98bc7543e5e5bb1e9e07da48d63faa7f0" not in combined, "obsolete Paper I archive hash removed", checks)
        require("with \\(o\\ge1\\)" in en and "con \\(o\\ge1\\)" in es, "tightness boundary qualification is synchronized", checks)
        if draft_version == "1.3":
            en_tex = paths["en_tex"].read_text(encoding="utf-8")
            es_tex = paths["es_tex"].read_text(encoding="utf-8")
            require("gives \\(z_e=x_e\\)" in en and "da \\(z_e=x_e\\)" in es, "equation (4.7) substitution z=x is explicit and bilingual", checks)
            require("residual coefficient \\(r_e\\) is zero" in en and "coeficiente residual \\(r_e\\) es cero" in es, "equation (4.7) H-accounting is explicit and bilingual", checks)
            require("If \\(A\\ge0\\) and \\(o\\ge3\\)" in en and "Si \\(A\\ge0\\) y \\(o\\ge3\\)" in es, "Appendix A.2 excess formula is restricted to o>=3", checks)
            require("Corollary 7.1g" not in combined and "Corolario 7.1g" not in combined, "unverified Schrijver pinpoint removed", checks)
            require("[4, Chapter 7]" in en and "[4, Capítulo 7]" in es, "Schrijver chapter-level citation is synchronized", checks)
            require("CEOClique_Parts.pdf" in en and "CEOClique_Parts.pdf" in es, "primary Chen--Erdos--Ordman scan is cited in both Markdown sources", checks)
            require("erdos-81-chordal-clique-partitions" not in combined, "unused stale repository citation removed", checks)
            require("`sharp` refers to the quadratic coefficient \\(1/6\\)" in en, "English sharpness scope is explicit", checks)
            require("`sharp` se refiere al coeficiente cuadrático \\(1/6\\)" in es, "Spanish sharpness scope is explicit", checks)
            duplicate_markers = (
                "La demostración resultante tiene la forma",
                "Finalmente, \\(V_{\\mathrm{com}}\\le\\nu_3^*(G)\\). Así,",
                "Esto prueba el Teorema 1.1.",
                "El artículo se limita deliberadamente a la desigualdad fraccional finita.",
                "El autor reporta una auditoría adversarial interna asistida por IA",
            )
            for marker in duplicate_markers:
                require(es.count(marker) == 1, f"Spanish Markdown block occurs once: {marker[:45]}", checks)
                tex_marker = marker.replace("\\(", "\\(").replace("\\)", "\\)")
                require(es_tex.count(tex_marker) == 1, f"Spanish TeX block occurs once: {marker[:45]}", checks)
            correction_matrix = package / "04_integrity" / "EXTERNAL_AUDIT_CORRECTION_MATRIX.md"
            require(correction_matrix.is_file(), "external-audit correction matrix is present", checks)
            matrix_text = correction_matrix.read_text(encoding="utf-8")
            for finding in ("EXT-P1-L-001", "EXT-P1-M-001", "EXT-P1-D-001", "EXT-P1-E-002", "EXT-P1-J-001", "EXT-P1-I-001", "EXT-P1-I-002", "EXT-P1-I-003"):
                require(finding in matrix_text, f"correction matrix covers {finding}", checks)
            integrity_manifest = package / "04_integrity" / "CURRENT_TARGET_SHA256.txt"
            integrity_count = verify_manifest(integrity_manifest, package)
            require(integrity_count >= 7, "current integrity manifest covers manuscript artifacts and Lean archive", checks)
    elif paper == "PAPER_II":
        require("PAPER_II_LEAN_v1.0.1_FREEZE_sources.zip" not in combined, "obsolete Paper II archive name removed", checks)
        require("lean_v1.0.1_freeze/gate_logs" not in combined, "obsolete Paper II log path removed", checks)
        require("dacccc06" not in combined, "obsolete Paper II archive hash removed", checks)
        require("gate_logs/BUILD_LOG.txt" in combined and "gate_logs/BUILD_SUPPLEMENT_EXTREMIZER_COPYDEFECT.txt" in combined, "Paper II manuscripts name both delivered build records", checks)
    elif paper == "PAPER_III":
        require("first formal public release" in en and "primera liberación pública formal" in es, "Paper III first-public-release status is synchronized", checks)

    stray_dirs = [path for path in package.rglob("*") if path.is_dir() and path.name.startswith("$")]
    require(not stray_dirs, "package contains no shell-variable-named directories", checks)
    stray_tex_outputs = [
        path for path in manuscript.rglob("*")
        if path.is_file() and path.suffix.lower() in {".aux", ".log", ".out", ".toc", ".fls", ".fdb_latexmk"}
    ]
    require(not stray_tex_outputs, "manuscript directory contains no TeX compiler residue", checks)
    require("**Internal prior-art and novelty assessment.**" in en, "English internal novelty assessment present", checks)
    require("**Evaluación interna de arte previo y novedad.**" in es, "Spanish internal novelty assessment present", checks)
    require("EDITORIAL_DRAFT_WITH_OPEN_GATES" in en and "EDITORIAL_DRAFT_WITH_OPEN_GATES" in es, "draft status synchronized", checks)
    require(headings(en) == headings(es), "English/Spanish heading hierarchy matches", checks)
    en_figures, es_figures = figures(en), figures(es)
    require(len(en_figures) == len(es_figures), "English/Spanish figure counts match", checks)
    require([normalized_figure(x) for x in en_figures] == [normalized_figure(x) for x in es_figures], "English/Spanish figure order matches", checks)
    for relative in en_figures + es_figures:
        require((manuscript / relative).is_file(), f"figure exists: {relative}", checks)
    require(identifiers(en) == identifiers(es), "protected formal identifier sets match", checks)

    pdf_extracts: dict[str, str] = {}
    for language in ("en", "es"):
        tex = paths[f"{language}_tex"].read_text(encoding="utf-8")
        require("\\documentclass" in tex and "11pt" in tex and "margin=1in" in tex, f"{language} TeX uses series layout", checks)
        require(tex.count("\\includegraphics") == len(en_figures), f"{language} TeX figure count matches Markdown", checks)
        require(paths[f"{language}_pdf"].stat().st_mtime_ns >= paths[f"{language}_tex"].stat().st_mtime_ns, f"{language} PDF does not predate TeX", checks)
        require(embedded_fonts(paths[f"{language}_pdf"]), f"{language} PDF fonts are embedded", checks)
        extracted = pdf_text(paths[f"{language}_pdf"])
        pdf_extracts[language] = extracted
        title = (en if language == "en" else es).splitlines()[0].removeprefix("# ")
        require(title in re.sub(r"\s+", " ", extracted), f"{language} PDF title matches Markdown", checks)
        require("EDITORIAL_DRAFT_WITH_OPEN_GATES" in extracted, f"{language} PDF status present", checks)

    if paper == "PAPER_I" and draft_version == "1.3":
        for marker in (
            "La demostración resultante tiene la forma",
            "Esto prueba el Teorema 1.1.",
            "El artículo se limita deliberadamente a la desigualdad fraccional finita.",
            "El autor reporta una auditoría adversarial interna asistida por IA",
        ):
            require(pdf_extracts["es"].count(marker) == 1, f"Spanish PDF block occurs once: {marker[:45]}", checks)
        require("Corolario 7.1g" not in pdf_extracts["es"] and "Corollary 7.1g" not in pdf_extracts["en"], "unverified Schrijver pinpoint absent from PDFs", checks)
        require("CEOClique_Parts.pdf" in pdf_extracts["en"] and "CEOClique_Parts.pdf" in pdf_extracts["es"], "Chen--Erdos--Ordman scan appears in both PDFs", checks)

    summary = {
        "paper": paper,
        "target": f"preprint_draft_v{draft_version}",
        "audit_class": "INTERNAL_NOT_EXTERNAL",
        "lean_rerun": False,
        "status": "PASS",
        "checks_passed": len(checks),
        "checks": checks,
        "metrics": {
            "artifact_manifest_entries": artifact_count,
            "source_manifest_entries": source_count,
            "package_manifest_entries": package_count,
            "figures_per_language": len(en_figures),
            "formal_identifiers": len(identifiers(en)),
            "pdf_pages_en": pdf_pages(paths["en_pdf"]),
            "pdf_pages_es": pdf_pages(paths["es_pdf"]),
            "recorded_axioms": sorted(seen_axioms),
        },
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    rendered = json.dumps(summary, indent=2, ensure_ascii=False) + "\n"
    args.output.write_text(rendered, encoding="utf-8")
    args.log.parent.mkdir(parents=True, exist_ok=True)
    args.log.write_text(rendered + "EXIT_CODE=0\n", encoding="utf-8")
    print(rendered, end="")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except Exception as exc:
        print(f"FAIL: {type(exc).__name__}: {exc}", file=sys.stderr)
        raise
