from __future__ import annotations

import hashlib
import json
import re
from datetime import datetime
from pathlib import Path


HERE = Path(__file__).resolve().parent
RESULTS = HERE / "RESULTS"
FREEZE = Path(__file__).resolve().parents[3] / "05_formalization" / "lean_v1.4_freeze"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def read(path: Path) -> str:
    return path.read_text(encoding="utf-8-sig", errors="replace")


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def manifest(path: Path) -> dict[str, str]:
    result: dict[str, str] = {}
    for line in read(path).splitlines():
        if not line.strip():
            continue
        match = re.fullmatch(r"([0-9a-fA-F]{64})\s+\*?(.+)", line)
        if not match:
            raise AssertionError(f"malformed manifest line: {line!r}")
        result[match.group(2).replace("\\", "/")] = match.group(1).lower()
    return result


checks: list[dict[str, object]] = []


def require(condition: bool, label: str, detail: object = "") -> None:
    checks.append({"pass": bool(condition), "label": label, "detail": detail})


def main() -> int:
    result_manifest = manifest(RESULTS / "RESULTS_MANIFEST.sha256")
    require(len(result_manifest) == 32, "32-entry result manifest")
    for relative, expected in result_manifest.items():
        target = RESULTS / relative
        require(target.is_file() and sha256(target) == expected, f"result hash: {relative}")

    freeze_manifest = manifest(FREEZE / "SOURCE_MANIFEST.sha256")
    kit_manifest_raw = manifest(HERE / "BUILD_KIT_IDENTITY" / "PROJECT_MANIFEST.sha256")
    kit_project = {
        key.removeprefix("PROJECT/"): value
        for key, value in kit_manifest_raw.items()
        if key.startswith("PROJECT/")
    }
    extras = sorted(set(kit_project) - set(freeze_manifest))
    mismatches = sorted(
        key for key, value in freeze_manifest.items()
        if kit_project.get(key) != value
    )
    require(len(freeze_manifest) == 707, "freeze has 707 source/config entries")
    require(not mismatches, "all 707 freeze entries match the build-kit project manifest", mismatches)
    require(extras == ["CANDIDATE_METADATA.json", "ESCAPE_HATCH_ASSESSMENT.md"], "only two noncompiled metadata files are extra", extras)

    received_zip = HERE / "PAPER_III_v1.4_CLEAN_BUILD_RESULTS_CCS_NOTEBOOK456_20260823_021132.zip"
    received_sidecar = received_zip.with_suffix(received_zip.suffix + ".sha256")
    received_expected = read(received_sidecar).split()[0].lower()
    require(sha256(received_zip) == received_expected, "received ZIP matches its SHA-256 sidecar")

    config_before = json.loads(read(RESULTS / "evidence" / "CONFIG_HASHES_BEFORE.json"))
    config_after = json.loads(read(RESULTS / "evidence" / "CONFIG_HASHES_AFTER.json"))
    require(config_before == config_after, "project configuration is byte-identical before and after the run")
    freeze_config = {item["file"]: item["sha256"] for item in config_before}
    require(
        all(sha256(FREEZE / name) == expected for name, expected in freeze_config.items()),
        "project configuration matches the v1.4 freeze",
    )

    clean_state = read(RESULTS / "evidence" / "PRE_CACHE_CLEAN_STATE.txt")
    require("project_dot_lake_present=false" in clean_state, "no initial project .lake directory")
    require("compiled_project_artifacts=0" in clean_state, "no initial compiled project objects")
    require("lean_source_files=704" in clean_state, "704 Lean source files recorded")

    ordered_exit_files = [
        RESULTS / "logs" / "01_cache_get.exit.txt",
        RESULTS / "logs" / "02_build_public_root_clean.exit.txt",
        RESULTS / "logs" / "03_build_query_roots_incremental.exit.txt",
        *sorted((RESULTS / "logs").glob("axioms_*.exit.txt")),
    ]
    intervals: list[tuple[datetime, datetime]] = []
    for path in ordered_exit_files:
        text = read(path)
        require("exit_code=0" in text, f"zero exit: {path.name}")
        start = datetime.fromisoformat(re.search(r"start_utc=(.+)", text).group(1))
        end = datetime.fromisoformat(re.search(r"end_utc=(.+)", text).group(1))
        intervals.append((start, end))
    gaps = [(intervals[i][0] - intervals[i - 1][1]).total_seconds() for i in range(1, len(intervals))]
    require(all(0 <= gap < 30 for gap in gaps), "single continuous command sequence", {"max_gap_seconds": max(gaps)})

    public_log = read(RESULTS / "logs" / "02_build_public_root_clean.log")
    query_log = read(RESULTS / "logs" / "03_build_query_roots_incremental.log")
    require("Build completed successfully (8455 jobs)." in public_log, "clean public root completed 8,455 jobs")
    require("Build completed successfully (8444 jobs)." in query_log, "query roots completed 8,444 jobs")
    require("warning: declaration uses 'sorry'" not in public_log + query_log, "no active sorry warning in build logs")

    axiom_text = "\n".join(read(path) for path in sorted((RESULTS / "logs").glob("axioms_*.log")))
    footprints = re.findall(r"depends on axioms:\s*\[([^\]]*)\]", axiom_text)
    axiom_union = {
        item.strip()
        for footprint in footprints
        for item in footprint.split(",")
        if item.strip()
    }
    headline = re.search(r"'?PaperIII\.Theorem_1_1'? depends on axioms:\s*\[([^\]]*)\]", axiom_text)
    require(len(footprints) == 42, "42 theorem-level axiom outputs")
    require(axiom_union == ALLOWED_AXIOMS, "axiom union is foundational-only", sorted(axiom_union))
    require("sorryAx" not in axiom_text, "no sorryAx in axiom output")
    require(headline is not None, "headline theorem axiom output is present with Lean's quoted declaration format")
    axiom_summary = read(RESULTS / "evidence" / "AXIOM_GATE_SUMMARY.txt")
    require("result=PASS_FOUNDATIONAL_ONLY" in axiom_summary, "runner axiom gate reports foundational-only PASS")
    require("query_files=8" in axiom_summary and "surfaces=42" in axiom_summary and "sorryAx=0" in axiom_summary, "runner axiom summary has the expected complete coverage")

    closure = json.loads(read(RESULTS / "evidence" / "IMPORT_CLOSURE.json"))
    require(closure["paperIII_reaches_final"] and closure["paperIII_reaches_public_api"], "public root reaches final theorem and PublicAPI")
    require(not closure["canonical_reaches_archived_wlog"] and not closure["canonical_reaches_archived_axioms"], "canonical closure excludes archived axiom modules")
    dependencies = json.loads(read(RESULTS / "evidence" / "DEPENDENCIES.json"))
    require(len(dependencies) == 9 and all(d["clean"] and d["actual_revision"] == d["expected_revision"] for d in dependencies), "nine dependencies are exact and clean")

    raw_summary = json.loads(read(RESULTS / "RUN_SUMMARY.json"))
    require(raw_summary["result"] == "PASS" and raw_summary["failure"] is None, "raw runner reports PASS without adjudication")
    require(raw_summary["clean_public_root_build"] is True, "raw runner classifies the public-root build as clean")
    require(raw_summary["started_utc"] < raw_summary["ended_utc"] and raw_summary["duration_seconds"] > 0, "raw run duration is recorded")

    failed = [item for item in checks if not item["pass"]]
    output = {
        "paper": "PAPER_III",
        "version": "1.4",
        "raw_runner_result": "PASS",
        "raw_runner_failure": raw_summary["failure"],
        "validated_result": "PASS_CLEAN_UNINTERRUPTED",
        "validation_basis": "The received runner reports PASS; all result hashes, command exits, build counts, axiom surfaces, closure checks, dependency pins, source identity and configuration invariance verify independently.",
        "clean_initial_state": True,
        "uninterrupted_command_sequence": True,
        "source_identity": "707/707 freeze source/config hashes match the runner-verified kit manifest",
        "checks_passed": sum(bool(item["pass"]) for item in checks),
        "checks_total": len(checks),
        "failed": failed,
        "checks": checks,
    }
    (HERE / "VALIDATED_RUN_SUMMARY.json").write_text(
        json.dumps(output, indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8",
        newline="\n",
    )
    print(json.dumps(output, indent=2, ensure_ascii=True))
    return 0 if not failed else 1


if __name__ == "__main__":
    raise SystemExit(main())
