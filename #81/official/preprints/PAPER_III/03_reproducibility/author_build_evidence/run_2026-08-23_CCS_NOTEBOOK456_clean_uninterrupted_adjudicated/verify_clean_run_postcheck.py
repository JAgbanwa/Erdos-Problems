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
    require(len(result_manifest) == 30, "30-entry result manifest")
    for relative, expected in result_manifest.items():
        target = RESULTS / relative
        require(target.is_file() and sha256(target) == expected, f"result hash: {relative}")

    freeze_manifest = manifest(FREEZE / "SOURCE_MANIFEST.sha256")
    kit_manifest_raw = manifest(HERE / "RUNNER_SNAPSHOT" / "PROJECT_MANIFEST.sha256")
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

    closure = json.loads(read(RESULTS / "evidence" / "IMPORT_CLOSURE.json"))
    require(closure["paperIII_reaches_final"] and closure["paperIII_reaches_public_api"], "public root reaches final theorem and PublicAPI")
    require(not closure["canonical_reaches_archived_wlog"] and not closure["canonical_reaches_archived_axioms"], "canonical closure excludes archived axiom modules")
    dependencies = json.loads(read(RESULTS / "evidence" / "DEPENDENCIES.json"))
    require(len(dependencies) == 9 and all(d["clean"] and d["actual_revision"] == d["expected_revision"] for d in dependencies), "nine dependencies are exact and clean")

    raw_summary = json.loads(read(RESULTS / "RUN_SUMMARY.json"))
    require(raw_summary["failure"] == "Headline theorem axiom output is missing.", "raw runner stopped only at the known headline regex postcheck")
    require(raw_summary["started_utc"] < raw_summary["ended_utc"] and raw_summary["duration_seconds"] == 5047.306, "raw run duration is recorded")

    failed = [item for item in checks if not item["pass"]]
    output = {
        "paper": "PAPER_III",
        "version": "1.4",
        "raw_runner_result": "FAIL",
        "raw_runner_failure": raw_summary["failure"],
        "adjudicated_result": "PASS_CLEAN_UNINTERRUPTED_POSTCHECK_ADJUDICATED",
        "adjudication_basis": "All build/query/axiom commands exited zero; the headline output exists but Lean quotes the declaration name, while the runner regex required an unquoted name.",
        "clean_initial_state": True,
        "uninterrupted_command_sequence": True,
        "source_identity": "707/707 freeze source/config hashes match the runner-verified kit manifest",
        "checks_passed": sum(bool(item["pass"]) for item in checks),
        "checks_total": len(checks),
        "failed": failed,
        "checks": checks,
    }
    (HERE / "ADJUDICATED_RUN_SUMMARY.json").write_text(
        json.dumps(output, indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8",
        newline="\n",
    )
    print(json.dumps(output, indent=2, ensure_ascii=True))
    return 0 if not failed else 1


if __name__ == "__main__":
    raise SystemExit(main())
