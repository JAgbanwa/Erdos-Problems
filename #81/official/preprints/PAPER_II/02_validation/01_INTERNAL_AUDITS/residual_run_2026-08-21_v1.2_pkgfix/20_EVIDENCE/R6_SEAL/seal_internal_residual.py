from __future__ import annotations

import hashlib
import json
import zipfile
from pathlib import Path


RUN = Path(__file__).resolve().parents[2]
PACKAGE = RUN / "40_PACKAGE"
ZIP_PATH = PACKAGE / "INTERNAL_RESIDUAL_AUDIT_PACKAGE.zip"


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def manifest_text(files: list[Path], base: Path) -> str:
    return "".join(f"{digest(path)}  {path.relative_to(base).as_posix()}\n" for path in files)


def main() -> int:
    gates = RUN / "20_EVIDENCE"
    gate_counts: dict[str, int] = {}
    for gate in sorted(path for path in gates.iterdir() if path.is_dir()):
        manifest = gate / "SHA256_MANIFEST.txt"
        files = sorted(
            (path for path in gate.rglob("*") if path.is_file() and path != manifest),
            key=lambda path: path.relative_to(gate).as_posix().lower(),
        )
        manifest.write_text(manifest_text(files, gate), encoding="utf-8", newline="\n")
        gate_counts[gate.name] = len(files)

    input_files: list[Path] = []
    for directory in (RUN / "00_CONTROL", RUN / "20_EVIDENCE", RUN / "30_REPORT"):
        input_files.extend(path for path in directory.rglob("*") if path.is_file())
    input_files.sort(key=lambda path: path.relative_to(RUN).as_posix().lower())

    PACKAGE.mkdir(parents=True, exist_ok=True)
    package_manifest = PACKAGE / "PACKAGE_MANIFEST.sha256"
    package_manifest.write_text(manifest_text(input_files, RUN), encoding="utf-8", newline="\n")
    entries = [
        {"path": path.relative_to(RUN).as_posix(), "bytes": path.stat().st_size, "sha256": digest(path)}
        for path in input_files
    ]
    package_json = PACKAGE / "PACKAGE_MANIFEST.json"
    package_json.write_text(
        json.dumps(
            {
                "paper": "PAPER_II",
                "target": "preprint_draft_v1.2_package_fix",
                "protocol": "PAPER_II_INTERNAL_PACKAGE_RESIDUAL_v1.0",
                "files": len(entries),
                "bytes": sum(item["bytes"] for item in entries),
                "manifest_algorithm": "UTF-8 LF-only '<file_sha256><two spaces><run-relative_posix_path>\\n', sorted case-insensitively by run-relative POSIX path",
                "entries": entries,
            },
            ensure_ascii=False,
            indent=2,
        )
        + "\n",
        encoding="utf-8",
        newline="\n",
    )

    zip_members = input_files + [package_manifest, package_json]
    with zipfile.ZipFile(ZIP_PATH, "w", compression=zipfile.ZIP_DEFLATED, compresslevel=9) as archive:
        for path in zip_members:
            archive.write(path, path.relative_to(RUN).as_posix())

    failures: list[str] = []
    with zipfile.ZipFile(ZIP_PATH) as archive:
        names = set(archive.namelist())
        for path in zip_members:
            name = path.relative_to(RUN).as_posix()
            if name not in names:
                failures.append(f"missing member: {name}")
            elif hashlib.sha256(archive.read(name)).hexdigest() != digest(path):
                failures.append(f"member mismatch: {name}")

    if failures:
        raise RuntimeError("; ".join(failures))

    zip_sha = digest(ZIP_PATH)
    summary = PACKAGE / "FINAL_SEAL_SUMMARY.json"
    summary.write_text(
        json.dumps(
            {
                "status": "PASS",
                "gate_manifest_file_counts": gate_counts,
                "package_manifest_entries": len(entries),
                "zip_members": len(zip_members),
                "zip_member_mismatches": 0,
                "zip_sha256": zip_sha,
            },
            indent=2,
        )
        + "\n",
        encoding="utf-8",
        newline="\n",
    )
    sidecar = PACKAGE / "INTERNAL_RESIDUAL_AUDIT_PACKAGE.zip.sha256"
    sidecar.write_text(f"{zip_sha}  {ZIP_PATH.name}\n", encoding="utf-8", newline="\n")
    print(summary.read_text(encoding="utf-8"))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
