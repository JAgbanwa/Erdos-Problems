from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path


ANCHORS = {
    "01_manuscript/PAPER_II_preprint_draft_v1.2.md": "7215e14bbea8ab2bf208dcdd1efa050cd2b72c997eee2efe504a1e6817c68882",
    "01_manuscript/PAPER_II_preprint_draft_v1.2_es.md": "d0d1df05eb267a51db2ccc100dd9725dcde9b03dbb95c8a730742e357eb0f4dc",
    "01_manuscript/PAPER_II_preprint_draft_v1.2_en.tex": "bb5f76c3ce56dbb0bff11242a3a8787f9c8ba3d9f0ad23973fc2f26cc5fc3cf0",
    "01_manuscript/PAPER_II_preprint_draft_v1.2_es.tex": "d3f0c6301a48d6553ebad222fa685f152119cb61b5efd3e8be55e389f9d606ae",
    "01_manuscript/PAPER_II_preprint_draft_v1.2_en.pdf": "d05c4cab1262357fddd21e4aab399bdb92d5bcf139172897c80595e781049052",
    "01_manuscript/PAPER_II_preprint_draft_v1.2_es.pdf": "d525d02a6e911cb23f7e1f28e1de7648441eccea6de206e76e5321161c86c2db",
    "05_formalization/lean_v1.2_freeze/PAPER_II_lean_v1.2_freeze.zip": "ee2d05cc40d943ca92f8f7bf3e5dd83c2692518ddea5e2ca4f7686ccb1ac3895",
    "02_validation/01_INTERNAL_AUDITS/30_PACKAGE/INTERNAL_AUDIT_PACKAGE.zip": "e6f625486db867582da72fff9e71fa0f600dcce40e43ef885ce01756282b24e2",
    "02_validation/02_IA_ADVERSARIAL_AUDITS/run_2026-08-21_v1.2/30_REPORT/FINAL_AUDIT_REPORT.md": "1e7afd3e9394bf83beb7e33ce19ff5227072fcd6b0eb3fd21e571329564e3ded",
}

EXCLUDED_PREFIXES = (
    "02_validation/02_IA_ADVERSARIAL_AUDITS/",
    "02_validation/01_INTERNAL_AUDITS/residual_run_2026-08-21_v1.2_pkgfix/",
)


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def verify_sidecar(root: Path, relative: str) -> tuple[bool, list[str]]:
    path = root / relative
    errors: list[str] = []
    raw = path.read_bytes()
    if b"\r" in raw:
        errors.append("not LF-only")
    for number, line in enumerate(raw.decode("utf-8").splitlines(), 1):
        match = re.fullmatch(r"([0-9a-f]{64})  (.+)", line)
        if not match:
            errors.append(f"line {number}: invalid format")
            continue
        expected, name = match.groups()
        target = root / Path(name)
        if not target.is_file():
            errors.append(f"line {number}: missing {name}")
        elif digest(target) != expected:
            errors.append(f"line {number}: mismatch {name}")
    return not errors, errors


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--manifest", required=True, type=Path)
    args = parser.parse_args()
    root = args.root.resolve()
    checks: list[dict[str, object]] = []

    def add(name: str, passed: bool, detail: str) -> None:
        checks.append({"name": name, "status": "PASS" if passed else "FAIL", "detail": detail})

    for relative, expected in ANCHORS.items():
        path = root / Path(relative)
        actual = digest(path) if path.is_file() else "MISSING"
        add(f"anchor:{relative}", actual == expected, actual)

    for relative in (
        "04_integrity/INITIAL_SOURCE_SHA256.txt",
        "04_integrity/CURRENT_TARGET_SHA256.txt",
    ):
        passed, errors = verify_sidecar(root, relative)
        add(f"sidecar:{relative}", passed, "; ".join(errors) if errors else "all entries verify; LF-only")

    integrity = root / "04_integrity"
    readme = (integrity / "README.md").read_text(encoding="utf-8")
    diff = (integrity / "INITIALIZATION_DIFF.md").read_text(encoding="utf-8")
    matrix = (integrity / "EXTERNAL_AUDIT_V1.2_RESIDUAL_MATRIX.md").read_text(encoding="utf-8")
    add("stale_pending_v1_1_absent", "Pending for v1.1" not in readme, "README inspected")
    add("missing_v1_1_sidecar_path_absent", "01_manuscript/PAPER_II_preprint_draft_v1.1.md" not in (integrity / "INITIAL_SOURCE_SHA256.txt").read_text(encoding="utf-8"), "sidecar inspected")
    add("v1_1_to_v1_2_diff_documented", "v1.1 to v1.2" in diff, "INITIALIZATION_DIFF inspected")
    add("minor_disposition_documented", "EXT-PII-M-001" in matrix and "Corrected" in matrix, "residual matrix inspected")
    add("note_preserved", "EXT-P2-I-001" in matrix and "nonblocking" in matrix, "residual matrix inspected")

    unwanted = []
    forbidden_suffixes = {".aux", ".toc", ".out", ".fls", ".fdb_latexmk", ".synctex", ".bbl", ".blg"}
    for path in root.rglob("*"):
        rel = path.relative_to(root).as_posix()
        if any(rel.startswith(prefix) for prefix in EXCLUDED_PREFIXES):
            continue
        if path.is_dir() and path.name.lower() == "tmp":
            unwanted.append(rel)
        if path.is_file() and (path.stat().st_size == 0 or path.suffix.lower() in forbidden_suffixes or "$" in path.name):
            unwanted.append(rel)
    add("package_hygiene", not unwanted, ", ".join(unwanted) if unwanted else "no tmp, zero-byte, dollar-name or compiler residue")

    inventory = []
    for path in sorted(root.rglob("*"), key=lambda item: item.as_posix().lower()):
        if not path.is_file():
            continue
        rel = path.relative_to(root).as_posix()
        if any(rel.startswith(prefix) for prefix in EXCLUDED_PREFIXES):
            continue
        inventory.append({"path": rel, "bytes": path.stat().st_size, "sha256": digest(path)})

    manifest_text = "".join(f"{item['sha256']}  {item['path']}\n" for item in inventory)
    args.manifest.parent.mkdir(parents=True, exist_ok=True)
    args.manifest.write_text(manifest_text, encoding="utf-8", newline="\n")
    manifest_sha = hashlib.sha256(manifest_text.encode("utf-8")).hexdigest()

    payload = {
        "paper": "PAPER_II",
        "target": "preprint_draft_v1.2_package_fix",
        "status": "PASS" if all(item["status"] == "PASS" for item in checks) else "FAIL",
        "checks_passed": sum(item["status"] == "PASS" for item in checks),
        "checks_total": len(checks),
        "checks": checks,
        "inventory": {
            "scope": "target excluding all external-audit output and this residual run",
            "files": len(inventory),
            "bytes": sum(item["bytes"] for item in inventory),
            "canonical_manifest_algorithm": "SHA-256 of UTF-8 LF-only lines '<file_sha256><two spaces><relative_posix_path>\\n' sorted case-insensitively by relative POSIX path",
            "manifest_sha256": manifest_sha,
        },
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8", newline="\n")
    print(json.dumps(payload, ensure_ascii=False, indent=2))
    return 0 if payload["status"] == "PASS" else 2


if __name__ == "__main__":
    raise SystemExit(main())
