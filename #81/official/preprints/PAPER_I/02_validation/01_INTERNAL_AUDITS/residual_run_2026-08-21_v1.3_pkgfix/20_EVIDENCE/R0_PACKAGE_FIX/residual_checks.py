from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path, PurePosixPath


EXPECTED = {
    "01_manuscript/PAPER_I_preprint_draft_v1.3.md": "f3094b670c93ff622c3f573cdab61bdd0f5d84007f04b1888b364e0183565bea",
    "01_manuscript/PAPER_I_preprint_draft_v1.3_es.md": "57ba967fc2de805b7bbb4cf5f937727bde43c2ada80fa794bcbb5a727db05b8b",
    "01_manuscript/PAPER_I_preprint_draft_v1.3_en.tex": "1a87de70548879ca90a714ec9e1b10c8576b380a749785916e5d59176e479465",
    "01_manuscript/PAPER_I_preprint_draft_v1.3_es.tex": "f83ee709c1168b5b9afe504e6b6a43763bf3bb2a08f674f2031f83670ba9bb56",
    "01_manuscript/PAPER_I_preprint_draft_v1.3_en.pdf": "7d04c47692b613c8d6e2cc4471f0205128b4ae06ca11d581a08d020eb2236db0",
    "01_manuscript/PAPER_I_preprint_draft_v1.3_es.pdf": "3ad16ae86e8fcad358bf964a6ae98ae053b0bde2fdf3140e008cedab78b90c2a",
    "05_formalization/lean_v1.2_freeze/PAPER_I_lean_v1.2_freeze.zip": "0181506408644fc1f8872d711de5a98a500f4052aa295bcd6f8c82776694fd3a",
}
EXTERNAL_REPORT = (
    "02_validation/02_IA_ADVERSARIAL_AUDITS/"
    "run_2026-08-21_v1.3/30_REPORT/FINAL_AUDIT_REPORT.md"
)
EXTERNAL_REPORT_HASH = "f2ad1605f0a802932c07503bfad429a98b08af26844dd968aad6e3f145aee495"
RUN_PREFIX = (
    "02_validation/01_INTERNAL_AUDITS/"
    "residual_run_2026-08-21_v1.3_pkgfix"
)
EXTERNAL_PREFIX = "02_validation/02_IA_ADVERSARIAL_AUDITS"
FORBIDDEN_SUFFIXES = (
    ".aux",
    ".toc",
    ".out",
    ".fls",
    ".fdb_latexmk",
    ".synctex.gz",
    ".nav",
    ".snm",
)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def excluded(relative: str) -> bool:
    p = PurePosixPath(relative)
    s = p.as_posix()
    return s == EXTERNAL_PREFIX or s.startswith(EXTERNAL_PREFIX + "/") or (
        s == RUN_PREFIX or s.startswith(RUN_PREFIX + "/")
    )


def verify_manifest(manifest: Path, base: Path) -> tuple[bool, int, list[str]]:
    errors: list[str] = []
    count = 0
    for raw in manifest.read_text(encoding="utf-8").splitlines():
        match = re.fullmatch(r"([0-9a-f]{64})  (.+)", raw)
        if not match:
            errors.append(f"malformed: {raw}")
            continue
        expected, rel = match.groups()
        target = base / rel
        count += 1
        if not target.is_file():
            errors.append(f"missing: {rel}")
        elif sha256(target) != expected:
            errors.append(f"hash mismatch: {rel}")
    return not errors, count, errors


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--inventory", required=True, type=Path)
    parser.add_argument("--freeze-manifest", required=True, type=Path)
    args = parser.parse_args()
    root = args.root.resolve()

    checks: list[dict] = []

    def check(name: str, passed: bool, detail: object) -> None:
        checks.append({"name": name, "passed": bool(passed), "detail": detail})

    inventory = []
    tmp_dirs = []
    compiler_residue = []
    zero_byte = []
    dollar_o = []
    for path in sorted(root.rglob("*")):
        rel = path.relative_to(root).as_posix()
        if excluded(rel):
            continue
        if path.is_dir():
            if path.name.lower() == "tmp":
                tmp_dirs.append(rel)
            continue
        if not path.is_file():
            continue
        size = path.stat().st_size
        digest = sha256(path)
        inventory.append({"path": rel, "bytes": size, "sha256": digest})
        lower = path.name.lower()
        if any(lower.endswith(suffix) for suffix in FORBIDDEN_SUFFIXES):
            compiler_residue.append(rel)
        if size == 0:
            zero_byte.append(rel)
        if path.name == "$o":
            dollar_o.append(rel)

    check("RES-V13-001 no tmp directory", not tmp_dirs, tmp_dirs)
    check("no forbidden compiler residue", not compiler_residue, compiler_residue)
    check("no zero-byte files", not zero_byte, zero_byte)
    check("no stray $o", not dollar_o, dollar_o)

    changelog = (root / "CHANGELOG_v1.3.md").read_text(encoding="utf-8")
    correct = ["PaperI.assembly_sharp", "PaperI.Split.residual_duality"]
    wrong = ["PaperI.Split.assembly_sharp", "PaperI.residual_duality"]
    check(
        "RES-V13-002 correct changelog namespaces",
        all(changelog.count(name) == 1 for name in correct),
        {name: changelog.count(name) for name in correct},
    )
    check(
        "transposed changelog namespaces absent",
        all(name not in changelog for name in wrong),
        {name: changelog.count(name) for name in wrong},
    )

    manuscript = (root / "01_manuscript/PAPER_I_preprint_draft_v1.3.md").read_text(
        encoding="utf-8"
    )
    freeze_axioms = (
        root / "05_formalization/lean_v1.2_freeze/FreezeAxioms.lean"
    ).read_text(encoding="utf-8")
    check(
        "manuscript Appendix C agrees with corrected namespaces",
        all(name in manuscript for name in correct),
        {name: name in manuscript for name in correct},
    )
    check(
        "FreezeAxioms agrees with corrected namespaces",
        all(name in freeze_axioms for name in correct),
        {name: name in freeze_axioms for name in correct},
    )

    actual_anchors = {}
    for rel, expected in EXPECTED.items():
        path = root / rel
        actual = sha256(path) if path.is_file() else None
        actual_anchors[rel] = actual
        check(f"unchanged anchor: {rel}", actual == expected, actual)

    report = root / EXTERNAL_REPORT
    report_hash = sha256(report) if report.is_file() else None
    check(
        "external PASS_WITH_RESIDUALS report preserved",
        report_hash == EXTERNAL_REPORT_HASH,
        report_hash,
    )

    sidecar = root / "01_manuscript/PAPER_I_preprint_draft_v1.3_SHA256.txt"
    raw_sidecar = sidecar.read_bytes()
    check("manuscript sidecar LF-only", b"\r" not in raw_sidecar, {
        "cr": raw_sidecar.count(b"\r"),
        "lf": raw_sidecar.count(b"\n"),
    })
    sidecar_ok, sidecar_count, sidecar_errors = verify_manifest(
        sidecar, sidecar.parent
    )
    check(
        "six-artifact sidecar verifies",
        sidecar_ok and sidecar_count == 6,
        {"entries": sidecar_count, "errors": sidecar_errors},
    )

    current = root / "04_integrity/CURRENT_TARGET_SHA256.txt"
    current_ok, current_count, current_errors = verify_manifest(current, root)
    check(
        "current target manifest verifies",
        current_ok and current_count == 8,
        {"entries": current_count, "errors": current_errors},
    )

    check(
        "v1.4 absent from active target",
        not (root.parent / "preprint_draft_v1.4").exists(),
        str(root.parent / "preprint_draft_v1.4"),
    )

    lines = [
        f"{item['sha256']}  {item['path']}"
        for item in inventory
    ]
    aggregate = hashlib.sha256(("\n".join(lines) + "\n").encode("utf-8")).hexdigest()
    payload = {
        "paper": "PAPER_I",
        "target": "preprint_draft_v1.3_package_fix",
        "audit_class": "INTERNAL_NOT_EXTERNAL",
        "excluded_prefixes": [EXTERNAL_PREFIX, RUN_PREFIX],
        "inventory": {
            "files": len(inventory),
            "bytes": sum(item["bytes"] for item in inventory),
            "aggregate_sha256": aggregate,
        },
        "anchors": actual_anchors,
        "checks": checks,
        "checks_passed": sum(item["passed"] for item in checks),
        "checks_total": len(checks),
        "status": "PASS" if all(item["passed"] for item in checks) else "FAIL",
    }

    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    args.inventory.write_text(
        json.dumps({"aggregate_sha256": aggregate, "files": inventory}, indent=2)
        + "\n",
        encoding="utf-8",
    )
    args.freeze_manifest.write_text("\n".join(lines) + "\n", encoding="utf-8")
    print(json.dumps(payload, indent=2))
    return 0 if payload["status"] == "PASS" else 2


if __name__ == "__main__":
    raise SystemExit(main())
