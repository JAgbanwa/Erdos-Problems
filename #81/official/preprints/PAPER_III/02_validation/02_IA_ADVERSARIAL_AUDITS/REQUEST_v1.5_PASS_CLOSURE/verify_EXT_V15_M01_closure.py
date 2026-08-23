from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path


PACKAGE = Path(__file__).resolve().parents[3]
REPRO = PACKAGE / "03_reproducibility"
LOGS = REPRO / "manuscript_build_logs"
MANUSCRIPT = PACKAGE / "01_manuscript"
EXPECTED_MANUSCRIPT = {
    "PAPER_III_preprint_v1.5.md": "a98e9313bfe5f1f98cc92bb29ba97386e8178e38c0201854cf40bd255066c99a",
    "PAPER_III_preprint_v1.5_en.tex": "6a97bc718df81d1cf91ab88ccffd9a9f701482fb898fbeca9240d19b4124195c",
    "PAPER_III_preprint_v1.5_en.pdf": "077a12da4db42ecbe6bcc25333539bf7ee3e63fa20bc7a46d8e801120ac9bb27",
    "PAPER_III_preprint_v1.5_es.md": "ee5a3ef2614316d573f622633d3ac5c544a262a43f36d0a8bacfe149b7beca3e",
    "PAPER_III_preprint_v1.5_es.tex": "cfc2cac78ce2495207e300c7f184c04b0aa778d91f077f25d4481b68dfb8ebcd",
    "PAPER_III_preprint_v1.5_es.pdf": "5ed3f83b97f6c900d63d09dd3eb491ed903693df1b90fe0dbac5df2e1e93ec92",
}
LEAN_ARCHIVE_HASH = "79ee24c38fd776bc2585a0c3c996e30817f0829fc5064463bdbde0fa2d3d7104"


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


checks: list[dict[str, object]] = []


def check(condition: bool, label: str, detail: object = "") -> None:
    checks.append({"pass": bool(condition), "label": label, "detail": detail})


root_files = sorted(path.name for path in LOGS.iterdir() if path.is_file())
legacy = LOGS / "v1.3_legacy"
current = LOGS / "v1.5"
legacy_files = sorted(path for path in legacy.iterdir() if path.is_file())
current_files = sorted(path for path in current.iterdir() if path.is_file())

check(not root_files, "no generically named compiler log remains at manuscript_build_logs root", root_files)
check(len(legacy_files) == 29, "all 29 historical root logs are preserved under v1.3_legacy", len(legacy_files))
check(all("v1.3" in path.read_text(encoding="utf-8", errors="replace") for path in legacy_files),
      "every relocated historical log is genuinely v1.3 evidence")
check(len(current_files) == 6, "the v1.5 log directory contains the six current logs", [p.name for p in current_files])
check(all("PAPER_III_preprint_v1.5" in path.read_text(encoding="utf-8", errors="replace") for path in current_files),
      "every current compiler log names the v1.5 artifact")

generic_consistency = REPRO / "MANUSCRIPT_CONSISTENCY_RESULTS.json"
current_consistency = REPRO / "MANUSCRIPT_CONSISTENCY_RESULTS_v1.5.json"
check(not generic_consistency.exists(), "stale generic consistency result is absent")
data = json.loads(current_consistency.read_text(encoding="utf-8"))
check(data.get("verdict") == "PASS" and data.get("checks") == 61,
      "versioned v1.5 consistency result is PASS 61/61")
check(data.get("files", {}).get("md_en", {}).get("sha256") == EXPECTED_MANUSCRIPT["PAPER_III_preprint_v1.5.md"],
      "versioned consistency result binds to the v1.5 English Markdown hash")

for name, expected in EXPECTED_MANUSCRIPT.items():
    check(sha256(MANUSCRIPT / name) == expected, f"unchanged manuscript hash: {name}")

lean_archive = PACKAGE / "05_formalization" / "lean_v1.4_freeze" / "PAPER_III_lean_v1.4_freeze.zip"
check(sha256(lean_archive) == LEAN_ARCHIVE_HASH, "Lean archive remains byte-identical")

stale_generic_names = {
    "LUALATEX_FINAL_en.log", "LUALATEX_FINAL_es.log",
    "LUALATEX_en_PASS1.txt", "LUALATEX_en_PASS2.txt",
    "LUALATEX_es_PASS1.txt", "LUALATEX_es_PASS2.txt",
    "LUALATEX_DIRECT_en_PASS1.txt", "LUALATEX_DIRECT_en_PASS2.txt",
    "LUALATEX_DIRECT_es_PASS1.txt", "LUALATEX_DIRECT_es_PASS2.txt",
}
unlabelled_stale = [
    path.relative_to(REPRO).as_posix()
    for path in REPRO.rglob("*")
    if path.is_file() and path.name in stale_generic_names
    and "v1.3_legacy" not in path.parts and "v1.5" not in path.parts
]
check(not unlabelled_stale, "no stale generic compiler-log name survives outside v1.3_legacy", unlabelled_stale)

failed = [item for item in checks if not item["pass"]]
result = {
    "finding": "EXT-V15-M01",
    "verdict": "PASS" if not failed else "FAIL",
    "checks_passed": sum(bool(item["pass"]) for item in checks),
    "checks_total": len(checks),
    "failed": failed,
    "checks": checks,
}
out = Path(__file__).with_name("EXT_V15_M01_CLOSURE_RESULTS.json")
out.write_text(json.dumps(result, indent=2, ensure_ascii=False) + "\n", encoding="utf-8", newline="\n")
print(json.dumps(result, indent=2, ensure_ascii=True))
raise SystemExit(0 if not failed else 1)
