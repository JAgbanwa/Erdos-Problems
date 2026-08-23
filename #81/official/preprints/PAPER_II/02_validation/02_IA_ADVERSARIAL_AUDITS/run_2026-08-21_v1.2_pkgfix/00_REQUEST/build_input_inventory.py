from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path


EXCLUDED = "02_validation/02_IA_ADVERSARIAL_AUDITS/"


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", required=True, type=Path)
    parser.add_argument("--manifest", required=True, type=Path)
    parser.add_argument("--inventory", required=True, type=Path)
    args = parser.parse_args()
    root = args.root.resolve()

    files = []
    for path in sorted(root.rglob("*"), key=lambda item: item.relative_to(root).as_posix().lower()):
        if not path.is_file():
            continue
        relative = path.relative_to(root).as_posix()
        if relative.startswith(EXCLUDED):
            continue
        files.append({"path": relative, "bytes": path.stat().st_size, "sha256": digest(path)})

    text = "".join(f"{item['sha256']}  {item['path']}\n" for item in files)
    args.manifest.write_text(text, encoding="utf-8", newline="\n")
    manifest_sha = hashlib.sha256(text.encode("utf-8")).hexdigest()
    args.inventory.write_text(
        json.dumps(
            {
                "paper": "PAPER_II",
                "target": "preprint_draft_v1.2_package_fix",
                "excluded_prefix": EXCLUDED,
                "files": len(files),
                "bytes": sum(item["bytes"] for item in files),
                "manifest_sha256": manifest_sha,
                "manifest_algorithm": "SHA-256 of the exact INPUT_TARGET_MANIFEST.sha256 bytes; that file is UTF-8 LF-only lines '<file_sha256><two spaces><target-relative_posix_path>\\n', sorted case-insensitively by target-relative POSIX path",
                "inventory": files,
            },
            ensure_ascii=False,
            indent=2,
        )
        + "\n",
        encoding="utf-8",
        newline="\n",
    )
    print(json.dumps({"files": len(files), "bytes": sum(item["bytes"] for item in files), "manifest_sha256": manifest_sha}, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
