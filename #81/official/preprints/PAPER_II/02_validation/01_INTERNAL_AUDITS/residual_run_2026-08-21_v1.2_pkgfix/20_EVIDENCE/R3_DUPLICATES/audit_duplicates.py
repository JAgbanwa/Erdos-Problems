from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import tempfile
import unicodedata
from collections import defaultdict
from difflib import SequenceMatcher
from pathlib import Path


def normalize(text: str) -> str:
    text = unicodedata.normalize("NFKC", text)
    text = re.sub(r"\\(?:label|tag)\{[^}]*\}", "", text)
    return re.sub(r"\s+", " ", text).strip()


def paragraphs(text: str) -> list[tuple[int, str]]:
    chunks = re.split(r"(?:\r?\n\s*){2,}", text)
    out: list[tuple[int, str]] = []
    offset = 0
    for chunk in chunks:
        line = text.count("\n", 0, offset) + 1
        offset += len(chunk) + 2
        value = normalize(chunk)
        if len(value) >= 180:
            out.append((line, value))
    return out


def pdf_text(path: Path) -> str:
    with tempfile.TemporaryDirectory() as tmp:
        out = Path(tmp) / "text.txt"
        subprocess.run(["pdftotext", "-layout", str(path), str(out)], check=True, capture_output=True, text=True)
        return out.read_text(encoding="utf-8", errors="replace")


def inspect(path: Path) -> dict[str, object]:
    text = pdf_text(path) if path.suffix.lower() == ".pdf" else path.read_text(encoding="utf-8", errors="replace")
    blocks = paragraphs(text)
    exact_map: dict[str, list[int]] = defaultdict(list)
    values: dict[str, str] = {}
    for line, value in blocks:
        key = hashlib.sha256(value.encode("utf-8")).hexdigest()
        exact_map[key].append(line)
        values[key] = value
    exact = [{"lines": lines, "length": len(values[key]), "preview": values[key][:160]} for key, lines in exact_map.items() if len(lines) > 1]
    near = []
    for index, (line_a, a) in enumerate(blocks):
        for line_b, b in blocks[index + 1 :]:
            if a == b or min(len(a), len(b)) / max(len(a), len(b)) < 0.9:
                continue
            ratio = SequenceMatcher(None, a, b, autojunk=False).ratio()
            if ratio >= 0.985:
                near.append({"lines": [line_a, line_b], "ratio": round(ratio, 6), "lengths": [len(a), len(b)], "preview_a": a[:120], "preview_b": b[:120]})
    return {"file": path.name, "paragraphs_scanned": len(blocks), "exact_duplicates": exact, "near_duplicates": near, "status": "PASS" if not exact and not near else "REVIEW"}


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--manuscript-dir", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    names = [
        "PAPER_II_preprint_draft_v1.2.md",
        "PAPER_II_preprint_draft_v1.2_es.md",
        "PAPER_II_preprint_draft_v1.2_en.tex",
        "PAPER_II_preprint_draft_v1.2_es.tex",
        "PAPER_II_preprint_draft_v1.2_en.pdf",
        "PAPER_II_preprint_draft_v1.2_es.pdf",
    ]
    results = [inspect(args.manuscript_dir / name) for name in names]
    payload = {"paper": "PAPER_II", "target": "preprint_draft_v1.2", "minimum_normalized_paragraph_length": 180, "near_duplicate_threshold": 0.985, "results": results, "status": "PASS" if all(item["status"] == "PASS" for item in results) else "REVIEW"}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8", newline="\n")
    print(json.dumps(payload, ensure_ascii=False, indent=2))
    return 0 if payload["status"] == "PASS" else 2


if __name__ == "__main__":
    raise SystemExit(main())
