#!/usr/bin/env python3
"""Prove the byte identity that authorizes reusing run_2026-08-21_v1.2 evidence.

The earlier inventory records repository-relative paths, so the prefix
'PAPER_II/active/preprint_draft_v1.2/' is stripped before comparison.
"""
import hashlib
import json
import os

ROOT = "C:/p2t"
PREV = (ROOT + "/02_validation/02_IA_ADVERSARIAL_AUDITS/run_2026-08-21_v1.2"
        "/00_REQUEST/INPUT_INVENTORY.json")
PFX = "PAPER_II/active/preprint_draft_v1.2/"

REUSED = [
    ("01_manuscript/PAPER_II_preprint_draft_v1.2.md",
     "mathematics, citations, novelty, bilingual, duplicates"),
    ("01_manuscript/PAPER_II_preprint_draft_v1.2_es.md", "bilingual, duplicates"),
    ("01_manuscript/PAPER_II_preprint_draft_v1.2_en.tex", "rendered artifacts"),
    ("01_manuscript/PAPER_II_preprint_draft_v1.2_es.tex", "rendered artifacts"),
    ("01_manuscript/PAPER_II_preprint_draft_v1.2_en.pdf",
     "rendered artifacts, duplicates"),
    ("01_manuscript/PAPER_II_preprint_draft_v1.2_es.pdf",
     "rendered artifacts, duplicates"),
    ("05_formalization/lean_v1.2_freeze/PAPER_II_lean_v1.2_freeze.zip",
     "formal conformance (Gate H)"),
]


def h(p):
    return hashlib.sha256(open(p, "rb").read()).hexdigest()


def main():
    prev = {}
    for i in json.load(open(PREV))["files"]:
        k = i["path"]
        prev[k[len(PFX):] if k.startswith(PFX) else k] = i["sha256"]
    rows = []
    for rel, gates in REUSED:
        p = os.path.join(ROOT, rel)
        cur = h(p) if os.path.isfile(p) else None
        rows.append({"path": rel, "gates_reused_for": gates,
                     "previous_sha256": prev.get(rel), "current_sha256": cur,
                     "byte_identical": cur is not None and cur == prev.get(rel)})
    print(json.dumps({"rows": rows,
                      "all_byte_identical": all(r["byte_identical"] for r in rows)},
                     indent=1))


if __name__ == "__main__":
    main()
