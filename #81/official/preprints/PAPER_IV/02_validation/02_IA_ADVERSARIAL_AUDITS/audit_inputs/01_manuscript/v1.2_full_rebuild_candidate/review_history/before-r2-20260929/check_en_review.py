"""Static English-review checks; does not build Lean or certify the mathematics."""
from collections import Counter
from pathlib import Path
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parent
baseline = ROOT.parent / "v1.0.1_candidate/PAPER_IV_preprint_v1.0.1_en.md"
candidate = ROOT / "PAPER_IV_preprint_v1.2_en.md"
index = json.loads((ROOT / "PROTECTED_BASELINE.json").read_text(encoding="utf-8"))
old = baseline.read_text(encoding="utf-8")
new = candidate.read_text(encoding="utf-8")
protected = [x for x in index if x["language"] == "en" and "text" in x]
missing = [{k: x[k] for k in ("kind", "line", "text")} for x in protected if x["text"] not in new]
tags_old = re.findall(r"\\tag\{([^}]+)\}", old)
tags_new = re.findall(r"\\tag\{([^}]+)\}", new)
links = re.findall(r"!\[[^\]]*\]\(([^)]+)\)", new)
missing_images = [x for x in links if not x.startswith(("https://", "http://")) and not (ROOT / x).is_file()]
refs = re.findall(r"(?m)^\[(\d+)\] ", new)
baseline_record = next(x for x in index if x["language"] == "en" and x["kind"] == "baseline_file")
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
expected_changes = all(
    (x["kind"] == "display" and r"\tag" not in x["text"] and x["line"] == 19)
    or (x["kind"] == "result_heading" and x["text"].startswith("**Corollary 6.1a"))
    for x in missing
)
report = {
    "scope": "English Markdown review only. Static checks, not mathematical certification.",
    "baseline": str(baseline),
    "candidate": str(candidate),
    "baseline_sha256": sha(baseline),
    "candidate_sha256": sha(candidate),
    "baseline_unchanged": sha(baseline) == baseline_record["sha256"],
    "protected_counts": dict(Counter(x["kind"] for x in protected)),
    "baseline_elements_not_verbatim": missing,
    "only_declared_protected_changes": expected_changes,
    "legacy_equation_tags_retained": all(tags_new.count(t) >= tags_old.count(t) for t in set(tags_old)),
    "duplicate_equation_tags": [t for t,c in Counter(tags_new).items() if c > 1],
    "lean_blocks_verbatim": all(x["text"] in new for x in protected if x["kind"] == "lean"),
    "math_delimiters_balanced": new.count(r"\[") == new.count(r"\]") and new.count(r"\(") == new.count(r"\)"),
    "needspace_absent": r"\Needspace" not in new,
    "reference_numbers_contiguous": list(map(int, refs)) == list(range(1,24)),
    "missing_local_images": missing_images,
    "new_tags": [t for t in tags_new if t not in tags_old],
    "new_internal_or_external_manuscript_audits_performed": False,
    "spanish_synchronized": False,
    "tex_pdf_generated": False,
    "editorial_verdict": "EDITORIAL_DRAFT_WITH_OPEN_GATES"
}
gates = [
    report["baseline_unchanged"], expected_changes,
    report["legacy_equation_tags_retained"], not report["duplicate_equation_tags"],
    report["lean_blocks_verbatim"], report["math_delimiters_balanced"],
    report["needspace_absent"], report["reference_numbers_contiguous"], not missing_images
]
report["static_check_status"] = "PASS" if all(gates) else "FAIL"
(ROOT / "EN_REVIEW_CHECKS.json").write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
print(json.dumps(report, ensure_ascii=False, indent=2))
raise SystemExit(0 if all(gates) else 1)
