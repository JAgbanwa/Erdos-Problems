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
def rename_e1(text):
    text = re.sub(r"(?<![A-Za-z])r(?![A-Za-z])", "t_W", text)
    text = re.sub(r"(?<![A-Za-z_])t(?![A-Za-z_])", "t_I", text)
    return text.replace("+rz", "+t_W z")

def normalize_o5(text):
    start = text.index("### E.1. Constructor and accounting")
    end = text.index("### E.2.", start)
    section = text[start:end]
    if r"\(r=|W|\)" in section:
        text = text[:start] + rename_e1(section) + text[end:]
    marker = "**Proof.** We first explain the retained estimate"
    if marker in text:
        start = text.index(marker)
        end = text.index("Substituting the middle bounds", start)
        section = text[start:end].replace(r"\(w=|W|\)", r"\(t_W=|W|\)")
        section = section.replace("nw", "nt_W")
        text = text[:start] + section + text[end:]
    return text

protected = [x for x in index if x["language"] == "en" and "text" in x]
relocation = json.loads((ROOT / "R2_STRUCTURAL_MAP.json").read_text(encoding="utf-8"))
def relocated(text):
    text = re.sub(r"\\tag\{([^}]+)\}",
                  lambda m: r"\tag{" + relocation["equation_map"].get(m[1], m[1]) + "}", text)
    names = relocation["result_map"]
    return re.sub('|'.join(re.escape(k) for k in sorted(names, key=len, reverse=True)),
                  lambda m: names[m[0]], text)
old_e1 = old[old.index("### E.1."):old.index("### E.2.")]
def adjusted_element(x):
    text = relocated(x["text"])
    return rename_e1(text) if x["text"] in old_e1 else text
missing = [{k: x[k] for k in ("kind", "line", "text")} for x in protected if adjusted_element(x) not in new]
before_r2 = ROOT / "review_history/before-r2-20260929/PAPER_IV_preprint_v1.2_en.md"
pre_relocation = before_r2.read_text(encoding="utf-8")
def displays(text):
    return Counter(re.sub(r"\\tag\{[^}]+\}", "", d).strip()
                   for d in re.findall(r"\\\[(.*?)\\\]", text, re.S))
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
    "legacy_equation_tags_retained_modulo_explicit_map": all(
        tags_new.count(relocation["equation_map"].get(t, t)) >= tags_old.count(t) for t in set(tags_old)),
    "pre_relocation_source_unchanged": sha(before_r2) == relocation["input_sha256"],
    "all_201_displays_retained_modulo_labels_and_scoped_O5_notation":
        not (displays(normalize_o5(pre_relocation)) - displays(new))
        and sum(displays(pre_relocation).values()) == 201,
    "current_display_count": sum(displays(new).values()),
    "all_five_lean_blocks_unchanged_since_r2": re.findall(r"```lean\n.*?```", pre_relocation, re.S)
        == re.findall(r"```lean\n.*?```", new, re.S),
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
    report["legacy_equation_tags_retained_modulo_explicit_map"], not report["duplicate_equation_tags"],
    report["pre_relocation_source_unchanged"],
    report["all_201_displays_retained_modulo_labels_and_scoped_O5_notation"],
    report["all_five_lean_blocks_unchanged_since_r2"],
    report["lean_blocks_verbatim"], report["math_delimiters_balanced"],
    report["needspace_absent"], report["reference_numbers_contiguous"], not missing_images
]
report["static_check_status"] = "PASS" if all(gates) else "FAIL"
(ROOT / "EN_REVIEW_CHECKS.json").write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
print(json.dumps(report, ensure_ascii=False, indent=2))
raise SystemExit(0 if all(gates) else 1)
