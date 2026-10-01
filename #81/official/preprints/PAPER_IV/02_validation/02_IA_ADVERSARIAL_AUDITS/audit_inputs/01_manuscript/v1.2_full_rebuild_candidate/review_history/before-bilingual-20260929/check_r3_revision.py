"""Bounded editorial regression checks, not a mathematical proof checker."""
from pathlib import Path
import difflib
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parent
NAME = "PAPER_IV_preprint_v1.2_en.md"
BASE = ROOT / "review_history/before-r3-errata-20260929" / NAME
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()


def continuation_warnings(text):
    """Flag possible missing operators; intentional multiplication also matches."""
    findings = []
    for block in re.finditer(r"\\\[(.*?)\\\]", text, re.S):
        lines = block[1].splitlines()
        start = text[:block.start(1)].count("\n") + 1
        for i in range(1, len(lines)):
            prev, current = lines[i - 1].strip(), lines[i].strip()
            prev = re.sub(r"(?:\\(?:quad|qquad)\s*)+$", "", prev).rstrip()
            if not current.startswith((r"\frac", r"\sum")) or not prev:
                continue
            if prev.endswith(("+", "-", "=", ",", ";", r"\\", r"\le", r"\ge")):
                continue
            if prev.startswith((r"\begin{", r"\end{")):
                continue
            findings.append({"line": start + i, "previous": prev, "current": current})
    return findings


def check():
    old, new = BASE.read_text(encoding="utf-8"), (ROOT / NAME).read_text(encoding="utf-8")
    changes = [
        (r"\le(s-\nu)c-\frac{2n}{9}" + "\n  " + r"\frac",
         r"\le(s-\nu)c-\frac{2n}{9}+" + "\n  " + r"\frac"),
        (r"d_E(G,F)&\le\operatorname{conf}(\psi)" + "\n",
         r"d_E(G,F)&\le\operatorname{conf}(\psi)+" + "\n"),
        (r"Every clique in \(\mathcal L\) has fewer than",
         r"Every clique in \(\mathcal L\) has at most"),
        ("whereas D.1 gives", "whereas Proposition D.1 gives"),
    ]
    expected = old
    unique = []
    for before, after in changes:
        unique.append(expected.count(before) == 1)
        expected = expected.replace(before, after, 1)
    negative_checks = []
    for before, after in changes[:2]:
        suffix = r"\sum_c x_c" if "conf" in before else ""
        malformed = "\\[\n" + before + suffix + "\n\\]"
        restored = "\\[\n" + after + suffix + "\n\\]"
        negative_checks.append(bool(continuation_warnings(malformed))
                               and not continuation_warnings(restored))
    lean_pattern = chr(96) * 3 + r"lean.*?" + chr(96) * 3
    report = {
        "scope": "Two operator restorations and two prose edits; no Lean execution.",
        "input_sha256": sha(BASE),
        "output_sha256": sha(ROOT / NAME),
        "input_identity_matches": sha(BASE) == "51a1dd71a6a6cfe47bb3b8c8c7e4f3d890f42e4ce03adf4bf69e9f1a1cb6629c",
        "each_replacement_unique": all(unique),
        "only_four_declared_edits": new == expected,
        "display_count": len(re.findall(r"\\\[(.*?)\\\]", new, re.S)),
        "lean_blocks_unchanged": re.findall(lean_pattern, old, re.S) == re.findall(lean_pattern, new, re.S),
        "both_negative_operator_controls_detected": all(negative_checks),
        "continuation_warnings_before": continuation_warnings(old),
        "continuation_warnings_after": continuation_warnings(new),
        "warning_policy": "Heuristic only; inspect warnings, never insert operators automatically.",
        "editorial_verdict": "EDITORIAL_DRAFT_WITH_OPEN_GATES",
    }
    gates = [report[k] for k in ("input_identity_matches", "each_replacement_unique",
                                "only_four_declared_edits", "lean_blocks_unchanged",
                                "both_negative_operator_controls_detected")]
    report["static_check_status"] = "PASS" if all(gates) else "FAIL"
    (ROOT / "R3_REVIEW_CHECKS.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    (ROOT / "R3_MANUSCRIPT.diff").write_text("".join(difflib.unified_diff(
        old.splitlines(True), new.splitlines(True), fromfile="before-r3/" + NAME,
        tofile=NAME)), encoding="utf-8")
    print(json.dumps(report, indent=2))
    return all(gates)


if __name__ == "__main__":
    raise SystemExit(0 if check() else 1)
