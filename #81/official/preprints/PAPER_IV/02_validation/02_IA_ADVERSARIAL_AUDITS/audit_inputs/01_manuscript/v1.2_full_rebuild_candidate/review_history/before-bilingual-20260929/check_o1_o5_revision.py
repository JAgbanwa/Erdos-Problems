"""Compare the authorized proof exposition with its preserved input; no Lean build."""
from collections import Counter
from pathlib import Path
import difflib
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parent
PAPER = ROOT.parent.parent
BEFORE = ROOT / "review_history/before-o1-o5-20260929/PAPER_IV_preprint_v1.2_en.md"
AFTER = ROOT / "PAPER_IV_preprint_v1.2_en.md"
EXPECTED_INPUT = "26cd86297512b9fa3ad00aa5be2f47ef438b05fa0f29a32d9ce1155960a83c92"
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
old = BEFORE.read_text(encoding="utf-8")
new = AFTER.read_text(encoding="utf-8")

def normalize(text):
    a = text.index("### E.1.")
    b = text.index("### E.2.", a)
    section = re.sub(r"(?<![A-Za-z])r(?![A-Za-z])", "t_W", text[a:b])
    section = re.sub(r"(?<![A-Za-z_])t(?![A-Za-z_])", "t_I", section)
    section = section.replace("+rz", "+t_W z")
    text = text[:a] + section + text[b:]
    a = text.index("**Proof.** We first explain the retained estimate")
    b = text.index("Substituting the middle bounds", a)
    section = text[a:b].replace(r"\(w=|W|\)", r"\(t_W=|W|\)").replace("nw", "nt_W")
    return text[:a] + section + text[b:]

display_re = re.compile(r"\\\[.*?\\\]", re.S)
lean_re = re.compile(chr(96)*3 + r"lean\n.*?" + chr(96)*3, re.S)
displays = lambda text: Counter(display_re.findall(text))
expected_displays = displays(normalize(old))
result_re = re.compile(r"(?m)^(?:#{2,4} |\*\*)(?:Theorem|Lemma|Corollary|Proposition) [^\n]+")
def statements(text):
    result = []
    for match in result_re.finditer(text):
        start = match.start()
        ends = [m.start() for m in re.finditer(r"(?m)^(?:\*\*Proof\.|#{2,4} |\*\*(?:Theorem|Lemma|Corollary|Proposition) )", text[match.end():])]
        end = match.end() + min(ends) if ends else len(text)
        result.append(text[start:end].strip())
    return result

protected = []
for kind, pattern in [("display", display_re), ("lean", lean_re)]:
    for i, match in enumerate(pattern.finditer(old), 1):
        protected.append({"id": f"{kind}-{i}", "kind": kind,
                          "line": old.count("\n", 0, match.start()) + 1,
                          "text": match[0],
                          "sha256": hashlib.sha256(match[0].encode()).hexdigest(),
                          "allowed_change": "O5 scoped variable renaming only" if kind == "display" else "none"})
for i, statement in enumerate(statements(old), 1):
    protected.append({"id": f"statement-{i}", "kind": "statement", "text": statement,
                      "sha256": hashlib.sha256(statement.encode()).hexdigest(),
                      "allowed_change": "none"})
(ROOT / "O1_O5_PROTECTED_INPUT.json").write_text(
    json.dumps({"source_sha256": sha(BEFORE), "elements": protected}, ensure_ascii=False, indent=2) + "\n",
    encoding="utf-8")

manifest_path = PAPER / "03_reproducibility/build_piv-v12-fb459343d234/SOURCE_MANIFEST.json"
manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
freeze = json.loads((PAPER / "04_integrity/FREEZE_piv-v12-fb459343d234.json").read_text(encoding="utf-8"))
source = PAPER / "05_formalization/lean_piv-v12-fb459343d234"
source_failures = [row["path"] for row in manifest
                   if not (source / row["path"]).is_file() or sha(source / row["path"]) != row["sha256"]]
missing_statements = [s.splitlines()[0] for s in statements(old) if s not in new]
missing_displays = list((expected_displays - displays(new)).elements())
tags_old = re.findall(r"\\tag\{([^}]+)\}", old)
tags_new = re.findall(r"\\tag\{([^}]+)\}", new)
report = {
    "scope": "English v1.2 proof exposition. Static preservation and frozen-source integrity, not a new mathematical audit.",
    "input_sha256": sha(BEFORE), "output_sha256": sha(AFTER),
    "input_identity_matches": sha(BEFORE) == EXPECTED_INPUT,
    "input_display_count": sum(displays(old).values()),
    "output_display_count": sum(displays(new).values()),
    "missing_old_displays_after_scoped_O5_renaming": missing_displays,
    "protected_statement_count": len(statements(old)),
    "missing_or_modified_statement_blocks": missing_statements,
    "lean_blocks_unchanged": lean_re.findall(old) == lean_re.findall(new),
    "old_tags_retained": not (Counter(tags_old) - Counter(tags_new)),
    "new_tags": [t for t in tags_new if t not in tags_old],
    "duplicate_tags": [t for t, count in Counter(tags_new).items() if count > 1],
    "frozen_manifest_identity_matches": sha(manifest_path) == freeze["manifest_sha256"],
    "frozen_source_entries_checked": len(manifest),
    "frozen_source_mismatches": source_failures,
    "frozen_archive_identity_matches": sha(Path(freeze["archive"])) == freeze["archive_sha256"],
    "no_control_characters": not any(ord(c) < 32 and c not in "\n\r" for c in new),
    "new_internal_or_external_audit": False,
    "lean_build_started": False,
    "tex_pdf_generated": False,
    "spanish_synchronized": False,
    "verdict": "EDITORIAL_DRAFT_WITH_OPEN_GATES",
}
checks = [report["input_identity_matches"], not missing_statements, not missing_displays,
          report["lean_blocks_unchanged"], report["old_tags_retained"], not report["duplicate_tags"],
          report["frozen_manifest_identity_matches"], not source_failures,
          report["frozen_archive_identity_matches"], report["no_control_characters"]]
report["static_status"] = "PASS" if all(checks) else "FAIL"
(ROOT / "O1_O5_REVIEW_CHECKS.json").write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
(ROOT / "O1_O5_MANUSCRIPT.diff").write_text("".join(difflib.unified_diff(
    old.splitlines(keepends=True), new.splitlines(keepends=True),
    fromfile=str(BEFORE.relative_to(ROOT)), tofile=AFTER.name)), encoding="utf-8")
print(json.dumps(report, ensure_ascii=False, indent=2))
raise SystemExit(0 if all(checks) else 1)
