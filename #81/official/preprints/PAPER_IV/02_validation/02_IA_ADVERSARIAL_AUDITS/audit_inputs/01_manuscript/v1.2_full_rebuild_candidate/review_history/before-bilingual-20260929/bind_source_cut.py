"""Bind English review metadata to an existing validated source freeze.

Updates evidence/status prose only, and refuses to alter any displayed formula
or literal Lean block. Does not generate or certify other manuscript formats.
"""
from pathlib import Path
from collections import Counter
import argparse
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parent
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('record')
args = parser.parse_args()
record = json.loads(Path(args.record).read_text(encoding='utf-8'))
assert record['status'] == 'LOCAL_SOURCE_FREEZE'
cut, count = record['freeze_id'], record['lean_modules']
entries, axioms = record['source_entries'], record['axiom_records_checked']
summary = record['build_summary']
assert summary['status'] == 'PASS'
assert hashlib.sha256(Path(record['archive']).read_bytes()).hexdigest() == record['archive_sha256']
path = ROOT / 'PAPER_IV_preprint_v1.2_en.md'
before = path.read_text(encoding='utf-8')
assert cut not in before, 'Source cut is already bound; do not silently repeat edits'
lines = before.splitlines()
changes = {
    '**Status:': f'**Status:** English Markdown review candidate. The Lean sources are locally frozen as `{cut}` after the combined build and fresh execution of all 19 selected targets. The source cut includes E35, the explicit public Theorem C and the square-root obstruction. Spanish synchronization, typesetting and renewed internal and external adversarial audits of the enlarged manuscript remain pending. Earlier audit verdicts do not certify this edition. It has not been published or assigned its own DOI.',
    'The export check contains 207': 'The export check contains 224 literal `#check` commands through `import PaperIV` alone. All passed in the new cut. This establishes access to that list, not that every declaration in the supplement belongs to the canonical interface. ResearchAudit traverses types and proof terms for 75 selected extension declarations; the six-declaration OptimalTemplateObstructionAudit and the other targets provide their own scoped checks. BoundedCliqueGap remains a separate annex, not a premise of the main theorem.',
    'The source cut `piv-stability-': f'The source cut `{cut}` contains {count} Lean modules and {entries} source/configuration/documentation entries. The final serial run compiled {summary["pass"]} modules and validated {summary["upToDate"]} cache hits; none failed, was blocked or was omitted. All 19 selected targets were freshly executed with exit code zero. The output contains {axioms} axiom records, each restricted to `propext`, `Classical.choice`, `Quot.sound` or a subset; these records are not a count of distinct theorems. Every local object was matched to a successful build record and its current source and dependency hashes. The manifest SHA-256 is `{record["manifest_sha256"]}`; the source-only archive SHA-256 is `{record["archive_sha256"]}`. Logs, provenance and target lists are retained in `03_reproducibility/build_{cut}/`. This is a local formal check and source freeze, not a completed internal or independent audit of version 1.2.',
    'The integration additions have separate local records.': 'The earlier cut `piv-stability-fe9bb18343da` and the separate integration runs are preserved under their original identities. The new cut supersedes their role as the selected source identity; it does not rewrite their evidence. The four E35L modules and FDCheck.TowerAudit were removed from the new tree because E35 supersedes their estimates and none belongs to the selected dependency closure. All remaining local Lean modules lie in the closure of the 19 selected targets. That closure includes historical definitions and comparison checks; it is not claimed to be the smallest possible proof library.',
    'The series repository, available at': 'The series repository, available at <https://github.com/jtraverso/erdos-81-chordal-clique-partitions>, contains the manuscripts and materials for Papers I–III [2–4] and the public v0.8 draft of Paper IV, identified by commit `f783a792404a60983a7ef754d055fbe6c341188b`. That commit identifies only the earlier version. The new source freeze supporting this candidate is identified locally above; no repository commit or publication date has been assigned to this candidate.',
    "The combined run's 17 targets": 'The single audit command described in §7 executes all 19 targets, including the root, the individual audit targets and the export check. Lean and dependency revisions are recorded in lean-toolchain and lake-manifest.json. Compilation, public export, axiom inspection and semantic correspondence are distinct checks. The new source freeze is identified locally; new internal and adversarial reviews of this enlarged source-and-manuscript pair remain pending.',
    'In the following table the prefix is PaperIV.SublinearResearch': 'In the following table the prefix is PaperIV.SublinearResearch, except for the explicitly named E32 entry. All listed files belong to the new source freeze identified in §7. ResearchAudit checks these interfaces; FDCheck.FinalAudit and E34.Audit check the fixed-defect assembly and removal development separately. E35, the public Theorem C adapter and the square-root obstruction are included in the same cut, with their specific checks listed below.',
    'The four finite lemmas above are already in the historical freeze.': 'The new source freeze includes the four finite lemmas above and E35.theoremC_tower, theoremC_tower_uniform, theoremC_tower_uniform_sMax and NfarE_le_tower_poly for (6.28)–(6.29) and (C.4). The public adapter is PaperIV.DefectExplicitPublication; FDCheck.ASCheck checks the selected removal dependencies. Proposition 6.3a is supported by PaperIV.OptimalTemplateObstruction.shifted_template_witness, shifted_template_sqrt_witness and no_linear_optimal_template_bound; optimal_family_nonempty verifies that the comparison is not vacuous. Their fresh audit results and source identity are described in §7.'
}
for prefix, replacement in changes.items():
    found = [i for i, line in enumerate(lines) if line.startswith(prefix)]
    assert len(found) == 1, (prefix, found)
    lines[found[0]] = replacement
after = '\n'.join(lines) + '\n'
assert Counter(re.findall(r'\\\[.*?\\\]', before, re.S)) == Counter(re.findall(r'\\\[.*?\\\]', after, re.S))
assert re.findall(r'```lean\n.*?```', before, re.S) == re.findall(r'```lean\n.*?```', after, re.S)
path.write_text(after, encoding='utf-8')

claim = ROOT / 'V1.2_CLAIM_MAP.md'
text = claim.read_text(encoding='utf-8')
text = text.replace('Source root: ../../05_formalization/lean_piv-stability-fe9bb18343da/',
                    f'Selected source root: ../../05_formalization/lean_{cut}/')
text = text.replace('This delta is not in the historical freeze above.',
                    'The integration additions listed below are included in the selected new freeze; they were not in the historical cut.')
text += f'\n## Selected source cut after the second review\n\n`{cut}`: {count} Lean modules, {entries} manifest entries, 19 freshly executed targets, 224 exports and {axioms} standard-axiom records. The single command is `python tools/audit_publication.py`. This supersedes the historical counts as the current source identity. The combined local record and all cache provenance are in `../../03_reproducibility/build_{cut}/`; the freeze record is `../../04_integrity/FREEZE_{cut}.json`. Manuscript audits remain pending.\n'
claim.write_text(text, encoding='utf-8')

report = ROOT / 'V1.2_EN_REVIEW_REPORT.md'
text = report.read_text(encoding='utf-8')
text = text.replace('The historical source freeze already exists and remains unchanged. The validated integration additions require a new source identity before publication; the old identity does not cover them.',
                    f'The historical source freeze remains unchanged. The new selected source identity is {cut}; it includes the integration additions. Binding the final bilingual manuscripts and performing their audits are still pending.')
text = text.replace('| CQ12-06 | Validate the integration delta, create a new source identity, and bind it to the reviewed manuscripts | Release preparation; no old audit PASS carries forward |',
                    '| CQ12-06 | Integration and new Lean source identity complete; bind the final bilingual manuscript pair after author review | Release preparation; no old manuscript-audit PASS carries forward |')
text += f'\n## 8. Authorized second-review closure and selected source identity\n\nThe editorial decisions and preserved mathematical substance are recorded in V1.2_R2_EDITORIAL_CLOSURE.md. The source cut `{cut}` contains {count} Lean modules and {entries} manifest entries. The serial verification compiled {summary["pass"]} targets and reused {summary["upToDate"]} validated dependency objects. All 19 targets were freshly executed, all 224 exports checked, and all {axioms} printed axiom records were subsets of the three standard axioms. There were no failed, blocked or omitted modules. Sources, configuration, cached-object provenance and ZIP members were verified. This completes the local source freeze, not the internal or adversarial manuscript audit.\n\nThe single audit command is `python tools/audit_publication.py`. The removed five modules have a recoverable backup; earlier freezes remain untouched. The English revision is still the only manuscript deliverable in this pass.\n'
report.write_text(text, encoding='utf-8')

readme = ROOT / 'README.md'
text = readme.read_text(encoding='utf-8')
head = text.split('## Lean authority')[0]
readme.write_text(head + f'''## Lean authority

The selected local source freeze is **{cut}**:

- Source tree: `../../05_formalization/lean_{cut}/`.
- Freeze record: `../../04_integrity/FREEZE_{cut}.json`.
- Evidence: `../../03_reproducibility/build_{cut}/`.
- {count} Lean modules, 19 freshly executed targets, 224 exports;
  {axioms} printed standard-axiom records.
- One audit command: `python tools/audit_publication.py`, with the existing
  pinned dependency cache attached as described in docs/PUBLICATION_AUDIT.md.

The cut includes E35, the explicit public Theorem C and the square-root
obstruction. Exactly five superseded unused modules were retired. The historical
cut piv-stability-fe9bb18343da and all earlier evidence remain unchanged.

## Second-review editorial changes

See V1.2_R2_EDITORIAL_CLOSURE.md and R2_STRUCTURAL_MAP.json. The static check
preserves all 201 displays modulo labels and all five Lean blocks. The new
Figure 4 explains the proof of C′; that proof stays in the main body.

This is a local source freeze, not a frozen bilingual manuscript or an internal
or external audit PASS. After English approval: synchronize Spanish, generate
and inspect both typeset versions, identify that pair, then repeat the audits.
No GitHub publication, tag or deposit has been made.
''', encoding='utf-8')
print(cut)
