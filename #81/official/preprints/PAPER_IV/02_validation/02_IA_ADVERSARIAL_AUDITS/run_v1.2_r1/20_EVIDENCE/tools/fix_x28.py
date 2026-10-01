import csv
p = 'C:/Users/jtraverso/e81p4-publish/preprints/PAPER_IV/02_validation/02_IA_ADVERSARIAL_AUDITS/run_v1.2_r1/30_REPORT/FINDINGS.csv'
rows = list(csv.reader(open(p, encoding='utf-8')))
for r in rows:
    if r and r[0] == 'X-28':
        r[4] = '20_EVIDENCE/E4/AuditorNegControl.lean and .log; 00_CONTROL/CORRECTIONS.md C-07'
        r[5] = "Lean 4.28 prints: declaration uses `sorry` (backticks); both runners search the literal string: declaration uses 'sorry' (single quotes)"
        r[6] = "Per-module sorry detection in the runners is ineffective; mitigated: no 'sorry' string occurs in any auditor or author log, and axiom cones exclude sorryAx"
        r[7] = 'OPEN: fix the pattern'
csv.writer(open(p, 'w', encoding='utf-8', newline='')).writerows(rows)
print([r for r in rows if r and r[0] == 'X-28'])
