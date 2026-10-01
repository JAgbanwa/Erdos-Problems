"""run_v1.22_r3 FINDINGS.csv: every row of run_v1.22_r2 FINDINGS.csv kept verbatim, plus r3 columns
(status, severity, closure class, pre-publication action, proof, revision verified); new r3 rows appended.
Also the per-gate TRACEABILITY_MATRIX.csv."""
import csv, pathlib
A = pathlib.Path('C:/Users/jtraverso/e81p4-publish/preprints/PAPER_IV/02_validation/02_IA_ADVERSARIAL_AUDITS')
rows = list(csv.reader(open(A / 'run_v1.22_r2/30_REPORT/FINDINGS.csv', encoding='utf-8')))
hdr, body = rows[0], rows[1:]
idx = {h: i for i, h in enumerate(hdr)}
R3 = ['status_v1.22_r3', 'severity_v1.22_r3', 'closure_class_r3', 'action_before_publication', 'proof_r3', 'revision_verified_r3']
NONE = 'none (documented limit)'
upd = {
 'NEW-04': ('RESOLVED', '-', 'CLOSED', 'none', 'five status paragraphs per language rewritten; checked against r2 report (E6_RECORD §NEW-04; E6_R3_DELTA.json)', 'v1.22-r3'),
 'X-28': ('MITIGATED (control closed)', 'MINOR', 'MITIGATED', 'none, provided the reproduction profile keeps verify_frozen_logs.py mandatory', 'supplementary fail-closed verifier rerun in place (PASS 1266) and in test copy (15/15 + 4/4); frozen runners unchanged, not patched', 'v1.22-r3'),
 'E8-02': ('RESOLVED', '-', 'CLOSED', 'none', 'error rule kept case-sensitive (identical to frozen audit_publication.py); sorry rule separate (E8_R3_CHECK.json)', 'v1.22-r3'),
 'X-17': ('KEPT', 'OBSERVATION', 'ACCEPTED_OBSERVATION', NONE, 'extended to N8 (linear-coefficient header existential in G)', 'v1.22-r3'),
 'X-18': ('KEPT', 'OBSERVATION', 'ACCEPTED_OBSERVATION', NONE, 'unchanged', 'v1.22-r3'),
 'X-19': ('KEPT', 'OBSERVATION', 'ACCEPTED_OBSERVATION', NONE, 'unchanged', 'v1.22-r3'),
 'X-22': ('KEPT', 'OBSERVATION', 'ACCEPTED_OBSERVATION', 'none (historical fact)', 'unchanged', 'v1.22-r3'),
 'X-24': ('KEPT', 'OBSERVATION', 'ACCEPTED_OBSERVATION', 'none (author choice)', 'unchanged', 'v1.22-r3'),
 'X-29': ('KEPT', 'OBSERVATION', 'ACCEPTED_OBSERVATION', 'none (historical fact)', 'unchanged', 'v1.22-r3'),
 'R-01': ('KEPT', 'OBSERVATION', 'ACCEPTED_OBSERVATION', NONE, 'declared in A.2 (r3 paragraph states it)', 'v1.22-r3'),
 'X-26': ('KEPT', 'INFO', 'KEPT_INFO', 'none; human peer review recommended before publication decision', 'run_v1.22_r3 same session/family', 'v1.22-r3'),
}
out = []
for r in body:
    i = r[0]
    if i in upd:
        out.append(r + list(upd[i]))
    else:
        cls = r[idx['closure_class']]
        out.append(r + [r[idx['status_v1.22_r2']], r[idx['severity_v1.22_r2']], cls, 'none', 'inherited; identity re-verified in r3 (E0, diff)', 'as recorded in run_v1.22_r2'])
blank = ['-'] * len(hdr)
def mk(i, gate, loc, ev, note, st, sev, cls, act, proof, rev):
    b = list(blank); b[0], b[1] = i, gate; b[idx['location']], b[idx['evidence']], b[idx['resolution_or_remaining_step']] = loc, ev, note
    return b + [st, sev, cls, act, proof, rev]
new = [
 mk('NEW-05', 'E6', 'ES MD l.1355 (A.2 "programación numérica de C.3"), l.2356 (F.4 "cota adaptada con muestra fijada")', '20_EVIDENCE/E6/E6_RECORD.md',
    'r3 rewrites break established ES terminology ("calendario numérico" l.1599 and C.3 heading; "muestras con anclajes" F.5 l.2403, Tabla 10 l.2398)',
    'NEW', 'MINOR', 'OPEN', 'restore the two terms in ES; repeat ES identity + E6', 'found by auditor text check of the changed paragraphs', 'v1.22-r3'),
 mk('C4-01', 'E6', '20_EVIDENCE/E6/PAGE_INSPECTION_LOG.csv', '00_CONTROL/CORRECTIONS.md', '13 comparison images not confirmable as displayed; rows re-logged from displayed overview sheets',
    'CORRECTION', 'CORRECTION', 'PRESERVED_CORRECTION', 'none', 'unconfirmed rows kept separately', 'v1.22-r3'),
 mk('C4-02', 'E6', 'draft of NEW-05', '00_CONTROL/CORRECTIONS.md', 'auditor first listed "conteos" as a third terminology defect; withdrawn since "Conteos" is established (A.2 table)',
    'CORRECTION', 'CORRECTION', 'PRESERVED_CORRECTION', 'none', 'E6_RECORD.md', 'v1.22-r3'),
 mk('C4-03', 'E8', 'testcopy verifier patch', '00_CONTROL/CORRECTIONS.md', 'first sed patch failed (delimiter); harness aborted before writing; re-patched with Python; only the root path differs',
    'CORRECTION', 'CORRECTION', 'PRESERVED_CORRECTION', 'none', 'testcopy_verifier_patch.diff', 'v1.22-r3'),
]
w = csv.writer(open(A / 'run_v1.22_r3/30_REPORT/FINDINGS.csv', 'w', newline='', encoding='utf-8'))
w.writerow(hdr + R3); w.writerows(out); w.writerows(new)
import collections
print(len(out) + len(new), collections.Counter(r[-4] for r in out + new))
TH = ['gate', 'v1.2_r1', 'v1.21_r1', 'v1.22_r1', 'v1.22_r2', 'v1.22_r3_current', 'basis_r3', 'new_check_r3', 'inherited_evidence (run, path/hash)', 'identity link', 'evidence_r3']
T = [
 ['E0', 'PASS', 'PASS', 'PASS', 'PASS', 'PASS', 'ejecutado en r3 (inicial + final)', 'target, manifest 226, ZIP 228 CRC, figures = r2, comparators, Lean 615, source ZIP, annex, 4 prior runs', '-', '-', '20_EVIDENCE/E0/E0_INITIAL.json, E0_FINAL.json'],
 ['E1', 'PASS', 'PASS_WITH_MINOR', 'PASS', 'PASS', 'PASS', 'heredado y revalidado por identidad (21 rows) + ejecutado en r3 (12 new rows)', '13 headers vs sources/logs; 12 semantic rows N1-N12', 'run_v1.2_r1/20_EVIDENCE/E1/E1_RECORD.md', 'statement text unchanged; Lean 615/615', '30_REPORT/CLAIM_MAP_CONSOLIDATED.md; 20_EVIDENCE/E1/E1E3_HEADERS_CHECK.json'],
 ['E2', 'INCONCLUSIVE', 'INCONCLUSIVE', 'PASS', 'PASS', 'PASS (R-01)', 'heredado y revalidado por identidad', 'impact check only', 'run_v1.2_r1 / run_v1.21_r1 / run_v1.22_r1 E2_RECORD', 'no formula changed in r3', '20_EVIDENCE/E2/E2_RECORD.md; IMPACT/IMPACT_CHECK.json'],
 ['E3', 'PASS_WITH_FINDINGS', 'PASS', 'PASS', 'PASS', 'PASS', 'heredado y revalidado por identidad + ejecutado en r3 (static headers)', 'header/namespace/variable check', 'run_v1.2_r1 E3 (AuditorASProbe)', 'Lean 615/615', '20_EVIDENCE/E3/E3_RECORD.md'],
 ['E4', 'PASS (build)', 'PASS reused', 'PASS reused', 'PASS reused', 'PASS reused_verified_external_build', 'heredado y revalidado por identidad; no build, no kernel replay', 'documentary script rerun (identical)', 'run_v1.2_r1 console ef5b01c7, records 0f2d8495, annex 57ce1895, E4_RECORD 9ca125d2', 'Lean 615/615, source ZIP cb274145, annex 2847a422, run_v1.2_r1 1097 files', '20_EVIDENCE/E4/E4_RECORD.md, E4_REUSE_CHECK.json'],
 ['E5', 'PASS', 'PASS', 'PASS', 'PASS', 'PASS', 'heredado y revalidado por identidad', 'none (no formula changed)', 'run_v1.2_r1 T01-T24; run_v1.21_r1; run_v1.22_r1/r2 scripts', 'formulas identical', '20_EVIDENCE/E5/E5_RECORD.md'],
 ['E6', 'PASS_WITH_FINDINGS', 'PASS_WITH_FINDINGS', 'PASS_WITH_FINDINGS', 'PASS_WITH_OBSERVATIONS', 'PASS_WITH_FINDINGS (NEW-05)', 'ejecutado en r3', 'diff/protected/PDF/raster EN+ES; 145/145 pages; NEW-04 closed; NEW-05 opened', '-', '-', '20_EVIDENCE/E6/E6_RECORD.md, E6_R3_DELTA.json, PAGE_INSPECTION_LOG.csv'],
 ['E7', 'PASS_WITH_MINOR_FINDINGS', 'PASS', 'PASS', 'PASS', 'PASS', 'heredado y revalidado por identidad', 'references identical', 'run_v1.2_r1..run_v1.22_r2 E7', 'reference sections identical', '20_EVIDENCE/E7/E7_RECORD.md'],
 ['E8', 'PASS_WITH_FINDINGS', 'PASS_WITH_OBSERVATIONS', 'PASS_WITH_OBSERVATIONS', 'PASS_WITH_OBSERVATIONS', 'PASS_WITH_OBSERVATIONS', 'ejecutado en r3 + heredado', 'verifier in place (1266 PASS) + test copy (15/15, 4/4) + recount; E8-02 closed; X-28 control closed', 'run_v1.21_r1 1266-log scan', 'inventory hashes = files', '20_EVIDENCE/E8/E8_RECORD.md, E8_R3_CHECK.json'],
]
w = csv.writer(open(A / 'run_v1.22_r3/30_REPORT/TRACEABILITY_MATRIX.csv', 'w', newline='', encoding='utf-8')); w.writerow(TH); w.writerows(T)
