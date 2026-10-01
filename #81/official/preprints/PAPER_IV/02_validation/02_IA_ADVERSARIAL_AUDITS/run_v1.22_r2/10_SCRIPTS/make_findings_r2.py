"""Build run_v1.22_r2 FINDINGS.csv: all historical rows of run_v1.22_r1 FINDINGS.csv kept verbatim, plus
r2 columns (current status, closure class, closure proof, responsible party, revision verified). Also the
per-gate traceability matrix."""
import csv, pathlib
A = pathlib.Path('C:/Users/jtraverso/e81p4-publish/preprints/PAPER_IV/02_validation/02_IA_ADVERSARIAL_AUDITS')
rows = list(csv.reader(open(A / 'run_v1.22_r1/30_REPORT/FINDINGS.csv', encoding='utf-8')))
hdr, body = rows[0], rows[1:]
# closure class: CLOSED / MITIGATED / ACCEPTED_OBSERVATION / PRESERVED_CORRECTION / KEPT_INFO
upd = {
 'X-15': ('RESOLVED', '-', 'CLOSED', 'r2 ES prose: 0 residual matching(s)/packing; reference titles untouched (E6_R2_DELTA.json; PAGE_INSPECTION_LOG pp.16,18,20,21,55,56,61); count corrected to 11+1 (C3-01)', 'editor (text); auditor (count)', 'v1.22-r2'),
 'NEW-01': ('RESOLVED', '-', 'CLOSED', 'ES §7.2 `Model` monospace: MD l.1203 / TeX l.1084 / PDF p.35 (zoom 140 dpi)', 'editor', 'v1.22-r2'),
 'NEW-03': ('RESOLVED', '-', 'CLOSED', 'corrected artefact (E6) + explicit editor rectification (CORRECTIONS_AND_HANDOFF_v1.22_r2.md item 3); r1 response preserved', 'editor', 'v1.22-r2'),
 'X-28': ('MITIGATED', 'MINOR', 'MITIGATED', 'external detector rerun: 10/10 cases, 1266 logs, 0 hits; runner hashes = manifest; patch not applied', 'author (runners unchanged)', 'v1.21 (mitigation); re-confirmed v1.22-r2'),
 'R-01': ('KEPT', 'OBSERVATION', 'ACCEPTED_OBSERVATION', 'declared expository limit (second-moment B_q bounds cited, not derived)', 'author', 'v1.21; kept v1.22-r1, v1.22-r2'),
 'E8-02': ('KEPT', 'OBSERVATION', 'ACCEPTED_OBSERVATION', 'patch scope note; moot while patch not applied', 'author', 'v1.21; kept'),
 'X-26': ('KEPT', 'INFO', 'KEPT_INFO', 'run_v1.22_r2 continues the same session/model as all prior runs; not blind; same family as manuscript assistant', 'auditor', 'all'),
}
def cls_of(st):
    if st.startswith('RESOLVED'): return 'CLOSED'
    if st == 'MITIGATED': return 'MITIGATED'
    if st in ('CORRECTION', 'PROCESS'): return 'PRESERVED_CORRECTION'
    if st == 'KEPT': return 'ACCEPTED_OBSERVATION'
    return 'CHECK'
R2 = ['status_v1.22_r2', 'severity_v1.22_r2', 'closure_class', 'closure_proof_r2', 'responsible', 'revision_verified']
out_hdr = hdr + R2
out = []
for r in body:
    i, st, sv = r[0], r[8], r[9]
    if i in upd:
        out.append(r + list(upd[i]))
    else:
        cls = 'PRESERVED_CORRECTION' if (i.startswith('C2-') or i.startswith('AUD-')) else cls_of(st)
        out.append(r + [st, sv, cls, 'inherited; identity of covered text/source re-verified in r2 (E0, auditor diff)', '-', 'as recorded in run_v1.22_r1'])
blank = ['-'] * len(hdr)
def mk(i, gate, loc, ev, note, st, sev, cls, proof, resp, rev):
    b = list(blank); b[0], b[1] = i, gate; b[10], b[11], b[12] = loc, ev, note
    return b + [st, sev, cls, proof, resp, rev]
new = [
 mk('NEW-04', 'E6', 'ES/EN p.1 status; §7 "Estado/Audit status"; A.1 Table 7 note; A.2 scope (ES p.1, 33, 39, 40)', '20_EVIDENCE/E6/E6_RECORD.md', 'Historical status text says the v1.22 extensions await revalidation and names run_v1.21_r1 as latest; stale relative to the current state',
    'NEW', 'OBSERVATION', 'ACCEPTED_OBSERVATION', 'not changed by design (mandate §4, EN byte identity); must be updated in both languages before any publication, followed by a new identity check', 'editor', 'v1.22-r2'),
 mk('C3-01', 'E6', 'run_v1.21_r1 / run_v1.22_r1 X-15 narrative count', '00_CONTROL/CORRECTIONS.md', 'Auditor count error: "12 matching(s)" narrated; correct is 11 matching(s) + 1 packing',
    'CORRECTION', 'CORRECTION', 'PRESERVED_CORRECTION', 'recorded; prior reports not rewritten', 'auditor', 'v1.22-r2'),
 mk('C3-02', 'E6', '20_EVIDENCE/E6/PAGE_INSPECTION_LOG.csv', '00_CONTROL/CORRECTIONS.md', 'Rows written for comparison images that were not displayed; discarded and re-inspected',
    'CORRECTION', 'CORRECTION', 'PRESERVED_CORRECTION', 'discarded rows kept in a separate file', 'auditor', 'v1.22-r2'),
 mk('C3-03', 'E5', 'e5_v122_c3_negfix.py output path', '00_CONTROL/CORRECTIONS.md', 'Output written to the run root, moved; nothing written outside run_v1.22_r2',
    'CORRECTION', 'CORRECTION', 'PRESERVED_CORRECTION', 'E0 final confirms prior runs unchanged', 'auditor', 'v1.22-r2'),
]
w = csv.writer(open(A / 'run_v1.22_r2/30_REPORT/FINDINGS.csv', 'w', newline='', encoding='utf-8'))
w.writerow(out_hdr); w.writerows(out); w.writerows(new)
print(len(out), len(new), len(out_hdr)); import collections; print(collections.Counter(r[15] for r in out + new))
