"""Build run_v1.22_r1 FINDINGS.csv from run_v1.21_r1 FINDINGS.csv (historical columns kept verbatim) plus v1.22 columns."""
import csv, pathlib
A = pathlib.Path('C:/Users/jtraverso/e81p4-publish/preprints/PAPER_IV/02_validation/02_IA_ADVERSARIAL_AUDITS')
rows = list(csv.reader(open(A / 'run_v1.21_r1/30_REPORT/FINDINGS.csv', encoding='utf-8')))
hdr, body = rows[0], rows[1:]
inherit = lambda st, sev: (st, sev, '-', 'inherited (text/evidence unchanged; E0 identity)', 'run_v1.21_r1 status carried over')
upd = {
 'X-05': ('RESOLVED', '-', 'C.3 (EN p48-51; ES p49-52); A.2 scope (p40)', 'E2_RECORD.md checks 1-6; E5 C3a-C3n', 'Regularity bound defined = Mathlib initialBound/stepBound/bound; I=k0, H=h; five-term absorption <= B^6; tower 4t_j<=T(j+5) gives T(h+7); A.2 pointer fixed. A2-4 ACCEPTABLE_SUMMARY'),
 'X-12': ('RESOLVED', '-', 'EN p65-66; ES p67', 'E6_RECORD.md; zoom en_p065, es_p067', 'E34.lemma3 and E34.transfer now monospaced'),
 'X-15': ('PARTIAL', 'MINOR', 'ES MD l.526,578,688,746(x2),1892,1917,1959,2177,2182(x2),2184; PDF p16,18,20,21,55,56,61', 'E6_RECORD.md; E6_X15_NEW01_SCAN.json', "Figure 3 'valor base' fixed; 12 'matching(s)' + 1 'packing' remain in ES prose (same set as v1.21). Author response claims translation: inaccurate"),
 'X-10': ('RESOLVED', '-', 'ref [5] EN p71 / ES p72', 'E7_RECORD.md', "Spelling observation closed: 'Preference Labs'"),
 'X-26': ('KEPT', 'INFO', 'independence', '00_CONTROL/AUDITOR_DECLARATION.json', 'run_v1.22_r1 is a continuation of the SAME session as run_v1.2_r1 and run_v1.21_r1; not blind; same family; same machine/cache'),
 'X-27': ('RESOLVED (preserved)', '-', '7 (p31), Table 9, [23]', 'E3_RECORD.md; E6_RECORD.md', 'Disclosure preserved verbatim; Lean unchanged'),
 'X-28': ('MITIGATED', 'MINOR', 'frozen runners', 'E8_RECORD.md; E8_DETECTOR_RERUN.json', 'Patch not applied (runner hashes = manifest); external detector rerun: 1266 logs 0 hits'),
 'NEW-01': ('PARTIAL', 'MINOR', 'ES 7.2 MD l.1203 / TeX l.1084 / PDF p35', 'E6_RECORD.md; E6_X15_NEW01_SCAN.json; CORRECTIONS C2-08', "EN 5.1 heading, A.2 row, ES Lemma 3.2 heading and EN `Model` fixed; ES 'ganancia acotada de Model' still roman (v1.2 had `Model`); missed by run_v1.21_r1"),
 'NEW-02': ('RESOLVED', '-', 'ES ref [6] (p72)', 'E6_RECORD.md; E7_RECORD.md; zoom es_p072', 'Original title restored'),
 'R-01': ('KEPT', 'OBSERVATION', 'C.2 second-moment inputs', 'E2_RECORD.md', 'Declared expository limit; no new reason to raise'),
 'R-02': ('RESOLVED', '-', 'C.2 (EN p47 / ES p48)', 'E2_RECORD.md', "Sentence 'the sum includes every active profile containing both classes of q' added; matches PatternTransfer.servingT"),
 'E8-01': ('RESOLVED', '-', 'author response E8-01 row', 'E8_RECORD.md; E8_DETECTOR_RERUN.json', '844 (author) vs 1266 (prior auditor) attributed correctly; auditor rescan repeated, identical'),
 'E8-02': ('KEPT', 'OBSERVATION', 'proposed patch', 'E8_RECORD.md', 'Patch not applied; observation on re.I scope remains moot until applied'),
 'E8-03': ('RESOLVED', '-', 'v1.22 candidate dir', 'E0_INITIAL/FINAL other_zips_in_dir=[]', 'Single bound r1 package'),
}
out_hdr = hdr + ['status_v1.22', 'severity_v1.22', 'location_v1.22', 'evidence_v1.22', 'note_v1.22']
out = []
for r in body:
    i = r[0]
    if i in upd: out.append(r + list(upd[i]))
    else: out.append(r + list(inherit(r[3], r[4])))
new = [
 ['NEW-03', 'E6/E8', '-', '-', '-', 'NEW', 'MINOR', 'RESPONSE_TO_REVALIDATION_v1.22.md rows X-15, NEW-01', 'E6_RECORD.md; E8_RECORD.md', 'Author response overstates fixes: X-15 prose not translated; Model restored in EN only'],
 ['C2-01', 'E5', '-', '-', '-', 'CORRECTION', 'CORRECTION', 'e5_v122_c3.py C3m', '00_CONTROL/CORRECTIONS.md', 'Auditor negative control mis-specified; corrected and supplemented'],
 ['C2-02..05', 'E6', '-', '-', '-', 'CORRECTION', 'CORRECTION', 'PAGE_INSPECTION_LOG.csv', '00_CONTROL/CORRECTIONS.md', 'Premature/unconfirmed page-log rows discarded; final log only from displayed sheets; interim progress messages overstated coverage'],
 ['C2-06', 'E4', '-', '-', '-', 'CORRECTION', 'CORRECTION', '10_LOGS/E4_reuse_check.log', '00_CONTROL/CORRECTIONS.md', 'Console encoding error on first run; rerun identical'],
 ['C2-07', 'ALL', '-', '-', '-', 'CORRECTION', 'CORRECTION', 'filesystem listing', '00_CONTROL/CORRECTIONS.md; INPUT_ACCESS_LOG.csv', 'Over-broad find listed an out-of-scope path name; not opened'],
 ['C2-08', 'E6', '-', '-', '-', 'CORRECTION', 'CORRECTION', 'run_v1.21_r1 E1/E6', '00_CONTROL/CORRECTIONS.md', 'Prior auditor missed ES Model residual; recorded under NEW-01'],
]
w = csv.writer(open(A / 'run_v1.22_r1/30_REPORT/FINDINGS.csv', 'w', newline='', encoding='utf-8'))
w.writerow(out_hdr); w.writerows(out)
for n in new: w.writerow(n[:5] + ['-', '-', '-'] + n[5:])
print(len(out), len(new))
