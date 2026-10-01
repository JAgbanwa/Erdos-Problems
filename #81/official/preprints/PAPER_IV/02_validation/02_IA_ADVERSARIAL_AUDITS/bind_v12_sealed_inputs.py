"""Bind completed source/build/manuscripts, without authorizing or starting an audit."""
from pathlib import Path
import hashlib
import json
import zipfile

HERE = Path(__file__).resolve().parent
PAPER = HERE.parent.parent
MAN = PAPER / '01_manuscript/v1.2_full_rebuild_candidate'
EVIDENCE = PAPER / '03_reproducibility/full_rebuild_v12_20260929_seal'

def read(p):
    return json.loads(p.read_text(encoding='utf-8'))

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def bind(p):
    return {'path': p.relative_to(PAPER).as_posix(), 'sha256': sha(p), 'bytes': p.stat().st_size}

def write(p, obj):
    p.write_text(json.dumps(obj, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')

target_path = HERE / 'AUDIT_TARGET_v1.2.json'
target = read(target_path)
assert target['external_audit'] == 'NOT_STARTED' and not target['execution_authorized']
assert target['required_final_bindings']['internal_audit_package'] is None
freeze = read(MAN / 'MANUSCRIPT_FREEZE.json')
assert freeze['freeze_id'] == 'piv-v12-manuscripts-2451d43bface'
assert sha(MAN / 'MANUSCRIPT_MANIFEST.json') == freeze['manifest_sha256']
rows = read(MAN / 'MANUSCRIPT_MANIFEST.json')['files']
for row in rows:
    assert sha(MAN / row['path']) == row['sha256'], row['path']
archive = Path(freeze['archive'])
assert sha(archive) == freeze['archive_sha256']
with zipfile.ZipFile(archive) as z:
    assert z.testzip() is None
    assert set(z.namelist()) == {r['path'] for r in rows} | {'MANUSCRIPT_MANIFEST.json'}
    for row in rows:
        assert hashlib.sha256(z.read(row['path'])).hexdigest() == row['sha256']
for row in target['verified_source_files']:
    assert sha(PAPER / row['path']) == row['sha256']
evidence_seal = read(EVIDENCE / 'EVIDENCE_SEAL.json')
assert evidence_seal['status'] == 'PASS_LOCAL_RECORDED_BUILD_REVALIDATION'
assert sha(EVIDENCE / 'EVIDENCE_MANIFEST.json') == evidence_seal['manifest_sha256']
evidence_archive = Path(evidence_seal['archive'])
assert sha(evidence_archive) == evidence_seal['archive_sha256']
for row in read(EVIDENCE / 'EVIDENCE_MANIFEST.json')['files']:
    assert sha(PAPER / '03_reproducibility' / row['path']) == row['sha256']
with zipfile.ZipFile(evidence_archive) as z:
    assert z.testzip() is None

scope_path = HERE / 'LOCAL_INPUT_SCOPE_v1.2.json'
scope = read(scope_path)
scope['status'] = 'BLOCKED_PENDING_INTERNAL_AUDIT'
scope['allowed_from_intake'].append('02_validation/02_IA_ADVERSARIAL_AUDITS/bind_v12_sealed_inputs.py') if '02_validation/02_IA_ADVERSARIAL_AUDITS/bind_v12_sealed_inputs.py' not in scope['allowed_from_intake'] else None
scope['allowed_after_ready'].append('The bound historical v1.0 base source ZIP/configuration solely to reproduce the separate BoundedCliqueGap annex; not other historical research.') if not any('historical v1.0 base' in x for x in scope['allowed_after_ready']) else None
write(scope_path, scope)

target['status'] = 'BLOCKED_PENDING_INTERNAL_AUDIT'
target['manuscript_freeze'] = freeze['freeze_id']
target['expected_main_scope']['axiom_record_count'] = 461
target['expected_main_scope']['axiom_records_are_distinct_theorems'] = False
target['author_reconstruction']['final_validation_status'] = evidence_seal['status']
target['author_reconstruction']['evidence_manifest'] = bind(EVIDENCE / 'EVIDENCE_MANIFEST.json')
target['author_reconstruction']['unique_fresh_modules'] = 607
target['author_reconstruction']['resumed_fresh_modules'] = 186
target['author_reconstruction']['verified_first_segment_reuse'] = 421
b = target['required_final_bindings']
b['manuscript_manifest'] = bind(MAN / 'MANUSCRIPT_MANIFEST.json')
b['manuscript_freeze_record'] = bind(MAN / 'MANUSCRIPT_FREEZE.json')
b['manuscript_archive'] = bind(archive)
b['six_manuscript_files'] = [bind(MAN / f'PAPER_IV_preprint_v1.2_{lang}.{ext}') for lang in ('en','es') for ext in ('md','tex','pdf')]
b['author_full_build_evidence'] = [bind(EVIDENCE / n) for n in ('EVIDENCE_SEAL.json','EVIDENCE_MANIFEST.json','FULL_REBUILD_EVIDENCE_v1.2.zip')]
base = PAPER / '05_formalization/LEAN_SOURCE_SNAPSHOT_v1.0.zip'
assert sha(base) == '0a13c01cc4cf0198d5d138082d45b25df4c5ac0684c0ed85e7cc758575f8a7dd'
annex_root = PAPER / '05_formalization/lean_v1.0_gap_annex'
base_root = PAPER / '05_formalization/lean_v1.0_freeze'
annex_inputs = [base, PAPER / '05_formalization/LEAN_BOUNDED_GAP_ANNEX_v1.0.zip', annex_root / 'README.md', annex_root / 'SOURCE_MANIFEST.sha256']
annex_inputs += [base_root / n for n in ('lakefile.toml','lake-manifest.json','lean-toolchain')]
with zipfile.ZipFile(base) as z:
    assert z.testzip() is None
    for p in annex_inputs[-3:]:
        assert z.read('lean_v1.0_freeze/' + p.name) == p.read_bytes()
with zipfile.ZipFile(annex_inputs[1]) as z:
    assert z.testzip() is None
    for p in annex_inputs[2:4]:
        assert z.read(p.name) == p.read_bytes()
b['supplementary_annex_reproduction_inputs'] = {
    'files': [bind(p) for p in annex_inputs],
    'method': 'Overlay annex BoundedCliqueGap/ on a fresh extraction of the historical base; separate auditor project, serial after main build.',
    'target': 'BoundedCliqueGap.AxiomCheck',
    'author_project_objects_permitted': False,
    'dependencies': 'Reuse pinned installed Mathlib/packages; verify both manifests; no installation.'
}
b['mandate_and_scope_hashes'] = [bind(HERE / n) for n in ('EXTERNAL_ADVERSARIAL_AUDIT_REQUEST_v1.2.md','LOCAL_INPUT_SCOPE_v1.2.json','README.md','bind_v12_sealed_inputs.py')]
target['remaining_readiness_gates'] = [
    'Complete the renewed v1.2 internal audit on these exact inputs and resolve blockers.',
    'Bind the new internal-audit package/report and verify all final bindings.',
    'Owner requests external execution; intake independently verifies the bound identity.'
]
write(target_path, target)
prep_path = HERE / 'run_v1.2_r1/00_CONTROL/PREPARATION.json'
prep = read(prep_path)
assert prep['started_at'] is None
prep.update({'readiness': target['status'], 'manuscript_freeze': freeze['freeze_id'],
             'source_cut': target['source_cut'], 'target_sha256': sha(target_path),
             'author_reconstruction': 'COMPLETE_VALIDATED', 'internal_audit': 'NOT_STARTED'})
write(prep_path, prep)
print(json.dumps({'binding_status': target['status'], 'source_cut': target['source_cut'],
                  'manuscript_freeze': freeze['freeze_id'], 'manuscript_files_verified': len(rows),
                  'external_audit': 'NOT_STARTED', 'internal_audit': 'NOT_STARTED',
                  'target_sha256': sha(target_path)}, indent=2))
