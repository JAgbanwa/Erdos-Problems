"""Seal this editorial candidate; read-only verification of Lean and earlier audits.

No build, network, deletion or credentials. Refuses to overwrite an existing seal.
"""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import zipfile

ROOT = Path(__file__).resolve().parent
PAPER = ROOT.parents[1]
AUDITS = PAPER / '02_validation/02_IA_ADVERSARIAL_AUDITS'
MANIFEST = ROOT / 'MANUSCRIPT_REVIEW_MANIFEST.json'
PACKAGE = ROOT / 'PAPER_IV_v1.22_REVIEW_PACKAGE_r1.zip'
TARGET = AUDITS / 'AUDIT_TARGET_v1.22.json'

def sha(path):
    h = hashlib.sha256()
    with path.open('rb') as f:
        for block in iter(lambda: f.read(1024 * 1024), b''):
            h.update(block)
    return h.hexdigest()

def write_json(path, value):
    with path.open('x', encoding='utf-8') as f:
        json.dump(value, f, ensure_ascii=False, indent=2)
        f.write('\n')

def record(path):
    return {'path': path.relative_to(PAPER).as_posix(),
            'bytes': path.stat().st_size, 'sha256': sha(path)}

def sidecar(path):
    with path.with_name(path.name + '.sha256').open('x', encoding='ascii') as f:
        f.write(sha(path) + '  ' + path.name + '\n')

for p in (MANIFEST, PACKAGE, TARGET):
    assert not p.exists(), f'Existing seal: {p}; verify it, do not overwrite.'

frozen_manifest = PAPER / '03_reproducibility/build_piv-v12-fb459343d234/SOURCE_MANIFEST.json'
assert sha(frozen_manifest) == 'fb459343d234f968d7d32eff1491ea8a09aa2e135b313a80623012e7449042f5'
entries = json.loads(frozen_manifest.read_text(encoding='utf-8-sig'))
cut = PAPER / '05_formalization/lean_piv-v12-fb459343d234'
assert len(entries) == 615
assert all(sha(cut / e['path']) == e['sha256'] for e in entries)

expected = {
 '02_validation/02_IA_ADVERSARIAL_AUDITS/run_v1.21_r1/40_PACKAGE/EXTERNAL_REVALIDATION_run_v1.21_r1.zip':
 '11659a97b0a4f2bffadb6968159cc5b66562b4470053939a45c1e8a42db7a638',
 '02_validation/02_IA_ADVERSARIAL_AUDITS/run_v1.2_r1/40_PACKAGE/EXTERNAL_AUDIT_run_v1.2_r1.zip':
 '886ed7f033bca42a530944d48f91ef45e79f6be4cb0d74080c5d8d6efc4f5e2b',
 '05_formalization/LEAN_SOURCE_piv-v12-fb459343d234.zip':
 'cb2741454380736ffe01b59933057b5079fa9f865d5bbdd3f67534bf808a62e6',
 '05_formalization/LEAN_BOUNDED_GAP_ANNEX_v1.0.zip':
 '2847a422865e06880d457ea806aae5b9f749d22359eff325349c09c01cb4837d',
}
prior = []
for relative, digest in expected.items():
    p = PAPER / relative
    assert sha(p) == digest, relative
    with zipfile.ZipFile(p) as z:
        assert z.testzip() is None, relative
    prior.append(record(p))

artifact_checks = json.loads((ROOT / 'ARTIFACT_CHECKS.json').read_text())
for lang in ('en', 'es'):
    for ext in ('pdf', 'tex'):
        assert sha(ROOT / f'PAPER_IV_preprint_v1.22_{lang}.{ext}') == artifact_checks[lang][ext + '_sha256']
    assert (ROOT / f'qa_{lang}/pdf_sha256.txt').read_text().strip().split()[0] == artifact_checks[lang]['pdf_sha256']

files = sorted(p for p in ROOT.rglob('*') if p.is_file()
               and '__pycache__' not in p.parts and p.suffix not in {'.aux', '.pyc'})
assert not any(p.suffix == '.zip' or p.name.startswith('.env') for p in files)
items = [{'path': p.relative_to(ROOT).as_posix(), 'bytes': p.stat().st_size,
          'sha256': sha(p)} for p in files]
write_json(MANIFEST, {
    'revision': 'v1.22-r1', 'created_utc': datetime.now(timezone.utc).isoformat(),
    'status': 'READY_FOR_REVALIDATION_NOT_EXTERNALLY_PASSED',
    'files': items, 'lean_source_manifest': record(frozen_manifest),
    'prior_packages_verified_hash_and_crc': prior,
    'exclusions': ['__pycache__', '*.pyc', '*.aux', 'seal manifest and sidecar (included in ZIP separately)', 'ZIP and its sidecar'],
    'lean_executed': False,
})
sidecar(MANIFEST)
payload = files + [MANIFEST, MANIFEST.with_name(MANIFEST.name + '.sha256')]
with zipfile.ZipFile(PACKAGE, 'x', compression=zipfile.ZIP_DEFLATED, compresslevel=6) as z:
    for p in payload:
        z.write(p, p.relative_to(ROOT).as_posix())
with zipfile.ZipFile(PACKAGE) as z:
    assert z.testzip() is None
    assert set(z.namelist()) == {p.relative_to(ROOT).as_posix() for p in payload}
    for item in items:
        assert hashlib.sha256(z.read(item['path'])).hexdigest() == item['sha256']
sidecar(PACKAGE)
mandate = AUDITS / 'EXTERNAL_ADVERSARIAL_REVALIDATION_v1.22_r1.md'
write_json(TARGET, {
    'revision': 'v1.22-r1', 'status': 'PREPARED_NOT_STARTED',
    'candidate_manifest': record(MANIFEST), 'candidate_package': record(PACKAGE),
    'mandate': record(mandate), 'frozen_source_manifest': record(frozen_manifest),
    'earlier_evidence': prior, 'output_directory': str(AUDITS / 'run_v1.22_r1'),
    'no_lean_build_authorized': True, 'no_publication_authorized': True,
})
sidecar(TARGET)
assert all(sha(ROOT / i['path']) == i['sha256'] for i in items)
print(json.dumps({'sealed_files': len(items), 'package': record(PACKAGE),
                  'target': record(TARGET), 'prior_zip_crcs': 'PASS',
                  'source_entries_unchanged': 615, 'lean_executed': False}, indent=2))
