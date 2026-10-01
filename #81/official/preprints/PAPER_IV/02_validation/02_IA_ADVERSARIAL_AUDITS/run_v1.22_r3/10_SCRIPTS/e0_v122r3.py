"""E0 (auditor-written) for run_v1.22_r3. Read-only. usage: python e0_v122r3.py OUT.json
EN and ES changed in r3 by declaration: byte identity with r2 is RECORDED, not required. Required: target,
manifest, ZIP, Lean cut 615, source ZIP, annex, figures identical to r2, comparators and four prior runs unchanged."""
import hashlib, json, pathlib, sys, zipfile, datetime, re
B = pathlib.Path('C:/Users/jtraverso/e81p4-publish/preprints/PAPER_IV')
A = B / '02_validation/02_IA_ADVERSARIAL_AUDITS'
sha = lambda p: hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
ck = {}
T = json.loads((A / 'AUDIT_TARGET_v1.22_r3.json').read_text(encoding='utf-8'))
ck['target_sha256'] = sha(A / 'AUDIT_TARGET_v1.22_r3.json')
ck['target_sidecar_match'] = (A / 'AUDIT_TARGET_v1.22_r3.json.sha256').read_text().split()[0] == ck['target_sha256']
def chk(e):
    p = B / e['path']; return {'sha_match': p.exists() and sha(p) == e['sha256'], 'bytes_match': p.exists() and p.stat().st_size == e['bytes']}
for k in ['candidate_manifest', 'candidate_package', 'mandate', 'frozen_source_manifest', 'source_zip', 'annex_zip', 'baseline_target']:
    ck[k] = chk(T[k])
ck['earlier_evidence'] = {e['path']: chk(e) for e in T['earlier_evidence']}
R3 = B / '01_manuscript/v1.22_editorial_candidate_r3'
R2 = B / '01_manuscript/v1.22_editorial_candidate_r2'
R1 = B / '01_manuscript/v1.22_editorial_candidate'
mm = json.loads((R3 / 'MANUSCRIPT_REVIEW_MANIFEST.json').read_text(encoding='utf-8'))
files = {e['path']: e for e in mm['files']}
ck['r3_manifest_meta'] = {k: mm[k] for k in mm if k != 'files'}
ck['r3_manifest_files'] = len(files)
ck['r3_manifest_vs_dir_bad'] = [p for p, e in files.items() if not (R3 / p).exists() or sha(R3 / p) != e['sha256'] or (R3 / p).stat().st_size != e['bytes']]
ondisk = {p.relative_to(R3).as_posix() for p in R3.rglob('*') if p.is_file()}
ck['r3_dir_files_not_in_manifest'] = sorted(ondisk - set(files))
ck['r3_manifest_sidecar'] = (R3 / 'MANUSCRIPT_REVIEW_MANIFEST.json.sha256').read_text().split()[0] == sha(R3 / 'MANUSCRIPT_REVIEW_MANIFEST.json')
ck['r3_pkg_sidecar'] = (R3 / 'PAPER_IV_v1.22_REVIEW_PACKAGE_r3.zip.sha256').read_text().split()[0] == sha(R3 / 'PAPER_IV_v1.22_REVIEW_PACKAGE_r3.zip')
z = zipfile.ZipFile(R3 / 'PAPER_IV_v1.22_REVIEW_PACKAGE_r3.zip')
ck['zip_testzip_crc'] = z.testzip()
names = [n for n in z.namelist() if not n.endswith('/')]
ck['zip_members'] = len(names)
ck['zip_unsafe'] = [n for n in names if n.startswith('/') or '..' in n.split('/') or re.match(r'^[A-Za-z]:', n)]
zh = {n: hashlib.sha256(z.read(n)).hexdigest() for n in names}
ck['zip_only'] = sorted(set(zh) - set(files)); ck['manifest_only_not_in_zip'] = sorted(set(files) - set(zh))
ck['zip_hash_mismatch'] = sorted(p for p in files if p in zh and zh[p] != files[p]['sha256'])
ck['zip_extra_members_hash_vs_disk'] = {n: (R3 / n).exists() and sha(R3 / n) == h for n, h in zh.items() if n not in files}
ck['other_zips_in_r3_dir'] = sorted(p.name for p in R3.glob('*.zip') if p.name != 'PAPER_IV_v1.22_REVIEW_PACKAGE_r3.zip')
six = [f'PAPER_IV_preprint_v1.22_{l}.{x}' for l in ('en', 'es') for x in ('md', 'tex', 'pdf')]
ck['six_sha256_r3'] = {f: sha(R3 / f) for f in six}
ck['six_in_r3_manifest'] = all(f in files for f in six)
ck['six_byte_identical_to_r2_RECORDED_NOT_REQUIRED'] = {f: (R3 / f).read_bytes() == (R2 / f).read_bytes() for f in six}
# figures identical to r2
figs = {}
for d in ('figures', 'figures_en'):
    for p in sorted((R3 / d).glob('*')):
        q = R2 / d / p.name
        figs[f'{d}/{p.name}'] = q.exists() and q.read_bytes() == p.read_bytes()
    figs[f'{d}/__r2_only'] = sorted(p.name for p in (R2 / d).glob('*') if not (R3 / d / p.name).exists())
ck['figures_identical_to_r2'] = figs
# comparators unchanged
for nm, D, man in [('r2', R2, 'MANUSCRIPT_REVIEW_MANIFEST.json'), ('r1', R1, 'MANUSCRIPT_REVIEW_MANIFEST.json')]:
    m = json.loads((D / man).read_text(encoding='utf-8'))
    ck[f'{nm}_manifest_sha256'] = sha(D / man)
    ck[f'{nm}_dir_vs_manifest_bad'] = [e['path'] for e in m['files'] if not (D / e['path']).exists() or sha(D / e['path']) != e['sha256']]
# Lean
SRC = B / '05_formalization/lean_piv-v12-fb459343d234'
sm = json.loads((B / '03_reproducibility/build_piv-v12-fb459343d234/SOURCE_MANIFEST.json').read_text())
ck['source_entries'] = len(sm)
ck['source_mismatch'] = [e['path'] for e in sm if not (SRC / e['path']).exists() or sha(SRC / e['path']) != e['sha256']]
ck['source_dir_extra_files'] = sorted({p.relative_to(SRC).as_posix() for p in SRC.rglob('*') if p.is_file()} - {e['path'] for e in sm})
for zn in ['LEAN_SOURCE_piv-v12-fb459343d234.zip', 'LEAN_BOUNDED_GAP_ANNEX_v1.0.zip']:
    zz = zipfile.ZipFile(B / '05_formalization' / zn); ck[zn] = {'sha256': sha(B / '05_formalization' / zn), 'testzip': zz.testzip(), 'members': len(zz.namelist())}
zs = zipfile.ZipFile(B / '05_formalization/LEAN_SOURCE_piv-v12-fb459343d234.zip')
roots = {x.split('/')[0] for x in zs.namelist()}
zsh = {(n.split('/', 1)[1] if len(roots) == 1 and '/' in n else n): hashlib.sha256(zs.read(n)).hexdigest() for n in zs.namelist() if not n.endswith('/')}
ck['source_zip_vs_manifest_mismatch'] = [e['path'] for e in sm if zsh.get(e['path']) != e['sha256']]
for run, zipname in [('run_v1.2_r1', 'EXTERNAL_AUDIT_run_v1.2_r1.zip'), ('run_v1.21_r1', 'EXTERNAL_REVALIDATION_run_v1.21_r1.zip'),
                     ('run_v1.22_r1', 'EXTERNAL_REVALIDATION_run_v1.22_r1.zip'), ('run_v1.22_r2', 'EXTERNAL_REVALIDATION_run_v1.22_r2.zip')]:
    P = A / run
    man = json.loads((P / '40_PACKAGE/RUN_MANIFEST.json').read_text(encoding='utf-8'))
    pz = zipfile.ZipFile(P / '40_PACKAGE' / zipname)
    ck[run] = {'manifest_files': len(man), 'changed_on_disk': [e['path'] for e in man if not (P / e['path']).exists() or sha(P / e['path']) != e['sha256']],
               'zip_sidecar': (P / '40_PACKAGE' / (zipname + '.sha256')).read_text().split()[0] == sha(P / '40_PACKAGE' / zipname),
               'zip_testzip_crc': pz.testzip(), 'zip_members': len(pz.namelist()), 'run_manifest_sha256': sha(P / '40_PACKAGE/RUN_MANIFEST.json')}
json.dump({'run_at_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(), 'checks': ck}, open(sys.argv[1], 'w', encoding='utf-8'), indent=1, ensure_ascii=False)
print(json.dumps({k: v for k, v in ck.items() if k not in ('r3_manifest_meta', 'figures_identical_to_r2')}, indent=1, ensure_ascii=False))
print('figures all identical:', all(v for k, v in figs.items() if not k.endswith('__r2_only')), {k: v for k, v in figs.items() if k.endswith('__r2_only')})
