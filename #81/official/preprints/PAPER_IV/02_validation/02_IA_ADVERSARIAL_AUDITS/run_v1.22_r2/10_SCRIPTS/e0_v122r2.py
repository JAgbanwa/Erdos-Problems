"""E0 (auditor-written) for run_v1.22_r2. Read-only. usage: python e0_v122r2.py OUT.json"""
import hashlib, json, pathlib, sys, zipfile, datetime, re
B = pathlib.Path('C:/Users/jtraverso/e81p4-publish/preprints/PAPER_IV')
A = B / '02_validation/02_IA_ADVERSARIAL_AUDITS'
sha = lambda p: hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
ck = {}
T = json.loads((A / 'AUDIT_TARGET_v1.22_r2.json').read_text(encoding='utf-8'))
ck['target_sha256'] = sha(A / 'AUDIT_TARGET_v1.22_r2.json')
ck['target_sidecar_match'] = (A / 'AUDIT_TARGET_v1.22_r2.json.sha256').read_text().split()[0] == ck['target_sha256']
def chk(e):
    p = B / e['path']; return {'sha_match': p.exists() and sha(p) == e['sha256'], 'bytes_match': p.exists() and p.stat().st_size == e['bytes']}
for k in ['candidate_manifest', 'candidate_package', 'mandate', 'frozen_source_manifest', 'baseline_target']: ck[k] = chk(T[k])
ck['earlier_evidence'] = {e['path']: chk(e) for e in T['earlier_evidence']}
R2 = B / '01_manuscript/v1.22_editorial_candidate_r2'; R1 = B / '01_manuscript/v1.22_editorial_candidate'
mm = json.loads((R2 / 'MANUSCRIPT_REVIEW_MANIFEST.json').read_text(encoding='utf-8'))
files = {e['path']: e for e in mm['files']}
ck['r2_manifest_meta'] = {k: mm[k] for k in mm if k != 'files'}
ck['r2_manifest_files'] = len(files)
ck['r2_manifest_vs_dir_bad'] = [p for p, e in files.items() if not (R2 / p).exists() or sha(R2 / p) != e['sha256'] or (R2 / p).stat().st_size != e['bytes']]
ondisk = {p.relative_to(R2).as_posix() for p in R2.rglob('*') if p.is_file()}
ck['r2_dir_files_not_in_manifest'] = sorted(ondisk - set(files))
ck['r2_manifest_sidecar'] = (R2 / 'MANUSCRIPT_REVIEW_MANIFEST.json.sha256').read_text().split()[0] == sha(R2 / 'MANUSCRIPT_REVIEW_MANIFEST.json')
ck['r2_pkg_sidecar'] = (R2 / 'PAPER_IV_v1.22_REVIEW_PACKAGE_r2.zip.sha256').read_text().split()[0] == sha(R2 / 'PAPER_IV_v1.22_REVIEW_PACKAGE_r2.zip')
z = zipfile.ZipFile(R2 / 'PAPER_IV_v1.22_REVIEW_PACKAGE_r2.zip')
ck['zip_testzip_crc'] = z.testzip()
names = [n for n in z.namelist() if not n.endswith('/')]
ck['zip_members'] = len(names)
ck['zip_unsafe'] = [n for n in names if n.startswith('/') or '..' in n.split('/') or re.match(r'^[A-Za-z]:', n)]
zh = {n: hashlib.sha256(z.read(n)).hexdigest() for n in names}
ck['zip_only'] = sorted(set(zh) - set(files)); ck['manifest_only_not_in_zip'] = sorted(set(files) - set(zh))
ck['zip_hash_mismatch'] = sorted(p for p in files if p in zh and zh[p] != files[p]['sha256'])
ck['zip_extra_members_hash_vs_disk'] = {n: (R2 / n).exists() and sha(R2 / n) == h for n, h in zh.items() if n not in files}
ck['other_zips_in_r2_dir'] = sorted(p.name for p in R2.glob('*.zip') if p.name != 'PAPER_IV_v1.22_REVIEW_PACKAGE_r2.zip')
ck['english_byte_identical_to_r1'] = {f: (R2 / f).read_bytes() == (R1 / f).read_bytes() for f in [f'PAPER_IV_preprint_v1.22_en.{x}' for x in ('md', 'tex', 'pdf')]}
ck['six_sha256_r2'] = {f: sha(R2 / f) for f in [f'PAPER_IV_preprint_v1.22_{l}.{x}' for l in ('en', 'es') for x in ('md', 'tex', 'pdf')]}
ck['six_sha256_r1'] = {f: sha(R1 / f) for f in ck['six_sha256_r2']}
ck['six_in_r2_manifest'] = all(f in files for f in ck['six_sha256_r2'])
# r1 comparison cut unmodified
m1 = json.loads((R1 / 'MANUSCRIPT_REVIEW_MANIFEST.json').read_text(encoding='utf-8'))
ck['r1_manifest_sha256'] = sha(R1 / 'MANUSCRIPT_REVIEW_MANIFEST.json')
ck['r1_dir_vs_manifest_bad'] = [e['path'] for e in m1['files'] if not (R1 / e['path']).exists() or sha(R1 / e['path']) != e['sha256']]
ck['r1_package_sha256'] = sha(R1 / 'PAPER_IV_v1.22_REVIEW_PACKAGE_r1.zip')
# Lean cut
SRC = B / '05_formalization/lean_piv-v12-fb459343d234'
sm = json.loads((B / '03_reproducibility/build_piv-v12-fb459343d234/SOURCE_MANIFEST.json').read_text())
ck['source_entries'] = len(sm)
ck['source_mismatch'] = [e['path'] for e in sm if not (SRC / e['path']).exists() or sha(SRC / e['path']) != e['sha256']]
ck['source_dir_extra_files'] = sorted({p.relative_to(SRC).as_posix() for p in SRC.rglob('*') if p.is_file()} - {e['path'] for e in sm})
for zn in ['LEAN_SOURCE_piv-v12-fb459343d234.zip', 'LEAN_BOUNDED_GAP_ANNEX_v1.0.zip']:
    zz = zipfile.ZipFile(B / '05_formalization' / zn); ck[zn] = {'sha256': sha(B / '05_formalization' / zn), 'testzip': zz.testzip(), 'members': len(zz.namelist())}
# source ZIP content vs manifest
zs = zipfile.ZipFile(B / '05_formalization/LEAN_SOURCE_piv-v12-fb459343d234.zip')
zsh = {}
for n in zs.namelist():
    if not n.endswith('/'): zsh[n.split('/', 1)[1] if '/' in n and len({x.split('/')[0] for x in zs.namelist()}) == 1 else n] = hashlib.sha256(zs.read(n)).hexdigest()
ck['source_zip_vs_manifest_mismatch'] = [e['path'] for e in sm if zsh.get(e['path']) != e['sha256']]
# historical runs
for run, zipname in [('run_v1.2_r1', 'EXTERNAL_AUDIT_run_v1.2_r1.zip'), ('run_v1.21_r1', 'EXTERNAL_REVALIDATION_run_v1.21_r1.zip'), ('run_v1.22_r1', 'EXTERNAL_REVALIDATION_run_v1.22_r1.zip')]:
    P = A / run
    man = json.loads((P / '40_PACKAGE/RUN_MANIFEST.json').read_text(encoding='utf-8'))
    pz = zipfile.ZipFile(P / '40_PACKAGE' / zipname)
    ck[run] = {'manifest_files': len(man), 'changed_on_disk': [e['path'] for e in man if not (P / e['path']).exists() or sha(P / e['path']) != e['sha256']],
               'zip_sidecar': (P / '40_PACKAGE' / (zipname + '.sha256')).read_text().split()[0] == sha(P / '40_PACKAGE' / zipname),
               'zip_testzip_crc': pz.testzip(), 'zip_members': len(pz.namelist()), 'run_manifest_sha256': sha(P / '40_PACKAGE/RUN_MANIFEST.json')}
json.dump({'run_at_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(), 'checks': ck}, open(sys.argv[1], 'w', encoding='utf-8'), indent=1, ensure_ascii=False)
print(json.dumps({k: v for k, v in ck.items() if k not in ('six_sha256_r1', 'r2_manifest_meta')}, indent=1, ensure_ascii=False))
