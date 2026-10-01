"""E0 (auditor-written) for run_v1.21_r1. Read-only. usage: python e0_v121.py OUT.json"""
import hashlib, json, pathlib, sys, zipfile, datetime, re
B = pathlib.Path('C:/Users/jtraverso/e81p4-publish/preprints/PAPER_IV')
A = B / '02_validation/02_IA_ADVERSARIAL_AUDITS'
sha = lambda p: hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
out = {'run_at_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(), 'checks': {}}
ck = out['checks']
T = json.loads((A / 'AUDIT_TARGET_v1.21.json').read_text(encoding='utf-8'))
ck['target_sha256'] = sha(A / 'AUDIT_TARGET_v1.21.json')
ck['target_sidecar_match'] = (A / 'AUDIT_TARGET_v1.21.json.sha256').read_text().split()[0] == ck['target_sha256']
for k in ['request', 'manuscript_manifest', 'manuscript_zip', 'source_manifest', 'prior_evidence_binding']:
    e = T[k]; p = pathlib.Path(e['path'])
    ck[k] = {'sha_match': sha(p) == e['sha256'], 'bytes_match': p.stat().st_size == e['bytes']}
# manuscript manifest vs directory and zip
MD = B / '01_manuscript/v1.21_editorial_candidate'
mm = json.loads((MD / 'MANUSCRIPT_REVIEW_MANIFEST.json').read_text(encoding='utf-8'))
files = {e['path']: e for e in mm['files']}
bad = [p for p, e in files.items() if not (MD / p).exists() or sha(MD / p) != e['sha256'] or (MD / p).stat().st_size != e['bytes']]
ck['ms_manifest_files'] = len(files); ck['ms_manifest_vs_dir_bad'] = bad
ck['ms_manifest_meta'] = {k: mm[k] for k in mm if k != 'files'}
ck['ms_sidecar'] = (MD / 'MANUSCRIPT_REVIEW_MANIFEST.sha256').read_text().split()[0] == sha(MD / 'MANUSCRIPT_REVIEW_MANIFEST.json')
z = zipfile.ZipFile(MD / 'PAPER_IV_v1.21_REVIEW_PACKAGE_r1.zip')
ck['zip_testzip'] = z.testzip(); names = z.namelist()
ck['zip_members'] = len(names)
ck['zip_unsafe'] = [n for n in names if n.startswith('/') or '..' in n.split('/') or re.match(r'^[A-Za-z]:', n)]
zh = {n: hashlib.sha256(z.read(n)).hexdigest() for n in names if not n.endswith('/')}
pref = {n.split('/')[0] for n in zh}
strip = (lambda n: n.split('/', 1)[1]) if len(pref) == 1 and all('/' in n for n in zh) else (lambda n: n)
zs = {strip(n): h for n, h in zh.items()}
ck['zip_only'] = sorted(set(zs) - set(files)); ck['manifest_only_not_in_zip'] = sorted(set(files) - set(zs))
ck['zip_hash_mismatch'] = sorted(p for p in files if p in zs and zs[p] != files[p]['sha256'])
ck['r1_zip_sidecar'] = (MD / 'PAPER_IV_v1.21_REVIEW_PACKAGE_r1.sha256').read_text().split()[0] == sha(MD / 'PAPER_IV_v1.21_REVIEW_PACKAGE_r1.zip')
# six manuscripts
six = ['PAPER_IV_preprint_v1.21_en.md', 'PAPER_IV_preprint_v1.21_en.tex', 'PAPER_IV_preprint_v1.21_en.pdf', 'PAPER_IV_preprint_v1.21_es.md', 'PAPER_IV_preprint_v1.21_es.tex', 'PAPER_IV_preprint_v1.21_es.pdf']
ck['six'] = {f: sha(MD / f) for f in six}; ck['six_in_manifest'] = all(f in files for f in six)
# Lean sources
SRC = B / '05_formalization/lean_piv-v12-fb459343d234'
sm = json.loads((B / '03_reproducibility/build_piv-v12-fb459343d234/SOURCE_MANIFEST.json').read_text())
ck['source_manifest_sha'] = sha(B / '03_reproducibility/build_piv-v12-fb459343d234/SOURCE_MANIFEST.json')
ck['source_entries'] = len(sm)
ck['source_mismatch'] = [e['path'] for e in sm if not (SRC / e['path']).exists() or sha(SRC / e['path']) != e['sha256']]
extra = [p.relative_to(SRC).as_posix() for p in SRC.rglob('*') if p.is_file()]
ck['source_dir_extra_files'] = sorted(set(extra) - {e['path'] for e in sm})
ck['source_zip_sha'] = sha(B / '05_formalization/LEAN_SOURCE_piv-v12-fb459343d234.zip')
# prior evidence binding
EB = json.loads((MD / 'EXTERNAL_EVIDENCE_BINDING.json').read_text(encoding='utf-8'))
ck['binding_archive_match'] = sha(EB['archive']['path']) == EB['archive']['sha256']
ck['binding_evidence_mismatch'] = [e['path'] for e in EB['evidence'] if sha(e['path']) != e['sha256']]
# prior run manifest vs disk
P = A / 'run_v1.2_r1'
man = json.loads((P / '40_PACKAGE/RUN_MANIFEST.json').read_text(encoding='utf-8'))
ck['prior_manifest_files'] = len(man)
ck['prior_manifest_changed_on_disk'] = [e['path'] for e in man if not (P / e['path']).exists() or sha(P / e['path']) != e['sha256']]
ck['prior_zip_sidecar'] = (P / '40_PACKAGE/EXTERNAL_AUDIT_run_v1.2_r1.zip.sha256').read_text().split()[0] == sha(P / '40_PACKAGE/EXTERNAL_AUDIT_run_v1.2_r1.zip')
pz = zipfile.ZipFile(P / '40_PACKAGE/EXTERNAL_AUDIT_run_v1.2_r1.zip'); ck['prior_zip_testzip'] = pz.testzip(); ck['prior_zip_members'] = len(pz.namelist())
json.dump(out, open(sys.argv[1], 'w', encoding='utf-8'), indent=1, ensure_ascii=False)
print(json.dumps({k: v for k, v in ck.items() if k not in ('six', 'ms_manifest_meta')}, indent=1, ensure_ascii=False)[:5000])
print(json.dumps(ck['ms_manifest_meta'], indent=1, ensure_ascii=False)[:2500])
