"""Seal r4, verifying r3 and the unchanged formal cut before packaging."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib,json,zipfile
ROOT=Path(__file__).resolve().parent
BASE=ROOT.parent/'v1.22_editorial_candidate_r3'
PAPER=ROOT.parents[1]
AUDITS=PAPER/'02_validation/02_IA_ADVERSARIAL_AUDITS'
MANIFEST=ROOT/'MANUSCRIPT_REVIEW_MANIFEST.json'
PACKAGE=ROOT/'PAPER_IV_v1.22_REVIEW_PACKAGE_r4.zip'
TARGET=AUDITS/'AUDIT_TARGET_v1.22_r4.json'
def sha(p):
    h=hashlib.sha256()
    with p.open('rb') as f:
        for b in iter(lambda:f.read(1048576),b''): h.update(b)
    return h.hexdigest()
def read(p): return json.loads(p.read_text(encoding='utf-8-sig'))
def record(p): return {'path':p.relative_to(PAPER).as_posix(),'bytes':p.stat().st_size,'sha256':sha(p)}
def write(p,obj):
    with p.open('x',encoding='utf-8') as f: json.dump(obj,f,ensure_ascii=False,indent=2); f.write('\n')
def sidecar(p):
    with p.with_name(p.name+'.sha256').open('x',encoding='ascii') as f: f.write(sha(p)+'  '+p.name+'\n')
for p in (MANIFEST,PACKAGE,TARGET): assert not p.exists(),f'Existing seal: {p}'
old_target=AUDITS/'AUDIT_TARGET_v1.22_r3.json'
assert sha(old_target)=='df89c3dd33df19be5ddc4a42afaf5dd9053977623c7bc2a30fd12143b1044970'
old=read(old_target)
for key in ('candidate_manifest','candidate_package','mandate','frozen_source_manifest','source_zip','annex_zip'):
    e=old[key]; assert sha(PAPER/e['path'])==e['sha256']
old_manifest=read(PAPER/old['candidate_manifest']['path'])
assert len(old_manifest['files'])==226
assert all(sha(BASE/e['path'])==e['sha256'] for e in old_manifest['files'])
frozen=PAPER/old['frozen_source_manifest']['path']
cut=PAPER/'05_formalization/lean_piv-v12-fb459343d234'
entries=read(frozen)
assert len(entries)==615 and all(sha(cut/e['path'])==e['sha256'] for e in entries)
recent=AUDITS/'run_v1.22_r3/40_PACKAGE/EXTERNAL_REVALIDATION_run_v1.22_r3.zip'
assert sha(recent)=='8ca5a69a1fdbb96823bf415de8de89265d14a8d2897acfed01a86c2a70fd3ddd'
prior=[record(recent)]+old['earlier_evidence']
for e in prior+[old['candidate_package'],old['source_zip'],old['annex_zip']]:
    p=PAPER/e['path']; assert sha(p)==e['sha256']
    with zipfile.ZipFile(p) as z: assert z.testzip() is None
checks=read(ROOT/'ARTIFACT_CHECKS.json')
assert checks['exact_two_phrase_delta_md_tex_pdf'] and checks['protected_mathematics_identical']
assert checks['english_byte_identical'] and checks['frozen_entries_unchanged']==615
assert checks['changed_spanish_pages']==[40,66] and not checks['lean_executed']
for name,digest in checks['files'].items(): assert sha(ROOT/name)==digest
for name in ('verify_frozen_logs.py','LOG_INVENTORY.json'):
    assert sha(ROOT/name)==sha(BASE/name)
for ext in ('md','tex','pdf','log'):
    name='PAPER_IV_preprint_v1.22_en.'+ext
    assert sha(ROOT/name)==sha(BASE/name)
files=sorted(p for p in ROOT.rglob('*') if p.is_file() and '__pycache__' not in p.parts and p.suffix not in {'.aux','.pyc'})
assert not any(p.suffix=='.zip' or p.name.startswith('.env') for p in files)
items=[{'path':p.relative_to(ROOT).as_posix(),'bytes':p.stat().st_size,'sha256':sha(p)} for p in files]
write(MANIFEST,{'revision':'v1.22-r4','manuscript_version':'v1.22','created_utc':datetime.now(timezone.utc).isoformat(),
 'status':'READY_FOR_REVALIDATION_NOT_EXTERNALLY_PASSED','files':items,
 'baseline_manifest':old['candidate_manifest'],'lean_source_manifest':record(frozen),
 'historical_packages_verified_hash_and_crc':prior,'lean_executed':False,
 'exclusions':['__pycache__','*.pyc','*.aux','manifest and sidecar included separately','ZIP and its sidecar']})
sidecar(MANIFEST)
payload=files+[MANIFEST,MANIFEST.with_name(MANIFEST.name+'.sha256')]
with zipfile.ZipFile(PACKAGE,'x',compression=zipfile.ZIP_DEFLATED,compresslevel=6) as z:
    for p in payload: z.write(p,p.relative_to(ROOT).as_posix())
with zipfile.ZipFile(PACKAGE) as z:
    assert z.testzip() is None and set(z.namelist())=={p.relative_to(ROOT).as_posix() for p in payload}
    for e in items: assert hashlib.sha256(z.read(e['path'])).hexdigest()==e['sha256']
sidecar(PACKAGE)
write(TARGET,{'revision':'v1.22-r4','status':'PREPARED_NOT_STARTED','candidate_manifest':record(MANIFEST),
 'candidate_package':record(PACKAGE),'mandate':record(AUDITS/'EXTERNAL_ADVERSARIAL_REVALIDATION_v1.22_r4.md'),
 'frozen_source_manifest':record(frozen),'source_zip':old['source_zip'],'annex_zip':old['annex_zip'],
 'earlier_evidence':prior,'baseline_target':record(old_target),
 'output_directory':str(AUDITS/'run_v1.22_r4'),'no_lean_build_authorized':True,'no_publication_authorized':True,
 'human_peer_review':'separate future milestone, not an E0-E8 PASS prerequisite',
 'required_report':'FINAL_CONSOLIDATED_AUDIT_REPORT.md and .pdf; all E0-E8 with historical evidence and actual current verdict'})
sidecar(TARGET)
assert all(sha(ROOT/e['path'])==e['sha256'] for e in items)
print(json.dumps({'sealed_files':len(items),'package':record(PACKAGE),'target':record(TARGET),'historical_crc':'PASS','lean_executed':False},indent=2))
