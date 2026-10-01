"""Seal r2 once; verify earlier evidence without rebuilding or changing it."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, zipfile

ROOT=Path(__file__).resolve().parent
BASE=ROOT.parent/'v1.22_editorial_candidate'
PAPER=ROOT.parents[1]
AUDITS=PAPER/'02_validation/02_IA_ADVERSARIAL_AUDITS'
MANIFEST=ROOT/'MANUSCRIPT_REVIEW_MANIFEST.json'
PACKAGE=ROOT/'PAPER_IV_v1.22_REVIEW_PACKAGE_r2.zip'
TARGET=AUDITS/'AUDIT_TARGET_v1.22_r2.json'
def sha(p):
    h=hashlib.sha256()
    with p.open('rb') as f:
        for b in iter(lambda:f.read(1048576),b''): h.update(b)
    return h.hexdigest()
def record(p):
    return {'path':p.relative_to(PAPER).as_posix(),'bytes':p.stat().st_size,'sha256':sha(p)}
def write(p,obj):
    with p.open('x',encoding='utf-8') as f: json.dump(obj,f,ensure_ascii=False,indent=2); f.write('\n')
def sidecar(p):
    with p.with_name(p.name+'.sha256').open('x',encoding='ascii') as f: f.write(sha(p)+'  '+p.name+'\n')
for p in (MANIFEST,PACKAGE,TARGET): assert not p.exists(),f'Existing seal: {p}'
old_target=AUDITS/'AUDIT_TARGET_v1.22.json'
assert sha(old_target)=='cbe0fd6e8e8c3f70faf91b02d1e0e8da08d201ed9d87f262a12de1e6115f8119'
old=json.loads(old_target.read_text(encoding='utf-8-sig'))
for key in ('candidate_manifest','candidate_package','mandate','frozen_source_manifest'):
    entry=old[key]; assert sha(PAPER/entry['path'])==entry['sha256']
old_manifest=json.loads((PAPER/old['candidate_manifest']['path']).read_text())
assert all(sha(BASE/e['path'])==e['sha256'] for e in old_manifest['files'])
frozen=PAPER/old['frozen_source_manifest']['path']
cut=PAPER/'05_formalization/lean_piv-v12-fb459343d234'
entries=json.loads(frozen.read_text(encoding='utf-8-sig'))
assert len(entries)==615 and all(sha(cut/e['path'])==e['sha256'] for e in entries)
prior=list(old['earlier_evidence'])
recent=AUDITS/'run_v1.22_r1/40_PACKAGE/EXTERNAL_REVALIDATION_run_v1.22_r1.zip'
assert sha(recent)=='9c74d673206ab17a5b4586209ececca30536f1768fcc91ffdd39db551193a1fa'
prior.insert(0,record(recent))
for e in prior+[old['candidate_package']]:
    p=PAPER/e['path']; assert sha(p)==e['sha256']
    with zipfile.ZipFile(p) as z: assert z.testzip() is None
checks=json.loads((ROOT/'ARTIFACT_CHECKS.json').read_text())
assert checks['pending']=='External r2 revalidation'
for e in checks['english_byte_identical']:
    assert sha(ROOT/e['file'])==sha(BASE/e['file'])==e['sha256']
for ext in ('pdf','tex'): assert sha(ROOT/f'PAPER_IV_preprint_v1.22_es.{ext}')==checks['spanish_'+ext+'_sha256']
assert sha(ROOT/'PAPER_IV_preprint_v1.22_es.md')==json.loads((ROOT/'SEMANTIC_CHECKS.json').read_text())['spanish_output_sha256']
files=sorted(p for p in ROOT.rglob('*') if p.is_file() and '__pycache__' not in p.parts and p.suffix not in {'.aux','.pyc'})
assert not any(p.suffix=='.zip' or p.name.startswith('.env') for p in files)
items=[{'path':p.relative_to(ROOT).as_posix(),'bytes':p.stat().st_size,'sha256':sha(p)} for p in files]
write(MANIFEST,{'revision':'v1.22-r2','manuscript_version':'v1.22','created_utc':datetime.now(timezone.utc).isoformat(),
    'status':'READY_FOR_REVALIDATION_NOT_EXTERNALLY_PASSED','files':items,
    'baseline_manifest':old['candidate_manifest'],'lean_source_manifest':record(frozen),
    'historical_packages_verified_hash_and_crc':prior,'lean_executed':False,
    'exclusions':['__pycache__','*.pyc','*.aux','manifest and sidecar included separately','ZIP and its sidecar']})
sidecar(MANIFEST)
payload=files+[MANIFEST,MANIFEST.with_name(MANIFEST.name+'.sha256')]
with zipfile.ZipFile(PACKAGE,'x',compression=zipfile.ZIP_DEFLATED,compresslevel=6) as z:
    for p in payload: z.write(p,p.relative_to(ROOT).as_posix())
with zipfile.ZipFile(PACKAGE) as z:
    assert z.testzip() is None
    assert set(z.namelist())=={p.relative_to(ROOT).as_posix() for p in payload}
    for e in items: assert hashlib.sha256(z.read(e['path'])).hexdigest()==e['sha256']
sidecar(PACKAGE)
write(TARGET,{'revision':'v1.22-r2','status':'PREPARED_NOT_STARTED','candidate_manifest':record(MANIFEST),
    'candidate_package':record(PACKAGE),'mandate':record(AUDITS/'EXTERNAL_ADVERSARIAL_REVALIDATION_v1.22_r2.md'),
    'frozen_source_manifest':record(frozen),'earlier_evidence':prior,'baseline_target':record(old_target),
    'output_directory':str(AUDITS/'run_v1.22_r2'),'no_lean_build_authorized':True,'no_publication_authorized':True,
    'required_report':'FINAL_CONSOLIDATED_AUDIT_REPORT.md and .pdf, covering E0-E8 with historical evidence'})
sidecar(TARGET)
assert all(sha(ROOT/e['path'])==e['sha256'] for e in items)
print(json.dumps({'sealed_files':len(items),'package':record(PACKAGE),'target':record(TARGET),'historical_crc':'PASS','lean_executed':False},indent=2))
