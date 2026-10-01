"""Validate and seal the v1.23 editorial package. No build, download or Git write."""
from pathlib import Path
from datetime import datetime, timezone
from urllib.parse import unquote
import argparse, hashlib, json, os, re, subprocess, sys, zipfile

P=Path(__file__).resolve().parents[2]
ROOT=P.parent.parent
I=P/'04_integrity'
E=P/'02_validation/03_EDITORIAL_CHECKS/v1.23'
A=P/'02_validation/02_IA_ADVERSARIAL_AUDITS'
B=A/'audit_inputs/published_v1.22'
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--publication-authorized',action='store_true',help='Record explicit owner authorization for GitHub publication only')
authorized=parser.parse_args().publication_authorized
def sha(p):
    h=hashlib.sha256()
    resolved=Path(chr(92)*2+'?'+chr(92)+str(p.resolve())) if os.name=='nt' else p
    with resolved.open('rb') as f:
        for chunk in iter(lambda:f.read(1048576),b''): h.update(chunk)
    return h.hexdigest()
def read(p): return json.loads(p.read_text(encoding='utf-8-sig'))
def save(p,v): p.write_text(json.dumps(v,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')

subprocess.run([sys.executable,str(Path(__file__).with_name('check_editorial.py'))],check=True)
assert read(E/'WEB_CHECKS.json')['status']=='PASS'
assert read(E/'WEB_CHECKS.json')['cases']==20
baseline=read(B/'RELEASE_METADATA.json')
baseline.pop('push_or_deposit_authorized',None)
baseline.update(manuscript_version='1.23',status='AUTHORIZED_FOR_GITHUB_PUBLICATION' if authorized else 'PREPARED_FOR_AUTHOR_REVIEW_NOT_PUBLISHED',
    manuscript_bytes_changed_in_packaging=True,editorial_verdict='EDITORIALLY_READY',
    external_audit='PASS_FOR_V1.22_R4_ONLY',external_audit_of_v123=False,
    published_predecessor='1.22',published_predecessor_tag='paper-IV-v1.22',
    published_predecessor_commit='cfcd5cf57cadc8583a218caaa1476911efe6158a',
    editorial_report='02_validation/03_EDITORIAL_CHECKS/v1.23/EDITORIAL_REPORT.md',
    mathematical_content_changed=False,github_publication_authorized=authorized,
    zenodo_deposit_authorized=False,new_version_doi='10.5281/zenodo.23089131',
    new_version_doi_provenance='Supplied by the author on 2026-10-01',
    new_version_public_record_check='HTTP 404 at the 2026-10-01 prepublication check')
save(P/'RELEASE_METADATA.json',baseline)
summary=read(A/'run_v1.22_r4/30_REPORT/SUMMARY.json')
assert summary['overall_verdict']=='PASS' and not summary['open_actions']
relocations={}
for name,digest in summary['target']['six_sha256'].items():
    target=B/'01_manuscript'/name
    assert sha(target)==digest
    relocations['01_manuscript/'+name]=target.relative_to(P).as_posix()
save(I/'RELOCATION_DELTA_v1.23.json',{'purpose':'Resolve v1.22 paths moved into the audit baseline; original relocation map is unchanged','paths':relocations})
mapping=read(I/'RELOCATION_MAP_v1.22.json')['files']
for x in mapping: assert sha(P/relocations.get(x['published'],x['published']))==x['sha256']
counts={}
for run in ('run_v1.2_r1','run_v1.21_r1','run_v1.22_r1','run_v1.22_r2','run_v1.22_r3','run_v1.22_r4'):
    entries=read(A/run/'40_PACKAGE/RUN_MANIFEST.json')
    for x in entries: assert sha(A/run/x['path'])==x['sha256']
    counts[run]=len(entries)
zips=0
for sidecar in P.rglob('*.zip.sha256'):
    z=sidecar.with_suffix('')
    assert sha(z)==sidecar.read_text().split()[0]
    with zipfile.ZipFile(z) as archive: assert archive.testzip() is None
    zips+=1
logs=subprocess.run([sys.executable,str(P/'03_reproducibility/verify_logs.py')],check=True,capture_output=True,text=True)
log_result=json.loads(logs.stdout)
assert log_result['status']=='PASS' and log_result['logs_checked']==1266
assert not subprocess.check_output(['git','diff','--name-only','--','preprints/PAPER_I','preprints/PAPER_II','preprints/PAPER_III','preprints/PAPER_IV/05_formalization','preprints/PAPER_IV/superseded'],cwd=ROOT).strip()
assert sorted(x.name for x in (P/'01_manuscript').glob('*.md'))==['PAPER_IV_preprint_v1.23_en.md','PAPER_IV_preprint_v1.23_es.md','README.md']
files=sorted((P/'01_manuscript').glob('PAPER_IV_preprint_v1.23_*.*'))
assert len(files)==6
(P/'01_manuscript/SHA256SUMS.txt').write_text(''.join(sha(x)+'  '+x.name+'\n' for x in files),encoding='ascii')

docs=[ROOT/x for x in ('README.md','CITATION.md','WEB_PUBLICATION.md','preprints/README.md')]
docs += [P/x for x in ('README.md','CHANGELOG_v1.23.md','RELEASE_CHECKLIST_v1.23.md','01_manuscript/README.md','02_validation/README.md','03_reproducibility/README.md','04_integrity/README.md','05_formalization/README.md','superseded/README.md','02_validation/02_IA_ADVERSARIAL_AUDITS/audit_inputs/README.md')]
links=0
for doc in docs:
    for url in re.findall(r'\]\(([^)]+)\)',doc.read_text(encoding='utf-8')):
        url=url.strip('<>')
        if re.match(r'^[a-z]+:',url) or url.startswith('#'): continue
        assert (doc.parent/unquote(url.split('#')[0])).resolve().exists(),(doc,url)
        links+=1
for root,dirs,names in os.walk(P):
    assert not set(dirs)&{'.lake','.git','__pycache__','05_BUILD'}
    for name in names:
        path=Path(root,name)
        assert not name.startswith('.env') and path.suffix not in ('.olean','.ilean','.pyc')
        assert path.stat().st_size<100*1024**2
        if path.suffix in ('.md','.py','.json','.txt','.log','.toml','.csv','.tex') and path.stat().st_size<20*1024**2:
            text=path.read_text(encoding='utf-8',errors='replace')
            assert not re.search(r'arstl_[A-Za-z0-9_-]{25,}|gh[pousr]_[A-Za-z0-9]{30,}|-----BEGIN (?:RSA |OPENSSH )?PRIVATE KEY-----',text),path
result={'status':'PASS','prepared_utc':datetime.now(timezone.utc).isoformat(),
    'purpose':'Local editorial/package verification, not a new external audit',
    'current_version':'1.23','external_audited_revision':'v1.22-r4','external_audit_of_v123':False,
    'editorial_changes':12,'formal_entries_unchanged':615,'historical_audit_manifest_counts':counts,
    'mapped_artifacts':len(mapping),'relocated_active_manuscripts':6,'zip_sidecars_and_crc':zips,
    'navigation_links_checked':links,'required_log_verifier':log_result,
    'papers_I_II_III_and_v08_unchanged':True,'credentials_or_compiled_caches_detected':False,
    'lean_executed':False,'pdf_rebuilt':True,'git_commit_push_tag_or_deposit_performed':False,
    'github_publication_authorized':authorized,
    'pending':(['Apply new homepage only after publishing index.html'] if authorized else ['Author review and publication authorization','Apply new homepage only after publishing index.html'])}
save(I/'PUBLICATION_CHECKS.json',result)
excluded={'04_integrity/RELEASE_MANIFEST.json','04_integrity/RELEASE_MANIFEST.json.sha256'}
entries=[{'path':f.relative_to(P).as_posix(),'bytes':f.stat().st_size,'sha256':sha(f)} for f in sorted(P.rglob('*')) if f.is_file() and f.relative_to(P).as_posix() not in excluded]
manifest=I/'RELEASE_MANIFEST.json'
save(manifest,{'version':'1.23','external_audited_predecessor':'v1.22-r4','files':entries,'exclusions':sorted(excluded),'github_publication_authorized':authorized,'zenodo_deposit_authorized':False})
manifest.with_name(manifest.name+'.sha256').write_text(sha(manifest)+'  '+manifest.name+'\n',encoding='ascii')
repo=[]
for root,dirs,names in os.walk(ROOT):
    dirs[:]=[d for d in dirs if d not in ('.git','.lake','__pycache__')]
    for name in names:
        path=Path(root,name)
        if path not in (ROOT/'manifest_sha256.txt',ROOT/'manifest_sha256.txt.tmp',ROOT/'.git'): repo.append(path)
with (ROOT/'manifest_sha256.txt.tmp').open('w',encoding='utf-8',newline='\n') as out:
    for path in sorted(repo): out.write(sha(path)+'  '+path.relative_to(ROOT).as_posix()+'\n')
os.replace(ROOT/'manifest_sha256.txt.tmp',ROOT/'manifest_sha256.txt')
print(json.dumps({'status':'PASS','release_files':len(entries),'repository_files':len(repo),'release_manifest_sha256':sha(manifest),'checks':result},indent=2))
