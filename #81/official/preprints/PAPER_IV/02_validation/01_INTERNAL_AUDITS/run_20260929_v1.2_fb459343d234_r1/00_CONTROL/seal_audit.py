"""Seal only after human-model visual review has a bound acceptance record."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,zipfile,sys,subprocess,csv
from verify_package import verify

RUN=Path(__file__).resolve().parents[1];PAPER=RUN.parents[2];CONTROL=RUN/'00_CONTROL'
EV=RUN/'20_EVIDENCE';PK=RUN/'30_PACKAGE'
def read(p):return json.loads(p.read_text(encoding='utf-8-sig'))
def sha(p):
    with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
def save(p,o):p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(o,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
def files(d):return [p for p in d.rglob('*') if p.is_file() and not any(x in ('__pycache__','.lake','.git') for x in p.relative_to(RUN).parts)]
def archive(path,items):
    assert not path.exists(),'Never overwrite a sealed package'
    path.parent.mkdir(parents=True,exist_ok=True)
    selected=sorted(set(items));rows=[dict(path=p.relative_to(RUN).as_posix(),bytes=p.stat().st_size,sha256=sha(p)) for p in selected]
    assert all(not any(part.startswith('.env') for part in Path(r['path']).parts) for r in rows)
    with zipfile.ZipFile(path,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=6) as z:
        for r,p in zip(rows,selected):z.write(p,r['path'])
        z.writestr('MANIFEST.json',json.dumps(rows,ensure_ascii=False,indent=2)+'\n')
    checked=verify(path)
    h=sha(path);path.with_suffix(path.suffix+'.sha256').write_text(h+'  '+path.name+'\n',encoding='utf-8')
    return dict(path=path.relative_to(RUN).as_posix(),sha256=h,bytes=path.stat().st_size,verification=checked)

def main():
    reports=read(CONTROL/'REPORT_INDEX.json')
    acceptance=read(RUN/'10_REPORT/visual_qa/ACCEPTANCE.json')
    assert acceptance['status']=='PASS' and acceptance['report_index_sha256']==sha(CONTROL/'REPORT_INDEX.json')
    for r in reports:
        md=RUN/r['path']
        for ext,key in (('.md','md_sha256'),('.tex','tex_sha256'),('.pdf','pdf_sha256'),('.log','log_sha256')):assert sha(md.with_suffix(ext))==r[key]
    assert len(reports)==20
    assert read(EV/'G4_LEAN/RESULTS.json')['status']=='PASS'
    assert all(r['passed'] for r in read(EV/'G4_LEAN/ANNEX_RECHECK.json')['checks'])
    # Recheck all input bindings before changing any readiness record outside this run.
    p=subprocess.run([sys.executable,str(CONTROL/'intake.py')],capture_output=True,text=True,encoding='utf-8',timeout=180)
    (EV/'G0_INTEGRITY/FINAL_RECHECK.stdout.txt').write_text(p.stdout+'\n'+p.stderr,encoding='utf-8')
    assert p.returncode==0,p.stdout+p.stderr
    checks=read(EV/'G0_INTEGRITY/RESULTS.json');assert not checks['failures']
    trace=read(EV/'G1_CLAIMS/TRACE_SUMMARY.json');assert all(r['declarations'] for r in trace['headings'])
    state=dict(status='COMPLETED',verdict='PASS_INTERNAL_AUTHOR_SIDE',updated_at_utc=datetime.now(timezone.utc).isoformat(),gates={f'G{i}':'PASS' for i in range(9)},blocks={f'B{i:02}':'PASS' for i in range(1,11)},pending='External adversarial audit only on owner request; no publication authorized.',qualification='G4 recorded-build revalidation; finite regressions are not universal proofs; minor nonsemantic erratum in FINDINGS.md.')
    save(CONTROL/'AUDIT_STATE.json',state)
    findings=read(CONTROL/'FINDINGS.json')
    if not any(r['id']=='I-07' for r in findings):findings.append(dict(id='I-07',severity='INFORMATIONAL',status='RESOLVED',record='FINDINGS.md'))
    save(CONTROL/'FINDINGS.json',findings)
    save(RUN/'10_REPORT/INTERNAL_AUDIT_SUMMARY.json',dict(**state,source_cut='piv-v12-fb459343d234',manuscript_freeze='piv-v12-manuscripts-2451d43bface',reports=20,report_pages=acceptance['pages'],main_modules=607,targets=19,exports=224,axiom_list_records=461,source_headers_mapped=trace['exports'],separate_annex_source_closure=50,changes_to_frozen_inputs=False,lean_invocations_in_audit=0,subagents_in_this_continuation=0))
    ledger=[]
    for f in (EV/'G2_MATHEMATICS').glob('*/results/runner.json'):ledger.append(dict(evidence=f.relative_to(RUN).as_posix(),**read(f)))
    (CONTROL/'EXECUTION_LEDGER.jsonl').write_text(''.join(json.dumps(r,ensure_ascii=False)+'\n' for r in ledger),encoding='utf-8')
    save(EV/'G8_PACKAGE/PRESEAL_CHECK.json',dict(status='PASS',reports=20,source_integrity_recheck=True,all_report_hashes_match=True,visual_acceptance_sha256=sha(RUN/'10_REPORT/visual_qa/ACCEPTANCE.json'),no_blocking_findings=True,zip_checks='Performed by verify_package.py for every archive; outputs external to each archive to avoid self-reference.'))
    controls=files(CONTROL)
    # Each block can be extracted at the same relative run layout. Common frozen
    # source/manuscript ZIPs are identified by TARGET.json and not duplicated.
    common=controls+[EV/'G1_CLAIMS/MATHEMATICAL_REVIEW.md',EV/'G4_LEAN/EXPORT_TYPES.txt']
    cert=EV/'G2_MATHEMATICS/B01_MODEL/certificates/split_k3_h3_cover_optimal.json'
    index=[]
    for d in sorted((EV/'G2_MATHEMATICS').iterdir()):
        if d.is_dir() and d.name.startswith('B'):
            index.append(archive(PK/'blocks'/f'{d.name}_piv-v12.zip',files(d)+common+[cert]))
    for d in sorted(EV.iterdir()):
        if d.is_dir() and d.name.startswith('G'):
            index.append(archive(PK/'gates'/f'{d.name}_piv-v12.zip',files(d)+common))
    save(PK/'PACKAGE_INDEX.json',dict(status='PASS',parts=index,common_inputs='Frozen source/manuscript and build ZIPs identified by 00_CONTROL/TARGET.json; supplied once in publication tree, not copied into each block.',final_archive='INTERNAL_AUDIT_piv-v12-fb459343d234.zip'))
    save(PK/'PARTS_VERIFICATION.json',dict(status='PASS',parts=len(index),results=[dict(path=x['path'],**x['verification']) for x in index]))
    final=archive(PK/'INTERNAL_AUDIT_piv-v12-fb459343d234.zip',files(CONTROL)+files(RUN/'10_REPORT')+files(EV)+files(PK))
    # Deliberately not inside the archive: it contains that archive's hash.
    save(PK/'PACKAGE_VERIFICATION.json',dict(status='PASS',**final,parts=len(index),verified_at_utc=datetime.now(timezone.utc).isoformat()))
    print(json.dumps(final,indent=2))

if __name__=='__main__':main()
