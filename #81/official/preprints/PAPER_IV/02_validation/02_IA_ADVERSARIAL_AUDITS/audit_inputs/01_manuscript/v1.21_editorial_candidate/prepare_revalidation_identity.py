"""Bind read-only prior audit evidence, then the new editorial package. No build."""
from pathlib import Path
import hashlib, json, sys, zipfile
ROOT=Path(__file__).resolve().parent
PAPER=ROOT.parents[1]
AUD=PAPER/'02_validation/02_IA_ADVERSARIAL_AUDITS'
RUN=AUD/'run_v1.2_r1'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def record(p): return {'path':str(p),'sha256':sha(p),'bytes':p.stat().st_size}
def read(p): return json.loads(p.read_text(encoding='utf-8-sig'))
if '--target' not in sys.argv:
    summary=read(RUN/'30_REPORT/SUMMARY.json')
    assert summary['gates']['E4_formal_reproduction']=='PASS'
    assert summary['overall_verdict']=='INCONCLUSIVE'
    manifest=read(RUN/'40_PACKAGE/RUN_MANIFEST.json')
    changed=[r['path'] for r in manifest if not (RUN/r['path']).is_file() or sha(RUN/r['path'])!=r['sha256']]
    assert not changed,changed
    archive=RUN/'40_PACKAGE/EXTERNAL_AUDIT_run_v1.2_r1.zip'
    assert sha(archive)==Path(str(archive)+'.sha256').read_text().split()[0]
    with zipfile.ZipFile(archive) as z: assert z.testzip() is None
    counts={}
    for name,minimum in [('E4_main',607),('E4_annex',50)]:
        rows=[json.loads(s) for s in (RUN/f'10_LOGS/{name}/records.jsonl').read_text().splitlines() if s.strip()]
        assert all(r['status']=='PASS' and r['exit']==0 and not r['sorry_warning'] for r in rows)
        counts[name]={'records':len(rows),'distinct_modules':len({r['module'] for r in rows})}
        assert counts[name]['distinct_modules']>=minimum
    selected=['30_REPORT/FINAL_AUDIT_REPORT.md','30_REPORT/FINAL_AUDIT_REPORT.pdf',
      '30_REPORT/SUMMARY.json','30_REPORT/FINDINGS.csv','00_CONTROL/AUDITOR_DECLARATION.json',
      '00_CONTROL/CORRECTIONS.md','20_EVIDENCE/E4/E4_RECORD.md','20_EVIDENCE/E4/AuditorASProbe.log',
      '20_EVIDENCE/E4/AuditorChecks.log','20_EVIDENCE/E4/AuditorNegControl.log',
      '20_EVIDENCE/E4/olean_vs_author.json','20_EVIDENCE/E4/cache_diff.json',
      '20_EVIDENCE/E4/target_log_analysis.json','10_LOGS/E4_main_console.log',
      '10_LOGS/E4_main/records.jsonl','10_LOGS/E4_annex/records.jsonl',
      '10_LOGS/E4_annex_console.log','40_PACKAGE/RUN_MANIFEST.json']
    out={'previous_run':'run_v1.2_r1','previous_overall':'INCONCLUSIVE','previous_E4':'PASS',
      'prior_manifest_files_verified':len(manifest),'changed':changed,'records':counts,
      'archive':record(archive),'evidence':[record(RUN/n) for n in selected],
      'limitations':'Author identity/record check, not a new independent audit or compilation; auditor must validate reuse.'}
    (ROOT/'EXTERNAL_EVIDENCE_BINDING.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({k:v for k,v in out.items() if k!='evidence'},indent=2))
else:
    manifest=read(ROOT/'MANUSCRIPT_REVIEW_MANIFEST.json')
    assert all(sha(ROOT/r['path'])==r['sha256'] for r in manifest['files'])
    archive=ROOT/'PAPER_IV_v1.21_REVIEW_PACKAGE_r1.zip'
    with zipfile.ZipFile(archive) as z:
        assert z.testzip() is None
        assert all(hashlib.sha256(z.read(r['path'])).hexdigest()==r['sha256'] for r in manifest['files'])
    req=AUD/'EXTERNAL_ADVERSARIAL_REVALIDATION_v1.21_r1.md'
    source=PAPER/'03_reproducibility/build_piv-v12-fb459343d234/SOURCE_MANIFEST.json'
    out={'revision':'v1.21-r1','status':'PREPARED_NOT_STARTED','request':record(req),
       'manuscript_manifest':record(ROOT/'MANUSCRIPT_REVIEW_MANIFEST.json'),'manuscript_zip':record(archive),
       'source_manifest':record(source),'source_root':str(PAPER/'05_formalization/lean_piv-v12-fb459343d234'),
       'prior_evidence_binding':record(ROOT/'EXTERNAL_EVIDENCE_BINDING.json'),
       'new_lean_build_authorized':False,'output_directory':str(AUD/'run_v1.21_r1')}
    dest=AUD/'AUDIT_TARGET_v1.21.json'
    assert not dest.exists(),'Do not overwrite a bound target'
    dest.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
    Path(str(dest)+'.sha256').write_text(sha(dest)+'  '+dest.name+'\n',encoding='utf-8')
    print(json.dumps(out,indent=2))
