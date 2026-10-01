"""Bind candidate artifacts and verify immutable Lean; not an audit or release."""
from pathlib import Path
import hashlib,json,re,datetime,zipfile
ROOT=Path(__file__).resolve().parent
PAPER=ROOT.parents[1]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
manifest=PAPER/'03_reproducibility/build_piv-v12-fb459343d234/SOURCE_MANIFEST.json'
lean=PAPER/'05_formalization/lean_piv-v12-fb459343d234'
expected=json.loads(manifest.read_text(encoding='utf-8-sig'))
bad=[r['path'] for r in expected if not (lean/r['path']).is_file() or sha(lean/r['path'])!=r['sha256']]
source_check={'checked_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'manifest_sha256':sha(manifest),'entries_checked':len(expected),'changed_or_missing':bad,'status':'UNCHANGED' if not bad else 'MISMATCH'}
(ROOT/'LEAN_IDENTITY_CHECK.json').write_text(json.dumps(source_check,indent=2)+'\n',encoding='utf-8')
assert not bad, 'Frozen source differs: do not prepare review'
files=[]
for lang in ('en','es'):
    stem=f'PAPER_IV_preprint_v1.21_{lang}'
    files.extend(ROOT/(stem+'.'+ext) for ext in ('md','tex','pdf'))
    for path in re.findall(r'!\[.*?\]\(([^)]+)\.png\)',(ROOT/(stem+'.md')).read_text(encoding='utf-8')):
        files.extend(ROOT/(path+'.'+ext) for ext in ('png','pdf'))
names=('RESPONSE_TO_AUDIT_v1.21.md','EVIDENCE_AND_ANNEX_CORRIGENDUM.md','REVIEW_HANDOFF_v1.21.md','VISUAL_REVIEW_v1.21.md',
       'FINAL_EDITORIAL_REVALIDATION_v1.21.md','EDITORIAL_CHANGE_REPORT_v1.21.md','EXTERNAL_EVIDENCE_BINDING.json',
       'sorry_log_recheck.py','SORRY_RECHECK.json','RUNNER_SORRY_FIX_NOT_APPLIED.patch','final_audit_editorial_sync.py','prepare_revalidation_identity.py',
       'editorial_checks.py','finish_editorial.py','final_prose_pass.py','artifact_checks.py','bind_review.py',
       'PROTECTED_BASELINE.json','SEMANTIC_CHECKS.json','EXPOSITORY_CHECKS.json','ARTIFACT_CHECKS.json','AXIOM_COUNT_RECONCILIATION.json','LEAN_IDENTITY_CHECK.json',
       'CHANGES_en.diff','CHANGES_es.diff','build_draft.py','build_draft_en.py','typeset_helpers.py','series_template.tex','series_template_en.tex','prepare_typeset.py','make_stability_figure.py','make_stability_figure_es.py',
       'compiler_console_en.log','compiler_console.log')
files.extend(ROOT/n for n in names)
files.extend(ROOT.glob('qa_*/contact_*.png'))
files.extend(p for p in (ROOT/'review_history').rglob('*') if p.is_file())
rows=[{'path':str(p.relative_to(ROOT)).replace('\\','/'),'sha256':sha(p),'bytes':p.stat().st_size} for p in sorted(set(files))]
data={'identity':'Paper-IV-v1.21-r1-editorial-revalidation','status':'PREPARED_FOR_REVALIDATION','release':False,
      'lean_cut':'piv-v12-fb459343d234','source_manifest_sha256':sha(manifest),
      'audit_request':{'path':'02_validation/02_IA_ADVERSARIAL_AUDITS/EXTERNAL_ADVERSARIAL_REVALIDATION_v1.21_r1.md','sha256':sha(PAPER/'02_validation/02_IA_ADVERSARIAL_AUDITS/EXTERNAL_ADVERSARIAL_REVALIDATION_v1.21_r1.md')},
      'limits':'Editorial revalidation pending. Completed external E4 PASS may be reused after identity verification; no new Lean build authorized. No runtime fonts, caches, credentials or project objects included.',
      'files':rows}
dest=ROOT/'MANUSCRIPT_REVIEW_MANIFEST.json'
dest.write_text(json.dumps(data,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
(ROOT/'MANUSCRIPT_REVIEW_MANIFEST.sha256').write_text(sha(dest)+'  '+dest.name+'\n',encoding='utf-8')
archive=ROOT/'PAPER_IV_v1.21_REVIEW_PACKAGE_r1.zip'
assert not archive.exists(), 'Do not overwrite an identified review package'
with zipfile.ZipFile(archive,'x',compression=zipfile.ZIP_DEFLATED,compresslevel=3) as z:
    for row in rows:z.write(ROOT/row['path'],row['path'])
    z.write(dest,dest.name)
    z.write(ROOT/'MANUSCRIPT_REVIEW_MANIFEST.sha256','MANUSCRIPT_REVIEW_MANIFEST.sha256')
with zipfile.ZipFile(archive) as z:
    assert z.testzip() is None
    for row in rows:assert hashlib.sha256(z.read(row['path'])).hexdigest()==row['sha256']
(ROOT/'PAPER_IV_v1.21_REVIEW_PACKAGE_r1.sha256').write_text(sha(archive)+'  '+archive.name+'\n',encoding='utf-8')
print(json.dumps({'source':source_check,'manuscript_manifest_sha256':sha(dest),'package_sha256':sha(archive),'members':len(rows)+2},indent=2))
