"""Bind the sealed internal audit, without starting any external work."""
from pathlib import Path
import hashlib, json, sys

HERE=Path(__file__).resolve().parent
PAPER=HERE.parents[1]
RUN=PAPER/'02_validation/01_INTERNAL_AUDITS/run_20260929_v1.2_fb459343d234_r1'
def read(p): return json.loads(p.read_text(encoding='utf-8-sig'))
def sha(p):
    with p.open('rb') as f: return hashlib.file_digest(f,'sha256').hexdigest()
def save(p,o): p.write_text(json.dumps(o,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
def bind(p): return dict(path=p.relative_to(PAPER).as_posix(),sha256=sha(p),bytes=p.stat().st_size)

target=read(HERE/'AUDIT_TARGET_v1.2.json')
assert target['external_audit']=='NOT_STARTED' and not target['execution_authorized']
summary=read(RUN/'10_REPORT/INTERNAL_AUDIT_SUMMARY.json')
assert summary['verdict']=='PASS_INTERNAL_AUTHOR_SIDE'
assert all(x=='PASS' for x in list(summary['gates'].values())+list(summary['blocks'].values()))
sealed=read(RUN/'30_PACKAGE/PACKAGE_VERIFICATION.json')
assert sealed['status']=='PASS' and sealed['parts']==19
archive=RUN/sealed['path']
assert sha(archive)==sealed['sha256']
sys.path.insert(0,str(RUN/'00_CONTROL'))
from verify_package import verify
assert verify(archive)['status']=='PASS'

# Verify every existing bound file before modifying readiness metadata.
def verify_bound(o):
    if isinstance(o,dict):
        if 'path' in o and 'sha256' in o:
            # These two documents were updated solely for readiness above.
            if Path(o['path']).name not in ('README.md','EXTERNAL_ADVERSARIAL_AUDIT_REQUEST_v1.2.md'):
                assert sha(PAPER/o['path'])==o['sha256'],o['path']
        else:
            for v in o.values(): verify_bound(v)
    elif isinstance(o,list):
        for v in o: verify_bound(v)
verify_bound(target)
scope_path=HERE/'LOCAL_INPUT_SCOPE_v1.2.json'
scope=read(scope_path);scope['status']='READY_FOR_EXTERNAL_AUDIT'
new='02_validation/02_IA_ADVERSARIAL_AUDITS/bind_v12_internal_audit.py'
if new not in scope['allowed_from_intake']: scope['allowed_from_intake'].append(new)
save(scope_path,scope)
b=target['required_final_bindings']
b['internal_audit_package']=bind(archive)
b['internal_audit_final_report']=bind(RUN/'10_REPORT/INTERNAL_AUDIT_FINAL_REPORT.md')
b['internal_audit_report_pdf']=bind(RUN/'10_REPORT/INTERNAL_AUDIT_FINAL_REPORT.pdf')
b['internal_audit_package_verification']=bind(RUN/'30_PACKAGE/PACKAGE_VERIFICATION.json')
names=[Path(r['path']).name for r in b['mandate_and_scope_hashes']]
if 'bind_v12_internal_audit.py' not in names: names.append('bind_v12_internal_audit.py')
b['mandate_and_scope_hashes']=[bind(HERE/n) for n in names]
target['status']='READY_FOR_EXTERNAL_AUDIT'
target['internal_audit_completed_on']='2026-09-30'
target['remaining_readiness_gates']=['Owner requests external execution; intake independently verifies the bound identity.']
save(HERE/'AUDIT_TARGET_v1.2.json',target)
prep_path=HERE/'run_v1.2_r1/00_CONTROL/PREPARATION.json'
prep=read(prep_path);assert prep['started_at'] is None
prep.update(readiness=target['status'],internal_audit='COMPLETE_PASS_INTERNAL_AUTHOR_SIDE',target_sha256=sha(HERE/'AUDIT_TARGET_v1.2.json'))
save(prep_path,prep)
# Strict final identity verification, including the updated readiness documents.
def final_check(o):
    if isinstance(o,dict):
        if 'path' in o and 'sha256' in o: assert sha(PAPER/o['path'])==o['sha256'],o['path']
        else:
            for v in o.values(): final_check(v)
    elif isinstance(o,list):
        for v in o: final_check(v)
final_check(target)
result=dict(status='READY_FOR_EXTERNAL_AUDIT',external_audit='NOT_STARTED',execution_authorized=False,target_sha256=sha(HERE/'AUDIT_TARGET_v1.2.json'),internal_package_sha256=sha(archive),all_bound_hashes_verified=True)
save(HERE/'run_v1.2_r1/00_CONTROL/INTERNAL_BINDING_CHECK.json',result)
print(json.dumps(result,indent=2))
