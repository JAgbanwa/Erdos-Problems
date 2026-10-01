"""Read existing logs only. No imports from build runners; never launches Lean."""
from pathlib import Path
import hashlib, json, re, difflib
ROOT = Path(__file__).resolve().parent
PAPER = ROOT.parents[1]
RUN = PAPER / '02_validation/02_IA_ADVERSARIAL_AUDITS/run_v1.2_r1'
PATTERN = r"sorryAx|declaration\s+uses\s+[`'\"‘’“”]*sorry\b"
def detected(text):
    return bool(re.search(PATTERN, text, re.I))
def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()
negative = RUN / '20_EVIDENCE/E4/AuditorNegControl.log'
cases = ["warning: declaration uses `sorry`", "warning: declaration uses 'sorry'",
         'warning: declaration uses "sorry"', 'declaration uses sorry',
         'declaration uses ‘sorry’', '[sorryAx]', 'DECLARATION USES `SORRY`']
tests = {s: detected(s) for s in cases}
tests['captured_auditor_negative'] = detected(negative.read_text(encoding='utf-8'))
tests['clean_standard_axioms_accepted'] = not detected('depends on axioms: [propext, Classical.choice, Quot.sound]')
assert all(tests.values())
folders = [RUN/'10_LOGS/E4_main/modules', RUN/'10_LOGS/E4_annex/modules',
           PAPER/'03_reproducibility/full_rebuild_v12_20260929_resume/combined/modules']
rows = []
for folder in folders:
    files = sorted(folder.glob('*.log'))
    assert files, f'No logs in {folder}'
    for p in files:
        t = p.read_text(encoding='utf-8-sig')
        rows.append({'path':str(p), 'sha256':sha(p), 'detector_hit':detected(t),
                     'broad_sorry_hit':bool(re.search('sorry',t,re.I))})
assert not any(r['detector_hit'] or r['broad_sorry_hit'] for r in rows)
freeze = PAPER/'05_formalization/lean_piv-v12-fb459343d234'
patch = []
changes = {
 'tools/paperiv_build.py': ('sorry = "declaration uses \'sorry\'" in log', 'sorry = bool(re.search('+repr(PATTERN)+', log, re.I))'),
 'tools/audit_publication.py': ('r"sorryAx|declaration uses \'sorry\'|^.*error(?:\\(|:)", log, re.M', 'r"sorryAx|declaration\\s+uses\\s+.*?sorry\\b|^.*error(?:\\(|:)", log, re.M | re.I'),
}
for name,(old,new) in changes.items():
    t = (freeze/name).read_text(encoding='utf-8')
    assert t.count(old)==1
    patched = t.replace(old,new)
    compile(patched,name,'exec')  # Syntax only; no execution of runners.
    patch.extend(difflib.unified_diff(t.splitlines(True),patched.splitlines(True),fromfile='a/'+name,tofile='b/'+name))
(ROOT/'RUNNER_SORRY_FIX_NOT_APPLIED.patch').write_text(''.join(patch),encoding='utf-8')
out = {'status':'PASS','scope':'Existing logs, detector regression and patch syntax only; no Lean build',
       'negative_log':{'path':str(negative),'sha256':sha(negative)},'tests':tests,
       'log_count':len(rows),'groups':{str(p):len(list(p.glob('*.log'))) for p in folders},
       'logs':rows,'frozen_runners_modified':False}
(ROOT/'SORRY_RECHECK.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:v for k,v in out.items() if k!='logs'},indent=2))
