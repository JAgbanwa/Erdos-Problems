"""Negative tests and read-only historical scan. Creates only r3 evidence."""
from pathlib import Path
import json, tempfile, subprocess, sys
import verify_frozen_logs as v
ROOT=Path(__file__).resolve().parent
rel='02_validation/02_IA_ADVERSARIAL_AUDITS/run_v1.2_r1'
groups=[]
for name,count in [(rel+'/10_LOGS/E4_main/modules',608),(rel+'/10_LOGS/E4_annex/modules',50),
    ('03_reproducibility/full_rebuild_v12_20260929_r2/combined/modules',422),
    ('03_reproducibility/full_rebuild_v12_20260929_resume/combined/modules',186)]:
    logs=sorted((v.PAPER/name).glob('*.log')); assert len(logs)==count
    groups.append({'directory':name,'logs':[{'name':p.name,'sha256':v.sha(p)} for p in logs]})
manifest={'expected_total':1266,'groups':groups}
with (ROOT/'LOG_INVENTORY.json').open('x',encoding='utf-8') as f: json.dump(manifest,f,indent=2)
real=(v.PAPER/rel/'20_EVIDENCE/E4/AuditorNegControl.log').read_text(encoding='utf-8')
cases=[(real,True),('warning: declaration uses `sorry`',True),("declaration uses 'sorry'",True),
    ('declaration uses "sorry"',True),('declaration uses ‘sorry’',True),('declaration uses “sorry”',True),
    ('DECLARATION USES `SORRY`',True),('declaration  uses\n`sorry`',True),('[sorryAx]',True),
    ('theorem no_sorry_used : True',False),('declaration uses `sorryish`',False),
    ('depends on axioms: [propext, Classical.choice, Quot.sound]',False),
    ('error: bad declaration',True),('source.lean:10: error(unknown)',True),('ERROR: uppercase',False)]
results=[{'input':t,'expected':e,'observed':v.alerts(t)} for t,e in cases]
assert all(r['expected']==r['observed'] for r in results)
historical=v.verify(manifest); assert historical['status']=='PASS'
# Test actual CLI failure, not only a detector predicate. All test data stays temporary.
negative=[]
with tempfile.TemporaryDirectory(prefix='paperiv-r3-logtest-') as temp:
    td=Path(temp); log=td/'probe.log'; log.write_text('clean\n',encoding='utf-8')
    inv={'expected_total':1,'groups':[{'directory':str(td),'logs':[{'name':log.name,'sha256':v.sha(log)}]}]}
    for label,text,repin in [('sorry_warning','declaration uses `sorry`',True),('error','error: test',True),('changed','changed',False),('missing',None,False)]:
        if text is None: log.unlink()
        else: log.write_text(text,encoding='utf-8')
        if repin: inv['groups'][0]['logs'][0]['sha256']=v.sha(log)
        ip=td/'inventory.json'; ip.write_text(json.dumps(inv),encoding='utf-8')
        proc=subprocess.run([sys.executable,str(ROOT/'verify_frozen_logs.py'),'--inventory',str(ip),'--output',str(td/(label+'.json'))],capture_output=True,text=True)
        assert proc.returncode==1,(label,proc.stdout,proc.stderr)
        negative.append({'case':label,'exit_code':proc.returncode,'result':json.loads((td/(label+'.json')).read_text())})
with (ROOT/'LOG_VERIFIER_TESTS.json').open('x',encoding='utf-8') as f:
    json.dump({'unit_cases':results,'cli_negative_cases':negative,'historical_scan':historical,
        'legacy_error_semantics_preserved':True,'note':'Uppercase ERROR is intentionally not a new rule; inherited error alternative is unchanged.'},f,indent=2)
print(json.dumps({'unit_tests':len(results),'negative_cli_tests':len(negative),'logs':historical['logs_checked'],'status':'PASS'}))
