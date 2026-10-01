"""Explicitly rebuild the supplementary import closure before its audit.

These targets are deliberately separate from the main PaperIV aggregate.
"""
from pathlib import Path
import hashlib,json,shutil,subprocess

ROOT=Path(__file__).resolve().parents[1]
LEAN=ROOT/'05_formalization/lean_draft_freeze'
OUT=ROOT/'03_reproducibility/author_build_evidence'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
lake=shutil.which('lake') or 'lake'
cut=json.loads((ROOT/'04_integrity/baseline/LEAN_CUT.json').read_text())
records=[]
for name,cmd in [
 ('supplement_build',['build','ThreeRegime.CompleteStateAllOrders','FarExploration.CleanupRigidVerdict']),
 ('supplement_after_build',['env','lean',str(ROOT/'03_reproducibility/recorded_lean_audits/SupplementAudit.lean')])]:
    with (OUT/(name+'.log')).open('w',encoding='utf-8') as out:
        proc=subprocess.run([lake]+cmd,cwd=LEAN,stdout=out,stderr=subprocess.STDOUT)
    records.append({'name':name,'command':['lake']+cmd,'exit_code':proc.returncode,'log_sha256':sha(OUT/(name+'.log'))})
    unchanged=all(sha(LEAN/f)==h for f,h in cut['source_hashes'].items())
    (OUT/'SUPPLEMENT_REFRESH.json').write_text(json.dumps({'commands':records,'sources_unchanged':unchanged},indent=2)+'\n',encoding='utf-8')
    print(name,proc.returncode,flush=True)
    if proc.returncode or not unchanged: raise SystemExit(1)
