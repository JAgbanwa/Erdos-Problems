"""Rebuild selected public targets, then execute audits against the frozen tree.

Uses the pinned toolchain via Lake. A cache is permitted and disclosed; this
is an author-side reproduction, not an independent clean-room run.
"""
from pathlib import Path
import argparse, datetime, hashlib, json, shutil, subprocess

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT/'05_formalization/lean_draft_freeze'
OUT = ROOT/'03_reproducibility/author_build_evidence'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--lake', default=shutil.which('lake') or 'lake')
    args = parser.parse_args()
    cut = json.loads((ROOT/'04_integrity/baseline/LEAN_CUT.json').read_text(encoding='utf-8'))
    before = {f: sha(LEAN/f) for f in cut['source_hashes']}
    assert before == cut['source_hashes'], 'Freeze changed before build'
    OUT.mkdir(parents=True, exist_ok=True)
    jobs = [('build', ['build', 'PaperIV', 'PaperIV.Audit', 'PaperIV.ConeAudit', 'BoundedCliqueGap.AxiomCheck']),
            ('axioms', ['env','lean','PaperIV/Audit.lean']),
            ('cones', ['env','lean','PaperIV/ConeAudit.lean']),
            ('supplement', ['env','lean',str(ROOT/'03_reproducibility/recorded_lean_audits/SupplementAudit.lean')]),
            ('bounded', ['env','lean','BoundedCliqueGap/AxiomCheck.lean']),
            ('public_contracts', ['env','lean',str(ROOT/'03_reproducibility/PublicContracts.lean')])]
    record = {'started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
              'mode':'author-side cache-assisted Lake rebuild; not independent clean-room',
              'toolchain':(LEAN/'lean-toolchain').read_text().strip(),
              'snapshot_sha256':cut['sha256'], 'commands':[]}
    for name, command in jobs:
        log = OUT/(name+'.log')
        print('Starting',name,flush=True)
        with log.open('w',encoding='utf-8') as out:
            proc = subprocess.run([args.lake]+command,cwd=LEAN,stdout=out,stderr=subprocess.STDOUT)
        record['commands'].append({'name':name,'command':['lake']+command,'exit_code':proc.returncode,'log_sha256':sha(log)})
        record['sources_unchanged'] = all(sha(LEAN/f)==h for f,h in before.items())
        record['updated_utc'] = datetime.datetime.now(datetime.timezone.utc).isoformat()
        (OUT/'RESULTS.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
        print(name,proc.returncode,flush=True)
        if proc.returncode or not record['sources_unchanged']: raise SystemExit(1)

if __name__ == '__main__': main()
