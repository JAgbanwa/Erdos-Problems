"""Supplemental post-build verifier. No Lean, network or changes to frozen files.

Required input inventory pins every log. Missing, extra or changed logs fail closed.
This checks logs, not mathematical validity or completeness of Lean's trusted kernel.
"""
from pathlib import Path
import argparse, hashlib, json, re, sys
ROOT=Path(__file__).resolve().parent
PAPER=ROOT.parents[1]
SORRY=re.compile(r"\bsorryAx\b|declaration\s+uses\s+[`'\"‘’“”]*sorry\b",re.I)
# Deliberately retain the frozen runner's case-sensitive error rule.
ERROR=re.compile(r'^.*error(?:\(|:)',re.M)
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def alerts(text): return bool(SORRY.search(text) or ERROR.search(text))
def verify(manifest):
    errors=[]; checked=0
    for group in manifest['groups']:
        directory=PAPER/group['directory']
        observed={p.name for p in directory.glob('*.log')}
        expected={e['name'] for e in group['logs']}
        if observed!=expected: errors.append({'directory':group['directory'],'missing':sorted(expected-observed),'extra':sorted(observed-expected)})
        for entry in group['logs']:
            p=directory/entry['name']
            if not p.is_file(): continue
            checked+=1
            if sha(p)!=entry['sha256']: errors.append({'file':str(p),'error':'HASH_MISMATCH'})
            if alerts(p.read_text(encoding='utf-8',errors='replace')): errors.append({'file':str(p),'error':'ERROR_OR_SORRY'})
    if checked!=manifest['expected_total']: errors.append({'checked':checked,'expected':manifest['expected_total']})
    return {'status':'PASS' if not errors else 'FAIL','logs_checked':checked,'errors':errors,
            'sorry_pattern':SORRY.pattern,'error_pattern':ERROR.pattern,'lean_executed':False}
def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--inventory',type=Path,default=ROOT/'LOG_INVENTORY.json')
    ap.add_argument('--output',type=Path,required=True)
    args=ap.parse_args()
    result=verify(json.loads(args.inventory.read_text(encoding='utf-8')))
    with args.output.open('x',encoding='utf-8') as f: json.dump(result,f,indent=2); f.write('\n')
    print(json.dumps(result)); return 0 if result['status']=='PASS' else 1
if __name__=='__main__': sys.exit(main())
