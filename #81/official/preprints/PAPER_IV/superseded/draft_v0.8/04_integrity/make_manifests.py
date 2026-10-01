"""Seal only the curated Paper IV package, then the tracked repository surface."""
from pathlib import Path
import hashlib, json, os, subprocess

ROOT=Path(__file__).resolve().parents[1]
REPO=ROOT.parents[1]
def accessible(p):
    return Path('\\\\?\\'+str(p.resolve())) if os.name=='nt' else p
def sha(p): return hashlib.sha256(accessible(p).read_bytes()).hexdigest()
def included(p):
    return p.is_file() and '.lake' not in p.parts and '__pycache__' not in p.parts
def public_files():
    for base,dirs,names in os.walk(ROOT):
        dirs[:]=[d for d in dirs if d not in ('.lake','__pycache__')]
        for n in names: yield Path(base)/n
def main():
    results=json.loads((ROOT/'02_validation/01_INTERNAL_AUDITS/run_draft_20260921/CHECK_RESULTS.json').read_text())
    assert results['passed']==results['total'], 'Cannot seal failing checks'
    own={'04_integrity/PACKAGE_MANIFEST.sha256','04_integrity/PACKAGE_MANIFEST.sha256.sha256'}
    paths=sorted(p for p in public_files() if p.relative_to(ROOT).as_posix() not in own)
    manifest=ROOT/'04_integrity/PACKAGE_MANIFEST.sha256'
    manifest.write_text(''.join(sha(p)+'  '+p.relative_to(ROOT).as_posix()+'\n' for p in paths),encoding='utf-8')
    manifest.with_name(manifest.name+'.sha256').write_text(sha(manifest)+'  '+manifest.name+'\n',encoding='utf-8')
    tracked=subprocess.check_output(['git','ls-files','-z'],cwd=REPO).decode().split('\0')
    allpaths={REPO/n for n in tracked if n and n!='manifest_sha256.txt'}
    allpaths|=set(public_files())
    assert all(accessible(p).is_file() for p in allpaths)
    (REPO/'manifest_sha256.txt').write_text(''.join(sha(p)+'  '+p.relative_to(REPO).as_posix()+'\n' for p in sorted(allpaths)),encoding='utf-8',newline='\n')
    print('Paper IV files:',len(paths),'Repository manifest entries:',len(allpaths))

if __name__=='__main__': main()
