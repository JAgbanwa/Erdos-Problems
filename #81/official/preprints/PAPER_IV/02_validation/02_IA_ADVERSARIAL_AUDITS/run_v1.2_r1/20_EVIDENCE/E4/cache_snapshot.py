"""Snapshot (path,size,mtime) of all files in the shared package build dirs + sha256 of key oleans."""
import os,sys,json,hashlib,pathlib
PKG=pathlib.Path('C:/Users/jtraverso/e81p4/preprints/PAPER_IV/05_formalization/lean/.lake/packages')
out={}
for d in sorted(PKG.iterdir()):
    for root,_,files in os.walk(d):
        for f in files:
            p=os.path.join(root,f)
            try: st=os.stat(p); out[os.path.relpath(p,PKG)]=[st.st_size,int(st.st_mtime)]
            except OSError: pass
key=PKG/'mathlib/.lake/build/lib/lean/Mathlib.olean'
json.dump({'files':len(out),'Mathlib.olean.sha256':hashlib.sha256(key.read_bytes()).hexdigest(),'entries':out},open(sys.argv[1],'w'))
print(len(out))
