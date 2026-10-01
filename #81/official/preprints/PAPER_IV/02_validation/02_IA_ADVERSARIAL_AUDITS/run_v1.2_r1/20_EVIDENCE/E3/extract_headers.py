"""E3 static (auditor-written): extract literal statement headers (theorem/def ... up to the
top-level ':=' ) for listed declarations from the frozen source directory. Read-only.
usage: python extract_headers.py OUTFILE name1 name2 ...  (names may be qualified suffixes)"""
import re, sys, pathlib
SRC = pathlib.Path('C:/Users/jtraverso/e81p4-publish/preprints/PAPER_IV/05_formalization/lean_piv-v12-fb459343d234')
files = [p for p in SRC.rglob('*.lean') if '.lake' not in p.parts]
texts = {p: p.read_text(encoding='utf-8') for p in files}
out = []
for name in sys.argv[2:]:
    short = name.split('.')[-1]
    pat = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*(theorem|lemma|def|abbrev|structure|instance|class)\s+(?:[A-Za-z0-9_.]*\.)?' + re.escape(short) + r'\b', re.M)
    hits = []
    for p, t in texts.items():
        for m in pat.finditer(t):
            start = m.start()
            # capture until ':= by' or ':=' at depth 0 or 'where' for structures, cap 80 lines
            seg = t[start:start + 12000]
            lines = seg.splitlines()
            acc = []
            for ln in lines[:120]:
                acc.append(ln)
                if re.search(r':=\s*(by)?\s*$', ln) or re.search(r'\bwhere\s*$', ln) or re.search(r':=\s*\S', ln):
                    break
            # include namespace context
            ns = re.findall(r'^namespace\s+(\S+)', t[:start], re.M)
            ends = re.findall(r'^end\s+(\S+)', t[:start], re.M)
            lineno = t[:start].count('\n') + 1
            hits.append(f'--- {p.relative_to(SRC).as_posix()}:{lineno}  (namespaces opened before: {ns[-3:]}, ended: {ends[-3:]})\n' + '\n'.join(acc))
    out.append(f'=================== {name}  ({len(hits)} hit(s))\n' + '\n'.join(hits))
pathlib.Path(sys.argv[1]).write_text('\n\n'.join(out), encoding='utf-8')
print('\n\n'.join(out))
