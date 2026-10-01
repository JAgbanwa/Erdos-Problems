"""Static extraction of Lean declaration headers (statement up to ':=') from the frozen source copy.
Auditor-written. Usage: python extract_headers.py Module.decl [Module.decl ...]  (Module relative to root, dots)
Prints file, line, and the header text. Also reports whether the name occurs as 'theorem'/'lemma'/'def'.
"""
import re, sys
from pathlib import Path

ROOT = Path('C:/piv_r2/src/lean_v1.0_freeze')


def find_decl(short):
    pat = re.compile(r'^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*(theorem|lemma|def|abbrev|structure|instance|axiom)\s+' + re.escape(short) + r'(\s|$|\{|\(|:)')
    hits = []
    for f in ROOT.rglob('*.lean'):
        lines = f.read_text(encoding='utf-8').splitlines()
        for i, l in enumerate(lines):
            if pat.match(l):
                hits.append((f, i, lines))
    return hits


def header(lines, i):
    out = []
    depth = 0
    for j in range(i, min(i + 80, len(lines))):
        l = lines[j]
        out.append(l)
        s = re.sub(r'--.*$', '', l)
        if re.search(r':=\s*(by\b|$)|:=\s*$|\bwhere\s*$', s) or s.strip().startswith(':= '):
            break
    return '\n'.join(out)


for arg in sys.argv[1:]:
    short = arg.split('.')[-1]
    mod_hint = '.'.join(arg.split('.')[:-1])
    hits = find_decl(short)
    if mod_hint:
        filt = [h for h in hits if mod_hint.replace('.', '/') in str(h[0]).replace('\\', '/')]
        hits = filt or hits
    print('=' * 100)
    print('QUERY', arg, 'hits', len(hits))
    for f, i, lines in hits:
        print('--- %s:%d' % (f.relative_to(ROOT).as_posix(), i + 1))
        print(header(lines, i))
