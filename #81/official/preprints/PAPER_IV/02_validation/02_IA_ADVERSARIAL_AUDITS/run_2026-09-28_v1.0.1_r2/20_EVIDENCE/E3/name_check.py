"""Check that every backticked Lean identifier/module in the EN/ES manuscripts exists in the frozen source."""
import re, json, sys
from pathlib import Path
ROOT = Path('C:/piv_r2/src/lean_v1.0_freeze')
MS = Path('C:/Users/jtraverso/e81p4-publish/preprints/PAPER_IV/01_manuscript/v1.0.1_candidate')
src = {f.relative_to(ROOT).with_suffix('').as_posix().replace('/', '.'): f.read_text(encoding='utf-8') for f in ROOT.rglob('*.lean')}
alltext = '\n'.join(src.values())
declpat = re.compile(r'(?:theorem|lemma|def|abbrev|structure|irreducible_def|instance|class|inductive)\s+([^\s:({\[]+)')
decls = set()
for t in src.values():
    for m in declpat.finditer(t):
        decls.add(m.group(1))
modshort = {}
for m in src:
    modshort.setdefault(m.split('.')[-1], []).append(m)
out = {}
for lang in ['en', 'es']:
    text = (MS / f'PAPER_IV_preprint_v1.0.1_{lang}.md').read_text(encoding='utf-8')
    toks = sorted(set(re.findall(r'`([A-Za-z0-9_.\']+)`', text)))
    res = []
    for t in toks:
        parts = t.split('.')
        last = parts[-1]
        ok_mod = t in src or any(k.endswith('.' + t) or k == t for k in src) or last in modshort
        ok_decl = last in decls or t in decls
        # qualified decl: check namespace/module hint
        res.append({'token': t, 'module_or_short_module': bool(ok_mod), 'decl_name': bool(ok_decl)})
    out[lang] = res
missing = {lang: [r['token'] for r in v if not (r['module_or_short_module'] or r['decl_name'])] for lang, v in out.items()}
json.dump({'tokens': out, 'missing': missing}, open('name_check.json', 'w', encoding='utf-8'), indent=1, ensure_ascii=False)
print(json.dumps(missing, indent=1, ensure_ascii=False))
