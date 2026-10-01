"""E3/E1 (auditor-written): every backticked identifier in the v1.21 EN/ES Markdown that is NEW relative
to v1.2 must resolve to a module path, a declaration name, a namespace or a known tool/file in the
frozen Lean cut. Read-only."""
import re, pathlib, json, sys
B = pathlib.Path('C:/Users/jtraverso/e81p4-publish/preprints/PAPER_IV')
SRC = B / '05_formalization/lean_piv-v12-fb459343d234'
old = {l: (B / f'01_manuscript/v1.2_full_rebuild_candidate/PAPER_IV_preprint_v1.2_{l}.md').read_text(encoding='utf-8') for l in ('en', 'es')}
new = {l: (B / f'01_manuscript/v1.21_editorial_candidate/PAPER_IV_preprint_v1.21_{l}.md').read_text(encoding='utf-8') for l in ('en', 'es')}
code = lambda t: set(re.findall(r'`([^`\n]+)`', t))
lean_files = [p for p in SRC.rglob('*.lean')]
modules = {'.'.join(p.relative_to(SRC).with_suffix('').parts) for p in lean_files}
alltext = '\n'.join(p.read_text(encoding='utf-8') for p in lean_files)
decls = set(re.findall(r'^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*(?:theorem|lemma|def|abbrev|structure|instance|class|inductive)\s+([A-Za-z0-9_.\'«»]+)', alltext, re.M))
namespaces = set(re.findall(r'^namespace\s+(\S+)', alltext, re.M))
short = {d.split('.')[-1] for d in decls}
files = {p.relative_to(SRC).as_posix() for p in SRC.rglob('*') if p.is_file()}
def resolves(x):
    x = x.strip()
    if x in modules or x in decls or x in namespaces or x in files: return 'module/decl/ns/file'
    last = x.split('.')[-1]
    if last in short: return 'declaration (short name)'
    if any(m == x or m.endswith('.' + x) for m in modules): return 'module suffix'
    if any(n.endswith(x) for n in namespaces): return 'namespace suffix'
    return None
out = {}
for l in ('en', 'es'):
    added = sorted(code(new[l]) - code(old[l]))
    rows = []
    for x in added:
        r = resolves(x)
        rows.append({'token': x, 'resolves': r})
    out[l] = {'new_code_tokens': len(added), 'unresolved': [r['token'] for r in rows if not r['resolves']], 'rows': rows}
json.dump(out, open(sys.argv[1], 'w', encoding='utf-8'), indent=1, ensure_ascii=False)
for l in out: print(l, out[l]['new_code_tokens'], 'unresolved:', out[l]['unresolved'])
