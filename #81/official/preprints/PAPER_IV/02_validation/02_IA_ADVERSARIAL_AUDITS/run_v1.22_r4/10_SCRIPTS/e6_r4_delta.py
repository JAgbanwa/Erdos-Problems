"""E6 (auditor-written, run_v1.22_r4): ES r3 -> r4 delta, independent of the editor's check_r4.py. Read-only.
Word-level inventory (MD, TeX), protected content, established-term check, PDF token diff, raster/page diff."""
import re, json, sys, difflib, pathlib, hashlib, pymupdf
B = pathlib.Path('C:/Users/jtraverso/e81p4-publish/preprints/PAPER_IV/01_manuscript')
R3, R4 = B / 'v1.22_editorial_candidate_r3', B / 'v1.22_editorial_candidate_r4'
rd = lambda d, x: (d / f'PAPER_IV_preprint_v1.22_es.{x}').read_text(encoding='utf-8')
out = {}
def wchanges(a, b):
    A, Bv = a.splitlines(), b.splitlines()
    if len(A) != len(Bv): return 'LINE COUNT DIFFERS', None
    ch = []
    for i, (x, y) in enumerate(zip(A, Bv), 1):
        if x == y: continue
        tx, ty = re.findall(r'\S+|\s+', x), re.findall(r'\S+|\s+', y)
        for op, i1, i2, j1, j2 in difflib.SequenceMatcher(None, tx, ty, autojunk=False).get_opcodes():
            if op != 'equal': ch.append({'line': i, 'op': op, 'old': ''.join(tx[i1:i2]), 'new': ''.join(ty[j1:j2]), 'context_new': y[max(0, y.find(''.join(ty[j1:j2])) - 80):y.find(''.join(ty[j1:j2])) + 120]})
    return sorted({c['line'] for c in ch}), ch
for x in ('md', 'tex'):
    a, b = rd(R3, x), rd(R4, x)
    out[f'{x}_line_counts'] = (len(a.splitlines()), len(b.splitlines()))
    out[f'{x}_changed_lines'], out[f'{x}_changes'] = wchanges(a, b)
a, b = rd(R3, 'md'), rd(R4, 'md')
disp = lambda t: re.findall(r'\\\[(.*?)\\\]', t, re.S); inl = lambda t: re.findall(r'\\\((.*?)\\\)', t, re.S)
code = lambda t: re.findall(r'`[^`\n]+`', t); blocks = lambda t: re.findall(r'```.*?```', t, re.S)
tags = lambda t: re.findall(r'\\tag\{[^}]*\}', t); heads = lambda t: [l for l in t.splitlines() if l.startswith('#')]
leads = lambda t: re.findall(r'(?m)^\*\*[^*]+\*\*', t); rows = lambda t: [l for l in t.splitlines() if l.startswith('|')]
imgs = lambda t: re.findall(r'!\[[^\]]*\]\([^)]*\)', t)
refs = lambda t: t[t.find('# Referencias'):]
out['protected'] = {'displays': disp(a) == disp(b), 'inline_math': inl(a) == inl(b), 'code_spans': code(a) == code(b), 'code_blocks': blocks(a) == blocks(b),
                    'tags': tags(a) == tags(b), 'headings': heads(a) == heads(b), 'bold_leads': leads(a) == leads(b), 'table_rows': rows(a) == rows(b),
                    'images': imgs(a) == imgs(b), 'references': refs(a) == refs(b)}
out['tex_preamble_equal'] = (lambda s, t: s[:s.find('\\begin{document}')] == t[:t.find('\\begin{document}')])(rd(R3, 'tex'), rd(R4, 'tex'))
cnt = lambda t, p: len(re.findall(p, t))
out['terms_r3_r4'] = {k: (cnt(a, p), cnt(b, p)) for k, p in [('programación numérica', r'programación numérica'), ('calendario numérico', r'calendario numérico'), ('Un calendario explícito', r'Un calendario explícito'),
    ('muestra fijada', r'muestra fijada'), ('muestras con anclajes', r'muestras con anclajes'), ('Cota de muestra con anclajes', r'Cota de muestra con anclajes')]}
out['established_term_sites_r4'] = {t: [i + 1 for i, l in enumerate(b.splitlines()) if t in l] for t in ('calendario numérico', 'calendario explícito', 'muestras con anclajes', 'muestra con anclajes')}
def ptxt(p): return [pg.get_text() for pg in pymupdf.open(p)]
p3, p4 = ptxt(R3 / 'PAPER_IV_preprint_v1.22_es.pdf'), ptxt(R4 / 'PAPER_IV_preprint_v1.22_es.pdf')
out['pdf_pages'] = (len(p3), len(p4))
def toks(pages):
    t = []
    for pg in pages:
        s = '\n'.join(l for l in pg.splitlines() if not re.fullmatch(r'\s*\d+\s*', l)); s = re.sub(r'(\w)-\n(\w)', r'\1\2', s); t += s.split()
    return t
w3, w4 = toks(p3), toks(p4)
out['pdf_token_diffs'] = [(op, ' '.join(w3[max(0, i1 - 5):i2 + 5]), ' '.join(w4[max(0, j1 - 5):j2 + 5])) for op, i1, i2, j1, j2 in difflib.SequenceMatcher(None, w3, w4, autojunk=False).get_opcodes() if op != 'equal']
d3, d4 = pymupdf.open(R3 / 'PAPER_IV_preprint_v1.22_es.pdf'), pymupdf.open(R4 / 'PAPER_IV_preprint_v1.22_es.pdf')
out['raster_changed_pages_72dpi'] = [i + 1 for i in range(min(len(d3), len(d4))) if hashlib.sha256(d3[i].get_pixmap(dpi=72, alpha=False).samples).hexdigest() != hashlib.sha256(d4[i].get_pixmap(dpi=72, alpha=False).samples).hexdigest()]
out['page_first_last_lines_equal'] = {i + 1: (p3[i].strip().splitlines()[:1] == p4[i].strip().splitlines()[:1] and p3[i].strip().splitlines()[-2:] == p4[i].strip().splitlines()[-2:]) for i in out['raster_changed_pages_72dpi']}
out['pdf_metadata_r4'] = {k: d4.metadata.get(k) for k in ('producer', 'creator', 'creationDate')}
ed = (R4 / 'CHANGES_es.diff').read_text(encoding='utf-8')
mine = ''.join(difflib.unified_diff(a.splitlines(True), b.splitlines(True)))
out['editor_diff_body_equals_auditor'] = [l for l in ed.splitlines()[2:]] == [l for l in mine.splitlines()[2:]]
json.dump(out, open(sys.argv[1], 'w', encoding='utf-8'), indent=1, ensure_ascii=False)
pathlib.Path(sys.argv[1]).with_name('auditor_diff_es_md.diff').write_text(mine, encoding='utf-8')
print(json.dumps(out, indent=1, ensure_ascii=False))
