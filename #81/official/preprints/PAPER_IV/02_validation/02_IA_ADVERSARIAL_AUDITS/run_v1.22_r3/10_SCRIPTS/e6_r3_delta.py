"""E6 (auditor-written, run_v1.22_r3): independent check of the r2 -> r3 delta in EN and ES. Read-only.
- paragraph-level change inventory (MD) with full before/after text
- protected content identical: displays, inline math, code blocks, tags, heading/lead lines, table rows, reference list, image refs
- code spans added/removed
- PDF correspondence: r3 PDF text equals r2 PDF text outside the changed paragraphs (token diff limited to changed regions)
- raster/text changed pages (72 dpi), page counts
- editor CHANGES_*.diff == auditor-regenerated unified diff"""
import re, json, sys, difflib, pathlib, hashlib, pymupdf
B = pathlib.Path('C:/Users/jtraverso/e81p4-publish/preprints/PAPER_IV/01_manuscript')
R2, R3 = B / 'v1.22_editorial_candidate_r2', B / 'v1.22_editorial_candidate_r3'
out = {}
disp = lambda t: re.findall(r'\\\[(.*?)\\\]', t, re.S)
inl = lambda t: re.findall(r'\\\((.*?)\\\)', t, re.S)
code = lambda t: re.findall(r'`[^`\n]+`', t)
blocks = lambda t: re.findall(r'```.*?```', t, re.S)
tags = lambda t: re.findall(r'\\tag\{[^}]*\}', t)
heads = lambda t: [l for l in t.splitlines() if l.startswith('#')]
leads = lambda t: [re.match(r'^\*\*[^*]+\*\*', l).group(0) for l in t.splitlines() if re.match(r'^\*\*[^*]+\*\*', l)]
rows = lambda t: [l for l in t.splitlines() if l.startswith('|')]
imgs = lambda t: re.findall(r'!\[[^\]]*\]\([^)]*\)', t)
def refs(t, lang):
    k = t.find('# Referencias' if lang == 'es' else '# References')
    return t[k:] if k >= 0 else None
def paras(t):
    return [p for p in re.split(r'\n\s*\n', t)]
for lang in ('en', 'es'):
    a = (R2 / f'PAPER_IV_preprint_v1.22_{lang}.md').read_text(encoding='utf-8')
    b = (R3 / f'PAPER_IV_preprint_v1.22_{lang}.md').read_text(encoding='utf-8')
    o = {}
    pa, pb = paras(a), paras(b)
    sm = difflib.SequenceMatcher(None, pa, pb, autojunk=False)
    ch = []
    for op, i1, i2, j1, j2 in sm.get_opcodes():
        if op != 'equal':
            ch.append({'op': op, 'r2': pa[i1:i2], 'r3': pb[j1:j2], 'r2_para_index': [i1, i2], 'r3_para_index': [j1, j2]})
    o['n_paragraphs_r2_r3'] = (len(pa), len(pb))
    o['changed_paragraph_groups'] = len(ch)
    o['changed'] = ch
    ca, cb = code(a), code(b)
    o['protected'] = {
        'displays_equal': disp(a) == disp(b), 'n_displays': len(disp(b)),
        'inline_math_equal': inl(a) == inl(b), 'n_inline': len(inl(b)),
        'code_blocks_equal': blocks(a) == blocks(b), 'tags_equal': tags(a) == tags(b), 'n_tags': len(tags(b)),
        'headings_equal': heads(a) == heads(b), 'bold_leads_equal': leads(a) == leads(b),
        'table_rows_equal': rows(a) == rows(b), 'n_table_rows': len(rows(b)),
        'images_equal': imgs(a) == imgs(b), 'references_equal': refs(a, lang) is not None and refs(a, lang) == refs(b, lang),
        'inline_math_inside_changed_paragraphs_r2': sum(len(inl('\n'.join(c['r2']))) for c in ch),
        'inline_math_inside_changed_paragraphs_r3': sum(len(inl('\n'.join(c['r3']))) for c in ch),
        'code_spans_removed': sorted(set(ca) - set(cb)), 'code_spans_added': sorted(set(cb) - set(ca)),
        'code_span_count': (len(ca), len(cb)),
    }
    mine = ''.join(difflib.unified_diff(a.splitlines(True), b.splitlines(True), fromfile=f'v1.22-r2/{lang}.md', tofile=f'v1.22-r3/{lang}.md'))
    ed = (R3 / f'CHANGES_{lang}.diff').read_text(encoding='utf-8')
    o['editor_diff_equals_auditor_diff'] = mine == ed
    if mine != ed:
        o['editor_diff_len'], o['auditor_diff_len'] = len(ed), len(mine)
    pathlib.Path(sys.argv[2]).joinpath(f'auditor_diff_{lang}_md.diff').write_text(mine, encoding='utf-8')
    ta = (R2 / f'PAPER_IV_preprint_v1.22_{lang}.tex').read_text(encoding='utf-8')
    tb = (R3 / f'PAPER_IV_preprint_v1.22_{lang}.tex').read_text(encoding='utf-8')
    pathlib.Path(sys.argv[2]).joinpath(f'auditor_diff_{lang}_tex.diff').write_text(''.join(difflib.unified_diff(ta.splitlines(True), tb.splitlines(True))), encoding='utf-8')
    o['tex_preamble_equal'] = ta[:ta.find('\\begin{document}')] == tb[:tb.find('\\begin{document}')]
    o['tex_changed_line_count'] = sum(1 for l in difflib.unified_diff(ta.splitlines(), tb.splitlines(), n=0) if l.startswith(('+', '-')) and not l.startswith(('+++', '---')))
    o['tex_displays_equal'] = disp(ta) == disp(tb)
    o['tex_equation_envs_equal'] = re.findall(r'\\begin\{(equation|align|gather)\*?\}.*?\\end\{\1\*?\}', ta, re.S) == re.findall(r'\\begin\{(equation|align|gather)\*?\}.*?\\end\{\1\*?\}', tb, re.S)
    # PDF
    d2 = pymupdf.open(R2 / f'PAPER_IV_preprint_v1.22_{lang}.pdf'); d3 = pymupdf.open(R3 / f'PAPER_IV_preprint_v1.22_{lang}.pdf')
    o['pdf_pages'] = (len(d2), len(d3))
    o['pdf_metadata_r3'] = {k: d3.metadata.get(k) for k in ('producer', 'creator', 'creationDate')}
    rc = []
    for i in range(min(len(d2), len(d3))):
        if hashlib.sha256(d2[i].get_pixmap(dpi=72, alpha=False).samples).hexdigest() != hashlib.sha256(d3[i].get_pixmap(dpi=72, alpha=False).samples).hexdigest():
            rc.append(i + 1)
    o['raster_changed_pages_72dpi'] = rc
    def toks(d):
        t = []
        for pg in d:
            s = '\n'.join(l for l in pg.get_text().splitlines() if not re.fullmatch(r'\s*\d+\s*', l))
            s = re.sub(r'(\w)-\n(\w)', r'\1\2', s); t += s.split()
        return t
    w2, w3 = toks(d2), toks(d3)
    smt = difflib.SequenceMatcher(None, w2, w3, autojunk=False)
    regions = [(op, ' '.join(w2[i1:i2]), ' '.join(w3[j1:j2])) for op, i1, i2, j1, j2 in smt.get_opcodes() if op != 'equal']
    o['pdf_token_diff_regions'] = len(regions)
    o['pdf_token_diff_r3_text_total_tokens'] = sum(len(r[2].split()) for r in regions)
    # each PDF diff region's r3 text must come from a changed MD paragraph (by token overlap), else flag
    chtext = ' '.join(' '.join(c['r3']) for c in ch)
    chtok = set(re.findall(r'\w+', chtext.lower()))
    stray = []
    for op, x, y in regions:
        yt = set(re.findall(r'\w+', y.lower())); xt = set(re.findall(r'\w+', x.lower()))
        prev = ' '.join(' '.join(c['r2']) for c in ch); prevtok = set(re.findall(r'\w+', prev.lower()))
        if (yt and len(yt - chtok) > 2) or (xt and len(xt - prevtok) > 2):
            stray.append((op, x[:200], y[:200]))
    o['pdf_diff_regions_not_explained_by_changed_paragraphs'] = stray
    out[lang] = o
json.dump(out, open(pathlib.Path(sys.argv[2]) / sys.argv[1], 'w', encoding='utf-8'), indent=1, ensure_ascii=False)
for lang in out:
    o = out[lang]
    print(lang, json.dumps({k: v for k, v in o.items() if k not in ('changed',)}, ensure_ascii=False, indent=1)[:3500])
