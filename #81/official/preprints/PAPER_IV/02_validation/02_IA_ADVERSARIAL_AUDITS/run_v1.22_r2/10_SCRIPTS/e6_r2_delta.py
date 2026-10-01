"""E6 (auditor-written, run_v1.22_r2): independent check of the ES r1 -> r2 delta. Read-only.
1) word-level change inventory for MD and TeX; 2) protected content identical (displays, inline math, code spans/blocks,
tags, heading/lead lines, reference list); 3) residual English terms in prose; 4) Model formatting;
5) PDF corresponds to the corrected TeX: r2 PDF body text == r1 PDF body text after applying exactly the inventoried
substitutions, references identical; 6) raster comparison of r1 vs r2 PDF pages; 7) count reconciliation."""
import re, json, sys, difflib, pathlib, hashlib, pymupdf
B = pathlib.Path('C:/Users/jtraverso/e81p4-publish/preprints/PAPER_IV/01_manuscript')
R1, R2 = B / 'v1.22_editorial_candidate', B / 'v1.22_editorial_candidate_r2'
rd = lambda d, x: (d / f'PAPER_IV_preprint_v1.22_es.{x}').read_text(encoding='utf-8')
out = {}


def word_changes(a, b):
    A, Bv = a.splitlines(), b.splitlines()
    if len(A) != len(Bv):
        return None
    ch = []
    for i, (x, y) in enumerate(zip(A, Bv), 1):
        if x == y:
            continue
        tx, ty = re.findall(r'\S+|\s+', x), re.findall(r'\S+|\s+', y)
        for op, i1, i2, j1, j2 in difflib.SequenceMatcher(None, tx, ty, autojunk=False).get_opcodes():
            if op != 'equal':
                ch.append({'line': i, 'op': op, 'old': ''.join(tx[i1:i2]), 'new': ''.join(ty[j1:j2])})
    return ch


for x in ('md', 'tex'):
    a, b = rd(R1, x), rd(R2, x)
    wc = word_changes(a, b)
    out[f'{x}_line_counts'] = (len(a.splitlines()), len(b.splitlines()))
    out[f'{x}_changed_lines'] = sorted({c['line'] for c in wc}) if wc is not None else 'LINE COUNT DIFFERS'
    out[f'{x}_word_changes'] = wc
    out[f'{x}_n_word_changes'] = len(wc) if wc is not None else None

a, b = rd(R1, 'md'), rd(R2, 'md')
disp = lambda t: re.findall(r'\\\[(.*?)\\\]', t, re.S)
inl = lambda t: re.findall(r'\\\((.*?)\\\)', t, re.S)
code = lambda t: re.findall(r'`[^`\n]+`', t)
blocks = lambda t: re.findall(r'```.*?```', t, re.S)
tags = lambda t: re.findall(r'\\tag\{[^}]*\}', t)
heads = lambda t: [l for l in t.splitlines() if l.startswith('#') or re.match(r'^\*\*[^*]+\*\*', l)]


def refs(t):
    k = t.find('# Referencias')
    return t[k:] if k >= 0 else None


ca, cb = code(a), code(b)
out['protected_md'] = {
    'displays_equal': disp(a) == disp(b), 'n_displays': len(disp(b)),
    'inline_math_equal': inl(a) == inl(b), 'n_inline_math': len(inl(b)),
    'code_blocks_equal': blocks(a) == blocks(b), 'n_code_blocks': len(blocks(b)),
    'tags_equal': tags(a) == tags(b), 'n_tags': len(tags(b)),
    'heading_and_bold_lead_lines_equal': heads(a) == heads(b), 'n_heading_lines': len(heads(b)),
    'references_section_equal': refs(a) is not None and refs(a) == refs(b),
    'code_span_count_r1_r2': (len(ca), len(cb)),
    'code_spans_removed': sorted(set(ca) - set(cb)),
    'code_spans_with_increased_count': sorted({c for c in cb if cb.count(c) > ca.count(c)}),
}
out['md_substitution_pairs'] = sorted({(c['old'].strip(), c['new'].strip()) for c in out['md_word_changes']})
out['tex_substitution_pairs'] = sorted({(c['old'].strip(), c['new'].strip()) for c in out['tex_word_changes']}) if out['tex_word_changes'] is not None else None

# residuals and count reconciliation
L, L1 = b.splitlines(), a.splitlines()
rs = next(i for i, l in enumerate(L) if re.match(r'^#+ Referencias', l))
rs1 = next(i for i, l in enumerate(L1) if re.match(r'^#+ Referencias', l))
strip = lambda l: re.sub(r'https?://\S+', '', re.sub(r'`[^`]*`', '', l))
out['r2_prose_residuals_md'] = [(i, m.group(0)) for i, l in enumerate(L[:rs], 1) for m in re.finditer(r'\b(matchings?|packings?|baseline)\b', strip(l), re.I)]
out['r2_all_occurrences_md'] = [(i, m.group(0), 'reference list' if i > rs else 'body') for i, l in enumerate(L, 1) for m in re.finditer(r'\b(matchings?|packings?)\b', l, re.I)]
out['r1_prose_occurrences_md'] = [(i, m.group(0)) for i, l in enumerate(L1[:rs1], 1) for m in re.finditer(r'\b(matchings?|packings?)\b', strip(l), re.I)]
out['r1_prose_counts'] = {'matching(s)': sum(1 for _, w in out['r1_prose_occurrences_md'] if w.lower().startswith('matching')),
                          'packing': sum(1 for _, w in out['r1_prose_occurrences_md'] if w.lower().startswith('packing'))}
out['r1_reference_occurrences_md'] = [(i, m.group(0)) for i, l in enumerate(L1, 1) if i > rs1 for m in re.finditer(r'\b(matchings?|packings?)\b', l, re.I)]
out['model_es_md'] = {'r2_has_code_Model': 'ganancia acotada de `Model`' in b, 'r2_plain_Model_left': 'ganancia acotada de Model' in b}
t2 = rd(R2, 'tex')
out['model_es_tex_monospace'] = bool(re.search(r'ganancia acotada de \{\\ttfamily\\small Model\}', t2))


# PDF corresponds to TeX
def ptxt(p):
    return [pg.get_text() for pg in pymupdf.open(p)]


p1, p2 = ptxt(R1 / 'PAPER_IV_preprint_v1.22_es.pdf'), ptxt(R2 / 'PAPER_IV_preprint_v1.22_es.pdf')
out['pdf_pages_r1_r2'] = (len(p1), len(p2))
norm = lambda s: re.sub(r'\s+', '', s)
# word tokens; a line-final hyphen is joined to the next token (TeX hyphenation), page-number lines dropped
def toks(pages):
    t = []
    for pg in pages:
        lines = [l for l in pg.splitlines() if not re.fullmatch(r'\s*\d+\s*', l)]
        s = '\n'.join(lines)
        s = re.sub(r'(\w)-\n(\w)', r'\1\2', s)
        t += s.split()
    return t
w1, w2 = toks(p1), toks(p2)
def ref_start(w):
    return max(i for i, x in enumerate(w) if x == 'Referencias')
k1, k2 = ref_start(w1), ref_start(w2)
SUBS = {'matchings': 'emparejamientos', 'matching': 'emparejamiento'}
b1 = [re.sub(r'^(matchings?)', lambda m: SUBS[m.group(1)], x) for x in w1[:k1]]
for i in range(1, len(b1)):
    if b1[i - 1] == 'otro' and b1[i].startswith('packing'):
        b1[i] = b1[i].replace('packing', 'empaquetamiento', 1)
b2 = w2[:k2]
# allow the hyphenation join to differ: compare after removing remaining hyphens inside tokens only for diff reporting
sm = difflib.SequenceMatcher(None, b1, b2, autojunk=False)
diffs = [(op, ' '.join(b1[max(0, i1 - 6):i2 + 6]), ' '.join(b2[max(0, q1 - 6):q2 + 6])) for op, i1, i2, q1, q2 in sm.get_opcodes() if op != 'equal']
out['pdf_body_tokens_r1_r2'] = (len(b1), len(b2))
out['pdf_body_equal_after_inventoried_substitutions'] = not diffs
out['pdf_body_diffs'] = diffs[:40]
out['pdf_body_n_diffs'] = len(diffs)
out['pdf_reference_section_equal'] = w1[k1:] == w2[k2:]
out['pdf_body_pages_with_residual_terms'] = {i + 1: len(re.findall(r'\b(matchings?|packing)\b', t)) for i, t in enumerate(p2[:71]) if re.search(r'\b(matchings?|packing)\b', t)}
d2 = pymupdf.open(R2 / 'PAPER_IV_preprint_v1.22_es.pdf')
out['pdf_metadata_r2'] = {k: d2.metadata.get(k) for k in ('producer', 'creator', 'creationDate', 'modDate')}
for i, pg in enumerate(d2):
    if 'ganancia acotada de' in pg.get_text():
        out['pdf_model_spans'] = {'page': i + 1, 'spans': [(sp['text'], sp['font']) for blk in pg.get_text('dict')['blocks'] for ln in blk.get('lines', []) for sp in ln['spans'] if 'Model' in sp['text']]}
# raster and text page comparison
r1d = pymupdf.open(R1 / 'PAPER_IV_preprint_v1.22_es.pdf')
changed = []
for i in range(min(len(r1d), len(d2))):
    ha = hashlib.sha256(r1d[i].get_pixmap(dpi=72, alpha=False).samples).hexdigest()
    hb = hashlib.sha256(d2[i].get_pixmap(dpi=72, alpha=False).samples).hexdigest()
    if ha != hb:
        changed.append(i + 1)
out['raster_changed_pages_72dpi'] = changed
out['text_changed_pages'] = [i + 1 for i in range(min(len(p1), len(p2))) if norm(p1[i]) != norm(p2[i])]
json.dump(out, open(sys.argv[1], 'w', encoding='utf-8'), indent=1, ensure_ascii=False)
s = {k: v for k, v in out.items() if k not in ('md_word_changes', 'tex_word_changes', 'pdf_body_diffs', 'tex_substitution_pairs')}
print(json.dumps(s, indent=1, ensure_ascii=False))
print('pdf_body_diffs', json.dumps(out.get('pdf_body_diffs', [])[:10], ensure_ascii=False))
print('tex pairs', out['tex_substitution_pairs'])
