"""E6 (auditor-written): residual English terms in ES prose (X-15) and Model-format parity (NEW-01) in v1.22 MD/TeX/PDF. Read-only.
Excludes code spans, URLs and the reference list (cited titles must not be translated)."""
import re, json, sys, pathlib, pymupdf
M = pathlib.Path('C:/Users/jtraverso/e81p4-publish/preprints/PAPER_IV/01_manuscript/v1.22_editorial_candidate')
out = {}
md = (M / 'PAPER_IV_preprint_v1.22_es.md').read_text(encoding='utf-8').splitlines()
ref_start = next(i for i, l in enumerate(md) if re.match(r'^#+ Referencias', l))
pat = re.compile(r'\b(matchings?|packings?)\b', re.I)
hits = []
for i, l in enumerate(md[:ref_start], 1):
    s = re.sub(r'`[^`]*`', '', l); s = re.sub(r'https?://\S+', '', s)
    for m in pat.finditer(s): hits.append({'line': i, 'term': m.group(0), 'ctx': s[max(0, m.start()-60):m.end()+40]})
out['es_md_prose_hits'] = hits
tex = (M / 'PAPER_IV_preprint_v1.22_es.tex').read_text(encoding='utf-8')
tex_body = tex[:tex.find('Referencias')] if 'Referencias' in tex else tex
out['es_tex_counts'] = {t: len(re.findall(r'\b' + t + r'\b', re.sub(r'\{\ttfamily[^}]*\}', '', tex_body))) for t in ('matching', 'matchings', 'packing')}
d = pymupdf.open(M / 'PAPER_IV_preprint_v1.22_es.pdf')
pdfhits = {}
for pno, p in enumerate(d, 1):
    t = p.get_text()
    if pno >= 72: continue
    n = len(re.findall(r'\b(matchings?|packing)\b', t))
    if n: pdfhits[pno] = n
out['es_pdf_pages_with_terms_before_refs'] = pdfhits
out['es_valor_base_in_figure_page26'] = 'valor base' in d[25].get_text()
en = (M / 'PAPER_IV_preprint_v1.22_en.md').read_text(encoding='utf-8')
es = '\n'.join(md)
out['new01_en_model_code'] = 'bounded gain function from `Model`' in en
out['new01_es_model_code'] = 'ganancia acotada de `Model`' in es
out['new01_es_model_plain_line'] = [i for i, l in enumerate(md, 1) if 'ganancia acotada de Model' in l]
json.dump(out, open(sys.argv[1], 'w', encoding='utf-8'), indent=1, ensure_ascii=False)
print(json.dumps({k: v for k, v in out.items() if k != 'es_md_prose_hits'}, ensure_ascii=False, indent=1)); print(len(hits), [(h['line'], h['term']) for h in hits])
