"""E6 automated bilingual/PDF checks (auditor-written). Frozen PDFs are only read, never regenerated."""
import hashlib, json, re, collections
from pathlib import Path
import pymupdf

C = Path('C:/Users/jtraverso/e81p4-publish/preprints/PAPER_IV/01_manuscript/v1.0.1_candidate')
OUT = Path(__file__).resolve().parent
EXP = {'en': ('0c17c7303419b2c1979133479370bbb475d1febe3f0921737eb50c291caa8d10', 50),
       'es': ('84c49df8964dbe19dc3f07833fb771e31989443199bf1e4af5d9e48f9d4f5ca2', 51)}
rep = {}
(OUT / 'pages').mkdir(exist_ok=True)
for lang, (h, pages) in EXP.items():
    p = C / f'PAPER_IV_preprint_v1.0.1_{lang}.pdf'
    b = p.read_bytes()
    r = {'sha256_ok': hashlib.sha256(b).hexdigest() == h}
    d = pymupdf.open(p)
    r['pages'] = d.page_count; r['pages_ok'] = d.page_count == pages
    fonts = {}
    for i in range(d.page_count):
        for f in d.get_page_fonts(i):
            fonts[f[3]] = f[1]  # basefont -> ext ('' means not embedded)
    r['fonts'] = fonts
    r['non_embedded_fonts'] = [k for k, v in fonts.items() if v in ('', 'n/a')]
    text = [d[i].get_text() for i in range(d.page_count)]
    full = '\n'.join(text)
    r['replacement_chars'] = full.count('\ufffd')
    r['double_question'] = [(i + 1, m.start()) for i, t in enumerate(text) for m in re.finditer(r'\?\?', t)][:20]
    r['undefined_ref_markers'] = [(i + 1, s) for i, t in enumerate(text) for s in re.findall(r'\[\?\]|Missing|LaTeX Warning', t)][:20]
    r['stale_status_hits'] = [(i + 1, s) for i, t in enumerate(text) for s in re.findall(r'(?i)v0\.8|v1\.0\.2|v1\.0\.3|1\.0\.2|1\.0\.3|PASS_INTERNAL|external (?:adversarial )?review (?:has been|was) (?:completed|passed)|revisión externa (?:fue|ha sido) (?:completada|superada)', t)]
    # per-page raster for visual inspection (low dpi)
    for i in range(d.page_count):
        d[i].get_pixmap(dpi=60).save(OUT / 'pages' / f'{lang}_p{i + 1:02d}.png')
    # images with very low text (possible blank pages)
    r['near_blank_pages'] = [i + 1 for i, t in enumerate(text) if len(t.strip()) < 40]
    rep[lang] = r
    (OUT / f'pdftext_{lang}.txt').write_text(full, encoding='utf-8')

# numeric-token comparison EN vs ES (md) inside theorem/lemma/corollary statements and globally
def nums(s):
    s = s.replace('\\,', '').replace('{,}', '.')
    return collections.Counter(re.findall(r'(?<![A-Za-z])\d+(?:\.\d+)?', s))
md = {l: (C / f'PAPER_IV_preprint_v1.0.1_{l}.md').read_text(encoding='utf-8') for l in ('en', 'es')}
tex = {l: (C / f'PAPER_IV_preprint_v1.0.1_{l}.tex').read_text(encoding='utf-8') for l in ('en', 'es')}
ne, ns = nums(md['en']), nums(md['es'])
rep['md_numbers_only_in_en'] = {k: v - ns.get(k, 0) for k, v in ne.items() if v > ns.get(k, 0)}
rep['md_numbers_only_in_es'] = {k: v - ne.get(k, 0) for k, v in ns.items() if v > ne.get(k, 0)}
# display-math blocks equality EN vs ES (md): compare sequence of \[...\] blocks
def blocks(s):
    return [re.sub(r'\\text\{[^}]*\}|\\operatorname\{[^}]*\}|\\mathrm\{[^}]*\}|\s+', '', b) for b in re.findall(r'\\\[(.*?)\\\]', s, re.S)]
be, bs = blocks(md['en']), blocks(md['es'])
rep['display_math_counts'] = (len(be), len(bs))
diffs = [(i, a[:120], b[:120]) for i, (a, b) in enumerate(zip(be, bs)) if a != b]
rep['display_math_differences'] = diffs
# md vs tex numbers per language (tex has extra macros; report symmetric difference of distinctive constants)
KEY = ['16', '48', '117', '1825', '12687', '20000', '19', '365', '253', '500', '2920', '219', '1600', '87947', '44352',
       '393', '65536', '16384', '57344', '4500', '2208', '105', '59516', '191432', '59517', '10^{-16}', '10^{-12}']
def count_key(s):
    return {k: len(re.findall(r'(?<![\d.])' + re.escape(k) + r'(?![\d])', s)) for k in KEY}
rep['key_constants'] = {f'{src}_{l}': count_key(t) for src, dd in (('md', md), ('tex', tex)) for l, t in dd.items()}
# theorem/lemma headings
def heads(s):
    return re.findall(r'^#{2,4} .*$', s, re.M)
rep['heading_counts'] = {l: len(heads(md[l])) for l in md}
json.dump(rep, open(OUT / 'e6_auto.json', 'w', encoding='utf-8'), indent=1, ensure_ascii=False)
short = {l: {k: v for k, v in rep[l].items() if k != 'fonts'} for l in ('en', 'es')}
print(json.dumps(short, indent=1, ensure_ascii=False))
print('only_en', rep['md_numbers_only_in_en']); print('only_es', rep['md_numbers_only_in_es'])
print('display', rep['display_math_counts'], 'diffs', len(diffs)); [print(d_) for d_ in diffs[:15]]
print('heads', rep['heading_counts'])
kc = rep['key_constants']
for k in KEY:
    row = [kc[x][k] for x in ('md_en', 'md_es', 'tex_en', 'tex_es')]
    if len(set(row)) > 1:
        print('KEY MISMATCH', k, row)
