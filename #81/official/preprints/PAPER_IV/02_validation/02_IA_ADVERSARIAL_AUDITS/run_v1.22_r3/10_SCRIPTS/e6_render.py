"""E6 renders (auditor-written, run_v1.22_r3), read-only on inputs:
- overview/: r3 PDFs (EN 72, ES 73) as 4-up sheets at 70 dpi
- cmp/: each raster-changed page, r2 (left) | r3 (right) at 105 dpi"""
import pymupdf, pathlib, json
from PIL import Image
B = pathlib.Path('C:/Users/jtraverso/e81p4-publish/preprints/PAPER_IV/01_manuscript')
O = pathlib.Path(__file__).resolve().parents[1] / '20_EVIDENCE/E6'
D = json.load(open(O / 'E6_R3_DELTA.json', encoding='utf-8'))
img = lambda p, dpi: (lambda px: Image.frombytes('RGB', (px.width, px.height), px.samples))(p.get_pixmap(dpi=dpi, alpha=False))
for sub in ('overview', 'cmp'):
    (O / sub).mkdir(parents=True, exist_ok=True)
for lang in ('en', 'es'):
    d2 = pymupdf.open(B / f'v1.22_editorial_candidate_r2/PAPER_IV_preprint_v1.22_{lang}.pdf')
    d3 = pymupdf.open(B / f'v1.22_editorial_candidate_r3/PAPER_IV_preprint_v1.22_{lang}.pdf')
    ims = [img(p, 70) for p in d3]
    w, h = ims[0].size
    for i in range(0, len(ims), 4):
        s = Image.new('RGB', (4 * w + 30, h), (120, 120, 120))
        for k in range(4):
            if i + k < len(ims): s.paste(ims[i + k], (k * (w + 10), 0))
        s.save(O / 'overview' / f'{lang}_r3_{i+1:03d}-{min(i+4, len(ims)):03d}.png')
    for n in D[lang]['raster_changed_pages_72dpi']:
        a, b = img(d2[n - 1], 105), img(d3[n - 1], 105)
        s = Image.new('RGB', (a.width + b.width + 14, max(a.height, b.height)), (200, 40, 40)); s.paste(a, (0, 0)); s.paste(b, (a.width + 14, 0))
        s.save(O / 'cmp' / f'{lang}_p{n:03d}_r2_left_r3_right.png')
    print(lang, len(ims), D[lang]['raster_changed_pages_72dpi'])
