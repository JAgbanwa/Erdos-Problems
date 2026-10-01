"""E6 renders (auditor-written, run_v1.22_r2), read-only on inputs:
- pairs/: r2 ES PDF, 2-up sheets at 90 dpi (all 73 pages)
- cmp/: for each raster-changed page, r1 (left) | r2 (right) at 110 dpi, for shift inspection
- zoom/: each raster-changed r2 page alone at 140 dpi"""
import pymupdf, pathlib, json
from PIL import Image
B = pathlib.Path('C:/Users/jtraverso/e81p4-publish/preprints/PAPER_IV/01_manuscript')
O = pathlib.Path(__file__).resolve().parents[1] / '20_EVIDENCE/E6'
d1 = pymupdf.open(B / 'v1.22_editorial_candidate/PAPER_IV_preprint_v1.22_es.pdf')
d2 = pymupdf.open(B / 'v1.22_editorial_candidate_r2/PAPER_IV_preprint_v1.22_es.pdf')
img = lambda p, dpi: (lambda px: Image.frombytes('RGB', (px.width, px.height), px.samples))(p.get_pixmap(dpi=dpi, alpha=False))
for sub in ('pairs', 'cmp', 'zoom'):
    (O / sub).mkdir(parents=True, exist_ok=True)
ims = [img(p, 90) for p in d2]
for i in range(0, len(ims), 2):
    a = ims[i]; b = ims[i + 1] if i + 1 < len(ims) else Image.new('RGB', a.size, 'white')
    s = Image.new('RGB', (a.width + b.width + 10, max(a.height, b.height)), (120, 120, 120)); s.paste(a, (0, 0)); s.paste(b, (a.width + 10, 0))
    s.save(O / 'pairs' / f'es_r2_{i+1:03d}-{i+2:03d}.png')
changed = json.load(open(O / 'E6_R2_DELTA.json', encoding='utf-8'))['raster_changed_pages_72dpi']
for n in changed:
    a, b = img(d1[n - 1], 110), img(d2[n - 1], 110)
    s = Image.new('RGB', (a.width + b.width + 14, max(a.height, b.height)), (200, 40, 40)); s.paste(a, (0, 0)); s.paste(b, (a.width + 14, 0))
    s.save(O / 'cmp' / f'p{n:03d}_r1_left_r2_right.png')
    img(d2[n - 1], 140).save(O / 'zoom' / f'es_r2_p{n:03d}.png')
print('pages', len(ims), 'changed', changed)
