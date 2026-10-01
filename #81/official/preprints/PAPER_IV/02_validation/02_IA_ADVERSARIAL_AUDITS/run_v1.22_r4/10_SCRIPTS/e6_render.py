"""E6 renders (auditor-written, run_v1.22_r4): r3|r4 side-by-side at 130 dpi for the raster-changed ES pages, and
140 dpi crops of the changed paragraph (located by text search in the r4 PDF)."""
import pymupdf, pathlib, json
from PIL import Image
B = pathlib.Path('C:/Users/jtraverso/e81p4-publish/preprints/PAPER_IV/01_manuscript')
O = pathlib.Path(__file__).resolve().parents[1] / '20_EVIDENCE/E6'; (O / 'cmp').mkdir(exist_ok=True); (O / 'zoom').mkdir(exist_ok=True)
d3 = pymupdf.open(B / 'v1.22_editorial_candidate_r3/PAPER_IV_preprint_v1.22_es.pdf'); d4 = pymupdf.open(B / 'v1.22_editorial_candidate_r4/PAPER_IV_preprint_v1.22_es.pdf')
img = lambda p, dpi, clip=None: (lambda px: Image.frombytes('RGB', (px.width, px.height), px.samples))(p.get_pixmap(dpi=dpi, alpha=False, clip=clip))
for n, key in [(40, 'calendario numérico'), (66, 'muestras con anclajes')]:
    a, b = img(d3[n - 1], 130), img(d4[n - 1], 130)
    s = Image.new('RGB', (a.width + b.width + 14, max(a.height, b.height)), (200, 40, 40)); s.paste(a, (0, 0)); s.paste(b, (a.width + 14, 0)); s.save(O / 'cmp' / f'es_p{n:03d}_r3_left_r4_right.png')
    hits = d4[n - 1].search_for(key)
    r = hits[0]; clip = pymupdf.Rect(40, r.y0 - 120, d4[n - 1].rect.width - 40, r.y1 + 80)
    img(d4[n - 1], 160, clip).save(O / 'zoom' / f'es_r4_p{n:03d}_changed_paragraph.png')
    print(n, key, len(hits))
