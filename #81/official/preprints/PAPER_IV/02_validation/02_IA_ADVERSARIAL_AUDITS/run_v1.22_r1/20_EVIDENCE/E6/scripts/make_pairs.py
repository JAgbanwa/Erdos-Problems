"""Render the bound v1.21 PDFs page by page (90 dpi) and compose 2-up sheets for visual inspection."""
import pymupdf, pathlib
from PIL import Image
M = pathlib.Path('C:/Users/jtraverso/e81p4-publish/preprints/PAPER_IV/01_manuscript/v1.22_editorial_candidate')
O = pathlib.Path(__file__).resolve().parents[1] / 'pairs'; O.mkdir(exist_ok=True)
for lang in ('en', 'es'):
    d = pymupdf.open(M / f'PAPER_IV_preprint_v1.22_{lang}.pdf')
    imgs = []
    for p in d:
        pix = p.get_pixmap(dpi=90, alpha=False)
        imgs.append(Image.frombytes('RGB', (pix.width, pix.height), pix.samples))
    for i in range(0, len(imgs), 2):
        a = imgs[i]; b = imgs[i + 1] if i + 1 < len(imgs) else Image.new('RGB', a.size, 'white')
        s = Image.new('RGB', (a.width + b.width + 10, max(a.height, b.height)), (120, 120, 120))
        s.paste(a, (0, 0)); s.paste(b, (a.width + 10, 0))
        s.save(O / f'{lang}_{i+1:03d}-{i+2:03d}.png')
    print(lang, len(imgs))
