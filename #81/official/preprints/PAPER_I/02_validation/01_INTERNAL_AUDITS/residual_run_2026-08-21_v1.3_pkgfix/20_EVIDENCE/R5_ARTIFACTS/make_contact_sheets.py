from pathlib import Path
from PIL import Image, ImageDraw


def make(source: Path, output: Path, label: str) -> None:
    pages = sorted(source.glob("page-*.png"))
    cols = 5
    thumb_w = 190
    thumb_h = 270
    cell_w = 210
    cell_h = 300
    rows = (len(pages) + cols - 1) // cols
    sheet = Image.new("RGB", (cols * cell_w, rows * cell_h), "white")
    draw = ImageDraw.Draw(sheet)
    for i, page in enumerate(pages):
        image = Image.open(page).convert("RGB")
        image.thumbnail((thumb_w, thumb_h))
        x = (i % cols) * cell_w + (cell_w - image.width) // 2
        y = (i // cols) * cell_h + 20
        sheet.paste(image, (x, y))
        draw.text((x, 3 + (i // cols) * cell_h), f"{label} {i + 1}", fill="black")
    sheet.save(output, quality=92)


if __name__ == "__main__":
    base = Path(__file__).resolve().parent / "results" / "renders"
    make(base / "en", base / "contact_en.jpg", "EN")
    make(base / "es", base / "contact_es.jpg", "ES")

