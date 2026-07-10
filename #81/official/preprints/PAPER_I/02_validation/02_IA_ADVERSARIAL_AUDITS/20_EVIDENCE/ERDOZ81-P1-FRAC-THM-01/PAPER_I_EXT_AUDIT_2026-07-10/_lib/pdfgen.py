"""
pdfgen.py — minimal Markdown-subset -> PDF renderer (reportlab).

Supports: # / ## / ### headings, paragraphs, - and * bullet lists, fenced ```code```
blocks, and simple GitHub pipe tables. Enough for audit reports. English output.
No external LaTeX needed (pdflatex is unavailable in this environment).
"""
from __future__ import annotations
import re
from reportlab.lib.pagesizes import letter
from reportlab.lib.units import cm
from reportlab.lib import colors
from reportlab.lib.styles import getSampleStyleSheet, ParagraphStyle
from reportlab.platypus import (SimpleDocTemplate, Paragraph, Spacer, Preformatted,
                                Table, TableStyle, ListFlowable, ListItem)
from reportlab.lib.enums import TA_LEFT

_ss = getSampleStyleSheet()
STY = {
    "h1": ParagraphStyle("h1", parent=_ss["Heading1"], fontSize=16, spaceBefore=10, spaceAfter=6),
    "h2": ParagraphStyle("h2", parent=_ss["Heading2"], fontSize=13, spaceBefore=8, spaceAfter=4),
    "h3": ParagraphStyle("h3", parent=_ss["Heading3"], fontSize=11, spaceBefore=6, spaceAfter=3),
    "body": ParagraphStyle("body", parent=_ss["BodyText"], fontSize=9.5, leading=13, alignment=TA_LEFT),
    "code": ParagraphStyle("code", parent=_ss["Code"], fontSize=8, leading=10),
    "cell": ParagraphStyle("cell", parent=_ss["BodyText"], fontSize=8, leading=10),
    "cellb": ParagraphStyle("cellb", parent=_ss["BodyText"], fontSize=8, leading=10, fontName="Helvetica-Bold"),
}

def _inline(text):
    # escape XML, then apply **bold**, `code`, and keep math-ish text literal
    text = (text.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;"))
    text = re.sub(r"\*\*(.+?)\*\*", r"<b>\1</b>", text)
    text = re.sub(r"`(.+?)`", r'<font face="Courier">\1</font>', text)
    return text

def _flush_table(rows, story):
    if not rows:
        return
    ncol = len(rows[0])
    def norm(r):
        r = list(r)
        if len(r) < ncol: r = r + [""] * (ncol - len(r))
        elif len(r) > ncol: r = r[:ncol - 1] + [" | ".join(r[ncol - 1:])]
        return r
    header, body = norm(rows[0]), [norm(r) for r in rows[1:]]
    data = [[Paragraph(_inline(c), STY["cellb"]) for c in header]]
    for r in body:
        data.append([Paragraph(_inline(c), STY["cell"]) for c in r])
    t = Table(data, colWidths=[ (17.0/ncol)*cm ] * ncol, repeatRows=1)
    t.setStyle(TableStyle([
        ("GRID", (0, 0), (-1, -1), 0.4, colors.grey),
        ("BACKGROUND", (0, 0), (-1, 0), colors.HexColor("#e8e8e8")),
        ("VALIGN", (0, 0), (-1, -1), "TOP"),
        ("LEFTPADDING", (0, 0), (-1, -1), 3),
        ("RIGHTPADDING", (0, 0), (-1, -1), 3),
        ("TOPPADDING", (0, 0), (-1, -1), 2),
        ("BOTTOMPADDING", (0, 0), (-1, -1), 2),
    ]))
    story.append(t); story.append(Spacer(1, 6))

def md_to_pdf(md_text, out_path, title=None):
    story = []
    if title:
        story.append(Paragraph(_inline(title), STY["h1"]))
        story.append(Spacer(1, 4))
    lines = md_text.splitlines()
    i = 0
    bullets = []
    table_rows = []

    def flush_bullets():
        nonlocal bullets
        if bullets:
            items = [ListItem(Paragraph(_inline(b), STY["body"]), leftIndent=10) for b in bullets]
            story.append(ListFlowable(items, bulletType="bullet", start="•"))
            story.append(Spacer(1, 4))
            bullets = []

    while i < len(lines):
        ln = lines[i]
        if ln.strip().startswith("```"):
            flush_bullets(); _flush_table(table_rows, story); table_rows = []
            i += 1
            code = []
            while i < len(lines) and not lines[i].strip().startswith("```"):
                code.append(lines[i]); i += 1
            i += 1
            story.append(Preformatted("\n".join(code), STY["code"]))
            story.append(Spacer(1, 4))
            continue
        # pipe table? (split ONLY on space-padded pipes so literal |E|, |E(R)|,
        # |n1-n2| inside cells are preserved)
        if "|" in ln and ln.strip().startswith("|"):
            if re.match(r"^[\s:|-]+$", ln.strip()):   # separator row
                i += 1; continue
            inner = ln.strip()
            if inner.startswith("|"): inner = inner[1:]
            if inner.endswith("|"):   inner = inner[:-1]
            cells = [c.strip() for c in re.split(r"\s\|\s", inner)]
            table_rows.append(cells); i += 1; continue
        else:
            _flush_table(table_rows, story); table_rows = []
        if ln.startswith("### "):
            flush_bullets(); story.append(Paragraph(_inline(ln[4:]), STY["h3"]))
        elif ln.startswith("## "):
            flush_bullets(); story.append(Paragraph(_inline(ln[3:]), STY["h2"]))
        elif ln.startswith("# "):
            flush_bullets(); story.append(Paragraph(_inline(ln[2:]), STY["h1"]))
        elif re.match(r"^\s*[-*]\s+", ln):
            bullets.append(re.sub(r"^\s*[-*]\s+", "", ln))
        elif ln.strip() == "":
            flush_bullets(); story.append(Spacer(1, 4))
        elif set(ln.strip()) <= {"-", "="} and len(ln.strip()) >= 3:
            pass  # horizontal rule / setext underline -> skip
        else:
            flush_bullets(); story.append(Paragraph(_inline(ln), STY["body"]))
        i += 1
    flush_bullets(); _flush_table(table_rows, story)

    doc = SimpleDocTemplate(out_path, pagesize=letter,
                            leftMargin=2*cm, rightMargin=2*cm,
                            topMargin=2*cm, bottomMargin=2*cm,
                            title=title or "report")
    doc.build(story)
    return out_path

if __name__ == "__main__":
    import sys
    src, dst = sys.argv[1], sys.argv[2]
    ttl = sys.argv[3] if len(sys.a