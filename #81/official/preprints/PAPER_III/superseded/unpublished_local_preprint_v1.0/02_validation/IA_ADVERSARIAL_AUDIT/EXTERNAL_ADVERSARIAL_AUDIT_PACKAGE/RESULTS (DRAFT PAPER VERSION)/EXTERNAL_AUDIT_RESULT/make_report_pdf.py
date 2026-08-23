r"""
Render ADVERSARIAL_AUDIT_REPORT.md to a professional PDF via reportlab platypus.
Handles: #/##/### headers, markdown tables (| ... |), **bold**, `code`, fenced
```code``` blocks, ordered/unordered lists, horizontal rules, and paragraphs.
"""
import os, re, sys
from reportlab.lib.pagesizes import A4
from reportlab.lib.units import cm
from reportlab.lib import colors
from reportlab.lib.styles import getSampleStyleSheet, ParagraphStyle
from reportlab.lib.enums import TA_LEFT
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont
from reportlab.platypus import (SimpleDocTemplate, Paragraph, Spacer, Table, TableStyle,
                                HRFlowable, Preformatted, KeepTogether)

HERE = os.path.dirname(os.path.abspath(__file__))
MD = os.path.join(HERE, 'ADVERSARIAL_AUDIT_REPORT.md')
PDF = os.path.join(HERE, 'ADVERSARIAL_AUDIT_REPORT.pdf')

# Unicode-capable fonts (Arial covers Greek/accents/math operators; Consolas for code).
WF = r'C:\Windows\Fonts'
pdfmetrics.registerFont(TTFont('U', os.path.join(WF, 'arial.ttf')))
pdfmetrics.registerFont(TTFont('U-B', os.path.join(WF, 'arialbd.ttf')))
pdfmetrics.registerFont(TTFont('U-I', os.path.join(WF, 'ariali.ttf')))
pdfmetrics.registerFont(TTFont('Mono', os.path.join(WF, 'consola.ttf')))
FN, FB, FI, FM = 'U', 'U-B', 'U-I', 'Mono'

# The 7 glyphs Arial lacks -> readable equivalents.
_TR = {'₂': '2', '₃': '3', 'ₚ': 'p', '∀': 'for all ',
       '∨': 'v', '⊇': ' superset-eq ', '⟹': ' => '}
def tr(s):
    return ''.join(_TR.get(c, c) for c in s)

styles = getSampleStyleSheet()
BODY = ParagraphStyle('body', parent=styles['Normal'], fontName=FN,
                      fontSize=9, leading=12.5, alignment=TA_LEFT, spaceAfter=5)
H1 = ParagraphStyle('h1', parent=styles['Heading1'], fontName=FB,
                    fontSize=17, leading=20, spaceBefore=6, spaceAfter=8,
                    textColor=colors.HexColor('#12233b'))
H2 = ParagraphStyle('h2', parent=styles['Heading2'], fontName=FB,
                    fontSize=12.5, leading=15, spaceBefore=12, spaceAfter=5,
                    textColor=colors.HexColor('#1b3a5b'))
H3 = ParagraphStyle('h3', parent=styles['Heading3'], fontName=FB,
                    fontSize=10.5, leading=13, spaceBefore=8, spaceAfter=3,
                    textColor=colors.HexColor('#274b6d'))
VERDICT = ParagraphStyle('verdict', parent=BODY, fontName=FB,
                         fontSize=15, leading=18, textColor=colors.HexColor('#0b6b2e'),
                         spaceBefore=4, spaceAfter=8, alignment=1)
CELL = ParagraphStyle('cell', parent=BODY, fontSize=7.6, leading=9.6, spaceAfter=0)
CELLH = ParagraphStyle('cellh', parent=CELL, fontName=FB, textColor=colors.white)
CODE = ParagraphStyle('code', parent=styles['Code'], fontName=FM,
                      fontSize=7.6, leading=9.5, backColor=colors.HexColor('#f2f4f7'),
                      borderPadding=4, spaceAfter=6)
LIST = ParagraphStyle('list', parent=BODY, leftIndent=14, spaceAfter=3)


def inline(t):
    t = t.replace('&', '&amp;').replace('<', '&lt;').replace('>', '&gt;')
    t = re.sub(r'\*\*(.+?)\*\*', rf'<font name="{FB}">\1</font>', t)
    t = re.sub(r'`(.+?)`', rf'<font face="{FM}" size="8">\1</font>', t)
    t = re.sub(r'\[(.+?)\]\((.+?)\)', r'<link href="\2" color="blue">\1</link>', t)
    return t


def parse(md):
    flow = []
    lines = md.splitlines()
    i = 0
    while i < len(lines):
        ln = lines[i]
        # fenced code
        if ln.strip().startswith('```'):
            j = i + 1; buf = []
            while j < len(lines) and not lines[j].strip().startswith('```'):
                buf.append(lines[j]); j += 1
            flow.append(Preformatted('\n'.join(buf), CODE))
            i = j + 1; continue
        # table
        if ln.strip().startswith('|') and i + 1 < len(lines) and re.match(r'^\s*\|[\s:|-]+\|\s*$', lines[i+1]):
            rows = []
            while i < len(lines) and lines[i].strip().startswith('|'):
                rows.append([c.strip() for c in lines[i].strip().strip('|').split('|')])
                i += 1
            header = rows[0]; body = rows[2:]
            data = [[Paragraph(inline(c), CELLH) for c in header]]
            for r in body:
                while len(r) < len(header): r.append('')
                data.append([Paragraph(inline(c), CELL) for c in r[:len(header)]])
            ncol = len(header)
            avail = A4[0] - 3.6*cm
            # weight columns: give more room to wide text columns
            if ncol == 4:      widths = [0.13, 0.30, 0.22, 0.35]
            elif ncol == 5:    widths = [0.08, 0.20, 0.10, 0.30, 0.32]
            elif ncol == 2:    widths = [0.30, 0.70]
            elif ncol == 3:    widths = [0.22, 0.20, 0.58]
            else:              widths = [1.0/ncol]*ncol
            t = Table(data, colWidths=[w*avail for w in widths], repeatRows=1)
            t.setStyle(TableStyle([
                ('BACKGROUND', (0, 0), (-1, 0), colors.HexColor('#1b3a5b')),
                ('GRID', (0, 0), (-1, -1), 0.4, colors.HexColor('#b9c4d0')),
                ('ROWBACKGROUNDS', (0, 1), (-1, -1), [colors.white, colors.HexColor('#eef2f6')]),
                ('VALIGN', (0, 0), (-1, -1), 'TOP'),
                ('LEFTPADDING', (0, 0), (-1, -1), 4), ('RIGHTPADDING', (0, 0), (-1, -1), 4),
                ('TOPPADDING', (0, 0), (-1, -1), 3), ('BOTTOMPADDING', (0, 0), (-1, -1), 3),
            ]))
            flow.append(Spacer(1, 3)); flow.append(t); flow.append(Spacer(1, 5))
            continue
        # headers
        if ln.startswith('# '):
            flow.append(Paragraph(inline(ln[2:]), H1)); i += 1; continue
        if ln.startswith('## '):
            flow.append(Paragraph(inline(ln[3:]), H2)); i += 1; continue
        if ln.startswith('### '):
            flow.append(Paragraph(inline(ln[4:]), H3)); i += 1; continue
        # big verdict line
        if ln.startswith('# **') or ln.strip().startswith('**PASS'):
            flow.append(Paragraph(inline(ln.lstrip('# ')), VERDICT)); i += 1; continue
        # hr
        if ln.strip() in ('---', '***', '___'):
            flow.append(Spacer(1, 2))
            flow.append(HRFlowable(width='100%', thickness=0.6, color=colors.HexColor('#9fb0c0')))
            flow.append(Spacer(1, 2)); i += 1; continue
        # list item
        m = re.match(r'^(\s*)([-*]|\d+\.)\s+(.*)$', ln)
        if m:
            bullet = '•' if m.group(2) in ('-', '*') else m.group(2)
            flow.append(Paragraph(f'{bullet}&nbsp;&nbsp;{inline(m.group(3))}', LIST))
            i += 1; continue
        # blank
        if not ln.strip():
            i += 1; continue
        # paragraph (accumulate until blank)
        buf = [ln]; j = i + 1
        while j < len(lines) and lines[j].strip() and not re.match(r'^(#|\||```|\s*[-*]\s|\s*\d+\.\s|---)', lines[j]):
            buf.append(lines[j]); j += 1
        # special: big verdict inside a paragraph
        para = ' '.join(x.strip() for x in buf)
        flow.append(Paragraph(inline(para), BODY))
        i = j
    return flow


def main():
    md = tr(open(MD, encoding='utf-8').read())
    doc = SimpleDocTemplate(PDF, pagesize=A4,
                            leftMargin=1.8*cm, rightMargin=1.8*cm,
                            topMargin=1.6*cm, bottomMargin=1.6*cm,
                            title='External Adversarial Audit Report — Paper III (v0.9.5)',
                            author='External adversarial audit (Claude, claude-fable-5)')
    def footer(canvas, d):
        canvas.saveState()
        canvas.setFont(FN, 7)
        canvas.setFillColor(colors.HexColor('#7a8a99'))
        canvas.drawString(1.8*cm, 1.0*cm,
                          'External Adversarial Audit — Paper III (Erdős #81) v0.9.5 · 2026-07-21')
        canvas.drawRightString(A4[0]-1.8*cm, 1.0*cm, f'p. {d.page}')
        canvas.restoreState()
    doc.build(parse(md), onFirstPage=footer, onLaterPages=footer)
    print('wrote', PDF, os.path.getsize(PDF), 'bytes')


if __name__ == '__main__':
    main()
