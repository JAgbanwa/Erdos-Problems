"""Render Markdown reports to HTML->PDF (PyMuPDF Story) and the final report to LaTeX.
Minimal Markdown subset: headings, paragraphs, bullet/numbered lists, pipe tables, fenced code, **bold**,
*italic*, `code`. No TeX engine is available on this machine; the PDFs are therefore NOT compiled from TeX."""
import html, re, sys
from pathlib import Path
import pymupdf

RUN = Path(__file__).resolve().parents[1]


def inline(s):
    s = html.escape(s, quote=False)
    s = re.sub(r'`([^`]+)`', r'<code>\1</code>', s)
    s = re.sub(r'\*\*([^*]+)\*\*', r'<b>\1</b>', s)
    s = re.sub(r'(?<![*\w])\*([^*\n]+)\*(?![*\w])', r'<i>\1</i>', s)
    return s


def md_to_html(md):
    out, lines, i = [], md.splitlines(), 0
    para = []
    def flush():
        if para:
            out.append('<p>' + inline(' '.join(para)) + '</p>'); para.clear()
    while i < len(lines):
        l = lines[i]
        if l.startswith('```'):
            flush(); j = i + 1; buf = []
            while j < len(lines) and not lines[j].startswith('```'):
                buf.append(lines[j]); j += 1
            out.append('<pre>' + html.escape('\n'.join(buf)) + '</pre>'); i = j + 1; continue
        m = re.match(r'^(#{1,4}) (.*)$', l)
        if m:
            flush(); lv = len(m.group(1)); out.append(f'<h{lv}>{inline(m.group(2))}</h{lv}>'); i += 1; continue
        if l.startswith('|'):
            flush(); rows = []
            while i < len(lines) and lines[i].startswith('|'):
                rows.append(lines[i]); i += 1
            cells = [[c.strip() for c in r.strip().strip('|').split('|')] for r in rows]
            body = [r for r in cells if not all(re.fullmatch(r':?-{2,}:?', c or '--') for c in r)]
            t = '<table>'
            for k, r in enumerate(body):
                tag = 'th' if k == 0 else 'td'
                t += '<tr>' + ''.join(f'<{tag}>{inline(c)}</{tag}>' for c in r) + '</tr>'
            out.append(t + '</table>'); continue
        if re.match(r'^\s*[*-] ', l) or re.match(r'^\s*\d+\. ', l):
            flush(); ordered = bool(re.match(r'^\s*\d+\. ', l)); items = []
            while i < len(lines) and (re.match(r'^\s*[*-] ', lines[i]) or re.match(r'^\s*\d+\. ', lines[i]) or (lines[i].startswith('  ') and items)):
                if re.match(r'^\s*([*-]|\d+\.) ', lines[i]):
                    items.append(re.sub(r'^\s*([*-]|\d+\.) ', '', lines[i]))
                else:
                    items[-1] += ' ' + lines[i].strip()
                i += 1
            tg = 'ol' if ordered else 'ul'
            out.append(f'<{tg}>' + ''.join(f'<li>{inline(x)}</li>' for x in items) + f'</{tg}>'); continue
        if not l.strip():
            flush(); i += 1; continue
        para.append(l.strip()); i += 1
    flush()
    return '\n'.join(out)


CSS = """
body { font-family: sans-serif; font-size: 9pt; line-height: 1.3; }
h1 { font-size: 15pt; } h2 { font-size: 12pt; margin-top: 10pt; } h3 { font-size: 10.5pt; }
code, pre { font-family: monospace; font-size: 8pt; }
table { border-collapse: collapse; margin: 4pt 0; }
th, td { border: 0.5pt solid #888; padding: 2pt 3pt; font-size: 7.5pt; vertical-align: top; }
th { background-color: #eeeeee; }
"""


def to_pdf(md_path, pdf_path, footer):
    body = md_to_html(Path(md_path).read_text(encoding='utf-8'))
    story = pymupdf.Story(html=f'<html><body>{body}<p><i>{html.escape(footer)}</i></p></body></html>', user_css=CSS)
    tmp = str(pdf_path) + '.raw'
    writer = pymupdf.DocumentWriter(tmp)
    mediabox = pymupdf.paper_rect('a4'); where = mediabox + (48, 48, -48, -56)
    more = True
    while more:
        dev = writer.begin_page(mediabox); more, _ = story.place(where); story.draw(dev); writer.end_page()
    writer.close()
    d = pymupdf.open(tmp); n = d.page_count
    for k, p in enumerate(d):
        p.insert_text((48, mediabox.height - 28), f'{Path(md_path).name} — page {k + 1}/{n}', fontsize=7)
    d.save(str(pdf_path), garbage=3, deflate=True); d.close()
    return n


TEX_ESC = {'\\': r'\textbackslash{}', '&': r'\&', '%': r'\%', '$': r'\$', '#': r'\#', '_': r'\_', '{': r'\{', '}': r'\}', '~': r'\textasciitilde{}', '^': r'\textasciicircum{}'}


def tex_inline(s):
    parts = re.split(r'(`[^`]+`)', s)
    out = []
    for p in parts:
        if p.startswith('`') and p.endswith('`') and len(p) > 1:
            out.append(r'\texttt{' + ''.join(TEX_ESC.get(c, c) for c in p[1:-1]) + '}')
        else:
            q = ''.join(TEX_ESC.get(c, c) for c in p)
            q = re.sub(r'\*\*([^*]+)\*\*', r'\\textbf{\1}', q)
            q = re.sub(r'(?<![*\w])\*([^*\n]+)\*(?![*\w])', r'\\emph{\1}', q)
            out.append(q)
    return ''.join(out)


def md_to_tex(md):
    out = [r'\documentclass[10pt,a4paper]{article}', r'\usepackage{fontspec}', r'\usepackage{unicode-math}',
           r'\usepackage[margin=2cm]{geometry}', r'\usepackage{longtable,array}', r'\usepackage[hidelinks]{hyperref}',
           r'\setlength{\parindent}{0pt}\setlength{\parskip}{4pt}', r'% Semantic source: FINAL_AUDIT_REPORT.md. Requires XeLaTeX/LuaLaTeX (Unicode).',
           r'\begin{document}']
    lines = md.splitlines(); i = 0
    while i < len(lines):
        l = lines[i]
        m = re.match(r'^(#{1,4}) (.*)$', l)
        if m:
            lv = len(m.group(1)); cmd = {1: r'\section*', 2: r'\subsection*', 3: r'\subsubsection*', 4: r'\paragraph*'}[lv]
            out.append(cmd + '{' + tex_inline(m.group(2)) + '}'); i += 1; continue
        if l.startswith('|'):
            rows = []
            while i < len(lines) and lines[i].startswith('|'):
                rows.append(lines[i]); i += 1
            cells = [[c.strip() for c in r.strip().strip('|').split('|')] for r in rows]
            body = [r for r in cells if not all(re.fullmatch(r':?-{2,}:?', c or '--') for c in r)]
            k = max(len(r) for r in body); w = f'{0.95 / k:.3f}'
            out.append(r'{\small\begin{longtable}{' + '|'.join([r'p{' + w + r'\linewidth}'] * k) + '}')
            for j, r in enumerate(body):
                r = r + [''] * (k - len(r))
                out.append(' & '.join(tex_inline(c) for c in r) + r' \\ \hline')
            out.append(r'\end{longtable}}'); continue
        if re.match(r'^\s*[*-] ', l) or re.match(r'^\s*\d+\. ', l):
            env = 'enumerate' if re.match(r'^\s*\d+\. ', l) else 'itemize'; items = []
            while i < len(lines) and (re.match(r'^\s*([*-]|\d+\.) ', lines[i]) or (lines[i].startswith('  ') and items)):
                if re.match(r'^\s*([*-]|\d+\.) ', lines[i]):
                    items.append(re.sub(r'^\s*([*-]|\d+\.) ', '', lines[i]))
                else:
                    items[-1] += ' ' + lines[i].strip()
                i += 1
            out.append(r'\begin{' + env + '}' + ''.join(r'\item ' + tex_inline(x) for x in items) + r'\end{' + env + '}'); continue
        out.append(tex_inline(l) if l.strip() else ''); i += 1
    out.append(r'\end{document}')
    return '\n'.join(out)


if __name__ == '__main__':
    rep = RUN / '30_REPORT'
    md = rep / 'FINAL_AUDIT_REPORT.md'
    (rep / 'FINAL_AUDIT_REPORT.tex').write_text(md_to_tex(md.read_text(encoding='utf-8')), encoding='utf-8')
    foot = 'Rendered from the Markdown semantic source with PyMuPDF; not compiled from the TeX file (no TeX engine installed).'
    print('final pages', to_pdf(md, rep / 'FINAL_AUDIT_REPORT.pdf', foot))
    for g in ['E0', 'E1', 'E2', 'E3', 'E4', 'E5', 'E6', 'E7', 'E8']:
        src = next((RUN / '20_EVIDENCE' / g).glob('E*_RECORD.md'))
        print(g, 'pages', to_pdf(src, RUN / '20_EVIDENCE' / g / (src.stem + '.pdf'), foot))
