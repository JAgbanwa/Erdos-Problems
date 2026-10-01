"""Escape absolute-value pipes inside Markdown table rows of the auditor's own records (formatting only).
A pipe is kept as a cell separator iff it is preceded by line start or a space AND followed by a space or line end."""
import re, glob, os
os.chdir('C:/Users/jtraverso/e81p4-publish/preprints/PAPER_IV/02_validation/02_IA_ADVERSARIAL_AUDITS/run_v1.2_r1')
files = ['30_REPORT/FINAL_AUDIT_REPORT.md'] + sorted(glob.glob('20_EVIDENCE/*/*.md'))
def fix_row(l):
    out = []
    for i, ch in enumerate(l):
        if ch == '|' and (i == 0 or l[i - 1] != '\\'):
            pre = i == 0 or l[i - 1] == ' '
            post = i == len(l) - 1 or l[i + 1] == ' '
            out.append('|' if (pre and post) else '\\|')
        else:
            out.append(ch)
    return ''.join(out)
for f in files:
    s = open(f, encoding='utf-8').read(); lines = s.split('\n'); changed = 0
    for k, l in enumerate(lines):
        if l.startswith('|') and not re.match(r'^\|[-: |]+\|\s*$', l):
            nl = fix_row(l)
            if nl != l: lines[k] = nl; changed += 1
    if changed:
        open(f, 'w', encoding='utf-8').write('\n'.join(lines)); print(f, 'rows changed', changed)
