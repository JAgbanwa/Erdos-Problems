"""Find Markdown table rows whose unescaped-pipe count differs from the header row (report QA)."""
import re, glob, os
os.chdir('C:/Users/jtraverso/e81p4-publish/preprints/PAPER_IV/02_validation/02_IA_ADVERSARIAL_AUDITS/run_v1.22_r3')
PIPE = re.compile(r'(?<!\\)\|')
SEP = re.compile(r'^\|[-: |]+\|\s*$')
files = ['30_REPORT/FINAL_CONSOLIDATED_AUDIT_REPORT.md', '30_REPORT/CLAIM_MAP_CONSOLIDATED.md'] + sorted(glob.glob('30_REPORT/gates/*.md'))
for f in files:
    lines = open(f, encoding='utf-8').read().split('\n'); hdr = None
    for i, l in enumerate(lines):
        if l.startswith('|'):
            n = len(PIPE.findall(l))
            if hdr is None: hdr = n
            elif n != hdr and not SEP.match(l): print(f, i + 1, hdr, n, l[:120])
        else:
            hdr = None
