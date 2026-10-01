"""Apply the recorded one-time label relocation to the review documents."""
from pathlib import Path
import json
import re

ROOT = Path(__file__).resolve().parent
mapping = json.loads((ROOT / 'R2_STRUCTURAL_MAP.json').read_text(encoding='utf-8'))
for name in ('V1.2_EN_REVIEW_REPORT.md', 'V1.2_CLAIM_MAP.md', 'README.md'):
    path = ROOT / name
    before = (ROOT / 'review_history/before-r2-20260929' / name).read_text(encoding='utf-8')
    assert path.read_text(encoding='utf-8') == before, name + ': already changed'
    names = mapping['result_map']
    after = re.sub('|'.join(re.escape(k) for k in sorted(names, key=len, reverse=True)),
                   lambda m: names[m[0]], before)
    after = re.sub(r'\((\d+\.\d+[ab]?)\)',
                   lambda m: '(' + mapping['equation_map'].get(m[1], m[1]) + ')', after)
    after = after.replace('§6.8', '§6.6').replace('§6.9', '§6.7')
    path.write_text(after, encoding='utf-8')
