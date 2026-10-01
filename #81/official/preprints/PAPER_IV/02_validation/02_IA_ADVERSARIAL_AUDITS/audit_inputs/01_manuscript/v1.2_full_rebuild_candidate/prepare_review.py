"""Preserve the editorial baseline and mechanically retarget the series builders."""
from pathlib import Path
import hashlib, json, re

ROOT = Path(__file__).resolve().parent
BASE = ROOT.parent / 'v1.0.1_candidate'
index = []
for lang in ('en', 'es'):
    path = BASE / f'PAPER_IV_preprint_v1.0.1_{lang}.md'
    source = path.read_text(encoding='utf-8')
    for kind, pattern in [('display', r'\\\[.*?\\\]'),
                          ('lean', r'```lean\n.*?\n```'),
                          ('result_heading', r'(?m)^.*(?:\*\*|### )(?:Theorem|Teorema|Lemma|Lema|Corollary|Corolario|Proposition|Proposición)[^\n]*')]:
        for m in re.finditer(pattern, source, re.S if kind != 'result_heading' else 0):
            index.append(dict(language=lang, kind=kind, line=source.count('\n',0,m.start())+1,
                              sha256=hashlib.sha256(m[0].encode()).hexdigest(),
                              text=m[0], owner='author', edit_class='protected: retain; additions separately mapped'))
    index.append(dict(language=lang, kind='baseline_file', file=str(path),
                      sha256=hashlib.sha256(path.read_bytes()).hexdigest()))
(ROOT/'PROTECTED_BASELINE.json').write_text(json.dumps(index,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
for name in ('build_draft.py','build_draft_en.py'):
    path=ROOT/name
    path.write_text(path.read_text(encoding='utf-8').replace('v1.0.1','v1.2'),encoding='utf-8')
