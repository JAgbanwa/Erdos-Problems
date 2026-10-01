"""Record the semantic baseline and apply scoped mechanical presentation changes."""
from pathlib import Path
import hashlib, json, re

ROOT = Path(__file__).resolve().parent
BASE = ROOT.parent / 'v1.21_editorial_candidate'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
index = []
for lang in ('en', 'es'):
    p = BASE / f'PAPER_IV_preprint_v1.21_{lang}.md'
    text = p.read_text(encoding='utf-8')
    for kind, pattern in [('display', r'\\\[.*?\\\]'), ('lean', r'```lean\n.*?\n```'),
                          ('result_paragraph', r'(?m)^\*\*(?:Theorem|Lemma|Proposition|Corollary|Teorema|Lema|Proposición|Corolario) [^\n]+')]:
        for i, m in enumerate(re.finditer(pattern, text, re.S if kind != 'result_paragraph' else 0)):
            index.append(dict(language=lang, kind=kind, ordinal=i, line=text[:m.start()].count('\n')+1,
                              sha256=hashlib.sha256(m[0].encode()).hexdigest(), text=m[0],
                              allowed='presentation only; no statement/constant/dependency change'))
(ROOT/'PROTECTED_BASELINE.json').write_text(json.dumps({'baselines':{lang:sha(BASE/f'PAPER_IV_preprint_v1.21_{lang}.md') for lang in ('en','es')},'elements':index},ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
for lang in ('en','es'):
    p=ROOT/f'PAPER_IV_preprint_v1.22_{lang}.md'
    t=p.read_text(encoding='utf-8')
    t=t.replace('version 1.21, editorial review candidate.', 'version 1.22, editorial review candidate.')
    t=t.replace('versión 1.21, candidata a revisión editorial.', 'versión 1.22, candidata a revisión editorial.')
    t=t.replace('**Date of this revision:** September 30, 2026.', '**Date of this revision:** October 1, 2026.')
    t=t.replace('**Fecha de esta revisión:** 30 de septiembre de 2026.', '**Fecha de esta revisión:** 1 de octubre de 2026.')
    t=t.replace('This is E34.lemma3.', 'This is `E34.lemma3`.').replace('Éste es E34.lemma3.', 'Éste es `E34.lemma3`.')
    t=t.replace(' E34.transfer ', ' `E34.transfer` ')
    t=t.replace('PreferenceLabs', 'Preference Labs')
    t=t.replace('### 5.1. `Regularization`', '### 5.1. Regularization')
    t=t.replace('| `Regularization` mass,', '| Regularization mass,')
    t=t.replace('### Lema 3.2. `Nibble`', '### Lema 3.2. Nibble')
    t=t.replace('bounded gain function from Model', 'bounded gain function from `Model`')
    if lang=='es':
        # Only prose before References; never translate cited titles or identifiers.
        cut=t.index('[1] ')
        body,refs=t[:cut],t[cut:]
        spans=re.split(r'(```.*?```|`[^`]+`|\\\[.*?\\\]|\\\(.*?\\\))',body,flags=re.S)
        for i in range(0,len(spans),2):
            spans[i]=re.sub(r'\bmatchings\b','emparejamientos',spans[i])
            spans[i]=re.sub(r'\bmatching\b','emparejamiento',spans[i])
            spans[i]=re.sub(r'\bpacking\b','empaquetamiento',spans[i])
        refs=refs.replace('Integer and fractional empaquetamientos in dense graphs','Integer and fractional packings in dense graphs')
        t=''.join(spans)+refs
    p.write_text(t,encoding='utf-8')
for name in ('build_draft.py','build_draft_en.py'):
    p=ROOT/name
    p.write_text(p.read_text(encoding='utf-8').replace('PAPER_IV_preprint_v1.21_', 'PAPER_IV_preprint_v1.22_'),encoding='utf-8')
p=ROOT/'make_stability_figure_es.py'
p.write_text(p.read_text(encoding='utf-8').replace('Cotas de edición y baseline','Cotas de edición y valor base'),encoding='utf-8')
print('Baseline indexed; scoped mechanical edits applied.')
