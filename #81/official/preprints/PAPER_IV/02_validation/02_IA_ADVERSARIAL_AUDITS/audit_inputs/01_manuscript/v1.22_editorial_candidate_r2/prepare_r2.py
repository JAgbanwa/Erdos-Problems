"""Mechanical ES-only corrections; reject any difference beyond the allowlist."""
from pathlib import Path
import hashlib, json, re, difflib

ROOT = Path(__file__).resolve().parent
BASE = ROOT.parent / 'v1.22_editorial_candidate'
NAME = 'PAPER_IV_preprint_v1.22_es.md'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def protected(text):
    return {
        'display': re.findall(r'\\\[.*?\\\]', text, re.S),
        'inline_math': re.findall(r'\\\(.*?\\\)', text, re.S),
        'code_blocks': re.findall(r'```.*?```', text, re.S),
        'tags': re.findall(r'\\tag\{[^}]+\}', text),
        'result_paragraphs': re.findall(r'(?m)^\*\*(?:Teorema|Lema|Proposición|Corolario) [^\n]+', text),
    }

old = (BASE / NAME).read_text(encoding='utf-8')
assert (ROOT / NAME).read_text(encoding='utf-8') == old, 'Not an untouched copy'
body, refs = old.split('## Referencias', 1)
hits = re.findall(r'\bmatchings?\b', body)
assert len(hits) == 11, hits
assert len(re.findall(r'\bpacking\b', body)) == 1
assert body.count('ganancia acotada de Model.') == 1
newbody = re.sub(r'\bmatchings\b', 'emparejamientos', body)
newbody = re.sub(r'\bmatching\b', 'emparejamiento', newbody)
newbody = re.sub(r'\bpacking\b', 'empaquetamiento', newbody)
newbody = newbody.replace('ganancia acotada de Model.', 'ganancia acotada de `Model`.')
new = newbody + '## Referencias' + refs
assert protected(old) == protected(new)
before_codes = re.findall(r'`[^`\n]+`', old)
after_codes = re.findall(r'`[^`\n]+`', new)
from collections import Counter
assert Counter(after_codes) - Counter(before_codes) == Counter({'`Model`': 1})
assert not Counter(before_codes) - Counter(after_codes)
(ROOT / 'PROTECTED_BASELINE.json').write_text(json.dumps({
    'baseline_sha256': sha(BASE / NAME), 'protected': protected(old)
}, ensure_ascii=False, indent=2)+'\n', encoding='utf-8')
(ROOT / NAME).write_text(new, encoding='utf-8')
(ROOT / 'CHANGES_es.diff').write_text(''.join(difflib.unified_diff(
    old.splitlines(True), new.splitlines(True), fromfile='v1.22-r1/es.md',
    tofile='v1.22-r2/es.md')), encoding='utf-8')
english = []
for ext in ('md', 'tex', 'pdf'):
    name = f'PAPER_IV_preprint_v1.22_en.{ext}'
    assert (ROOT / name).read_bytes() == (BASE / name).read_bytes()
    english.append({'file': name, 'sha256': sha(ROOT/name), 'byte_identical': True})
(ROOT / 'SEMANTIC_CHECKS.json').write_text(json.dumps({
    'revision': 'v1.22-r2', 'spanish_input_sha256': sha(BASE/NAME),
    'spanish_output_sha256': sha(ROOT/NAME), 'matching_occurrences_corrected': 11,
    'packing_occurrences_corrected': 1, 'model_formatting_corrections': 1,
    'protected_fields_identical': list(protected(old)), 'references_identical': True,
    'english': english, 'lean_executed': False,
    'scope': 'Only the enumerated ES terminology and one code-format marker changed; version, date and audit-status prose intentionally retained.'
}, ensure_ascii=False, indent=2)+'\n', encoding='utf-8')
print('PASS: 11 matching(s), 1 packing, 1 Model format; protected text and EN unchanged.')
