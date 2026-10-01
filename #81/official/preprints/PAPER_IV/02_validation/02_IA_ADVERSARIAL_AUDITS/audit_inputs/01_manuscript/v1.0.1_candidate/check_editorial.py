"""Reproducible editorial checks; not an external mathematical audit."""
from pathlib import Path
import difflib
import hashlib
import json
import re
import sys

ROOT = Path(__file__).resolve().parent
BASE = ROOT.parent / 'v1.0_candidate'
sys.path.insert(0, str(Path.home() / '.cache/e81-editorial-tools/python-libs'))
import fitz

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def displays(text):
    return re.findall(r'\\\[(.*?)\\\]', text, re.S)

def clean_labels(text):
    return re.sub(r'\\text\{[^}]*\}', r'\\text{LABEL}', re.sub(r'\s+', '', text))

def headings(text):
    return re.findall(r'(?m)^#{2,4} .+$', text)

def code(text):
    return re.findall(r'```[^\n]*\n(.*?)```', text, re.S)

def identifiers(text):
    # F-12 corrected a document path, not a Lean declaration. File extensions
    # must not be mistaken for namespace components in either baseline.
    return sorted({x for x in re.findall(r'`([A-Z][A-Za-z0-9_]*(?:\.[A-Za-z0-9_]+)+)`', text)
                   if not x.endswith(('.md', '.lean', '.json', '.tex', '.pdf'))})

failures = []
results = {'scope': 'Editorial r3 preparation only; external r2 FAIL retained; r3 NOT STARTED', 'editions': {}}
protected = {}
texts = {}
for lang in ('en', 'es'):
    stem = f'PAPER_IV_preprint_v1.0.1_{lang}'
    src, tex, pdf = [ROOT / (stem + ext) for ext in ('.md', '.tex', '.pdf')]
    baseline = BASE / f'PAPER_IV_preprint_v1.0_{lang}.md'
    old, text = baseline.read_text(encoding='utf-8'), src.read_text(encoding='utf-8')
    texts[lang] = text
    math = displays(text)
    checks = {'displays_unchanged': math == displays(old),
              'code_unchanged': code(text) == code(old),
              'body_headings_unchanged': headings(text) == headings(old),
              'formal_identifiers_unchanged': identifiers(text) == identifiers(old),
              'no_intermediate_version': not re.search(r'v?1\.0\.[23]', text),
              'version_present': '1.0.1' in text,
              'source_identity_present': 'piv-v1.0-f1769273dd2c' in text,
              'source_to_tex_to_pdf_order': src.stat().st_mtime <= tex.stat().st_mtime <= pdf.stat().st_mtime}
    protected[lang] = {'baseline': str(baseline), 'baseline_sha256': sha(baseline),
                      'source_sha256': sha(src),
                      'display_elements': [{'id': f'{lang}-EQ-{i+1:03}', 'sha256': hashlib.sha256(x.encode()).hexdigest(),
                                            'allowed_change': 'NONE', 'owner': 'author'} for i, x in enumerate(math)],
                      'formal_identifiers': identifiers(text)}
    (ROOT / f'DIFF_FROM_v1.0_{lang}.patch').write_text(''.join(difflib.unified_diff(old.splitlines(True), text.splitlines(True), fromfile=baseline.name, tofile=src.name)), encoding='utf-8')
    log = (ROOT / (stem + '.log')).read_text(encoding='utf-8')
    console = (ROOT / ('compiler_console_en.log' if lang == 'en' else 'compiler_console.log')).read_text(encoding='utf-8')
    problems = [line for line in log.splitlines() if re.search(r'Overfull|Missing character|undefined references|LaTeX Error|^!', line)]
    checks['compiler_no_errors_or_overflow'] = not problems
    checks['compiler_names_output'] = stem + '.pdf' in console
    checks['two_tex_passes'] = 'Rerunning TeX' in console
    doc = fitz.open(pdf)
    outside = []
    for i, page in enumerate(doc):
        for block in page.get_text('dict')['blocks']:
            for line in block.get('lines', []):
                for span in line['spans']:
                    x0, y0, x1, y1 = span['bbox']
                    if x0 < -1 or y0 < -1 or x1 > page.rect.width + 1 or y1 > page.rect.height + 1:
                        outside.append({'page': i+1, 'text': span['text']})
    rendered = ROOT / f'qa_{lang}'
    checks['no_off_page_spans'] = not outside
    checks['render_matches_pdf'] = (rendered / 'pdf_sha256.txt').read_text().strip() == sha(pdf)
    checks['all_pages_rendered_after_pdf'] = all((rendered / f'page_{i+1:02}.png').is_file() and (rendered / f'page_{i+1:02}.png').stat().st_mtime >= pdf.stat().st_mtime for i in range(len(doc)))
    checks['figures_present'] = len(re.findall(r'!\[', text)) == 3
    results['editions'][lang] = {'checks': checks, 'pages': len(doc), 'display_blocks': len(math),
                               'code_blocks': len(code(text)), 'body_headings': len(headings(text)),
                               'compiler_problems': problems, 'off_page_spans': outside,
                               'nonfatal_fontconfig_advisory': 'Fontconfig error' in console,
                               'hashes': {p.name: sha(p) for p in (src, tex, pdf)}}
    failures += [f'{lang}:{key}' for key, value in checks.items() if not value]

en, es = texts['en'], texts['es']
pair_checks = {'display_math_translation_aware': [clean_labels(x) for x in displays(en)] == [clean_labels(x) for x in displays(es)],
               'heading_depth': [len(x.split(' ')[0]) for x in headings(en)] == [len(x.split(' ')[0]) for x in headings(es)],
               'equation_tags': re.findall(r'\\tag\{([^}]*)\}', en) == re.findall(r'\\tag\{([^}]*)\}', es),
               'code_blocks': code(en) == code(es), 'formal_identifiers': identifiers(en) == identifiers(es)}
failures += [f'parity:{key}' for key, value in pair_checks.items() if not value]
results['parity'] = pair_checks
results['failures'] = failures
results['status'] = 'PASS_STATIC_EDITORIAL_CHECKS' if not failures else 'FAIL'
results['limits'] = 'Not a proof or full semantic/visual review. See EDITORIAL_DELTA_REPORT.md for those checks and their scope.'
(ROOT / 'PROTECTED_ELEMENTS.json').write_text(json.dumps(protected, indent=2) + '\n', encoding='utf-8')
(ROOT / 'EDITORIAL_CHECKS.json').write_text(json.dumps(results, indent=2) + '\n', encoding='utf-8')
print(json.dumps(results, indent=2))
raise SystemExit(bool(failures))
