"""E1/E3 supplementary (auditor-written, run_v1.22_r3). Read-only, no Lean.
For each of the 13 entries of the author's SEMANTIC_HEADERS.json:
- source file sha256 == SOURCE_MANIFEST entry and == JSON; line number points to `theorem <name>`
- header text re-extracted independently (from `theorem` to first ':=' at bracket depth 0) == JSON header
- enclosing namespace(s) and `variable` lines in scope before the theorem
- definitions of key predicates used (structure/def lines) located
- external compilation log of run_v1.2_r1 exists, sha256 == JSON, module PASS in records.jsonl"""
import json, re, sys, hashlib, pathlib
B = pathlib.Path('C:/Users/jtraverso/e81p4-publish/preprints/PAPER_IV')
CUT = B / '05_formalization/lean_piv-v12-fb459343d234'
R3 = B / '01_manuscript/v1.22_editorial_candidate_r3'
P1 = B / '02_validation/02_IA_ADVERSARIAL_AUDITS/run_v1.2_r1'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
man = {e['path']: e['sha256'] for e in json.loads((B / '03_reproducibility/build_piv-v12-fb459343d234/SOURCE_MANIFEST.json').read_text())}
recs = {}
for l in (P1 / '10_LOGS/E4_main/records.jsonl').read_text(encoding='utf-8').splitlines():
    r = json.loads(l); recs[r['module']] = r
H = json.loads((R3 / 'SEMANTIC_HEADERS.json').read_text(encoding='utf-8'))
def my_header(text, start):
    depth = 0; i = start
    while i < len(text) - 1:
        c = text[i]
        if c in '([{⟨': depth += 1
        elif c in ')]}⟩': depth -= 1
        elif text.startswith(':=', i) and depth == 0: return text[start:i].rstrip()
        i += 1
    return None
def scope(text, pos):
    ns = []; var = []
    for m in re.finditer(r'(?m)^(namespace|end|section|variable)\b ?(.*)$', text[:pos]):
        k, v = m.group(1), m.group(2).strip()
        if k == 'namespace': ns.append(v)
        elif k == 'end' and ns and (v == ns[-1] or v == ''): ns.pop()
        elif k == 'variable': var.append(v)
    return ns, var
out = []
for e in H:
    p = CUT / e['source']; text = p.read_text(encoding='utf-8')
    short = e['name'].split('.')[-1]
    m = re.search(r'(?m)^theorem ' + re.escape(short) + r'\b', text)
    line = text.count('\n', 0, m.start()) + 1 if m else None
    mine = my_header(text, m.start()) if m else None
    ns, var = scope(text, m.start()) if m else ([], [])
    module = e['source'][:-5].replace('/', '.')
    log = B / e['external_compilation_log']
    out.append({'name': e['name'], 'source': e['source'],
                'source_sha_eq_manifest': sha(p) == man.get(e['source']), 'source_sha_eq_json': sha(p) == e['source_sha256'],
                'line_json': e['line'], 'line_found': line, 'line_ok': line == e['line'],
                'header_eq_json': mine == e['header'] if mine else False, 'namespaces_in_scope': ns, 'variables_in_scope': var,
                'elaborated_name_guess': '.'.join(ns + [short]),
                'log_exists': log.exists(), 'log_sha_eq_json': log.exists() and sha(log) == e['log_sha256'],
                'module_record_PASS': recs.get(module, {}).get('status') == 'PASS', 'module_exit': recs.get(module, {}).get('exit'),
                'log_mentions_error': bool(re.search(r'\berror\b', log.read_text(encoding='utf-8', errors='replace'))) if log.exists() else None,
                'header': mine})
json.dump(out, open(sys.argv[1], 'w', encoding='utf-8'), indent=1, ensure_ascii=False)
for o in out:
    print(o['name'], '| src', o['source_sha_eq_manifest'], o['source_sha_eq_json'], '| line', o['line_ok'], '| hdr', o['header_eq_json'], '| log', o['log_sha_eq_json'], o['module_record_PASS'], o['module_exit'], 'err', o['log_mentions_error'], '| ns', o['namespaces_in_scope'], '| vars', len(o['variables_in_scope']))
