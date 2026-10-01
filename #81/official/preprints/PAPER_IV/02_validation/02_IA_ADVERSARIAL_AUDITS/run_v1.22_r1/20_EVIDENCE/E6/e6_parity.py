"""E6/E1 (auditor-written): display-math parity EN/ES for v1.22, preservation vs v1.21, tags, theorem
headings, Lean code blocks, reference list titles. Read-only."""
import re, json, pathlib, sys, collections
B = pathlib.Path('C:/Users/jtraverso/e81p4-publish/preprints/PAPER_IV/01_manuscript')
rd = lambda v, l: (B / f'v{v}_editorial_candidate/PAPER_IV_preprint_v{v}_{l}.md').read_text(encoding='utf-8')
txt = {(v, l): rd(v, l) for v in ('1.21', '1.22') for l in ('en', 'es')}
disp = lambda t: [re.sub(r'\s+', ' ', m).strip() for m in re.findall(r'\\\[(.*?)\\\]', t, re.S)]
norm = lambda s: re.sub(r'\\text\{[^}]*\}', r'\\text{}', s)
tags = lambda t: re.findall(r'\\tag\{([^}]*)\}', t)
code_blocks = lambda t: re.findall(r'```lean\n(.*?)```', t, re.S)
heads = lambda t: [l for l in t.splitlines() if re.match(r'^(\*\*(Theorem|Teorema|Lemma|Lema|Corollary|Corolario|Proposition|Proposición)[^*]*\*\*|### (Theorem|Teorema|Lemma|Lema|Corollary|Corolario|Proposition|Proposición))', l)]
out = {}
for l in ('en', 'es'):
    d21, d22 = disp(txt[('1.21', l)]), disp(txt[('1.22', l)])
    c21, c22 = collections.Counter(d21), collections.Counter(d22)
    out[l] = {'displays_v121': len(d21), 'displays_v122': len(d22), 'removed_vs_v121': list((c21 - c22).elements()), 'added_vs_v121': len(list((c22 - c21).elements())),
              'tags_equal_v121': tags(txt[('1.21', l)]) == tags(txt[('1.22', l)]), 'lean_blocks_equal_v121': code_blocks(txt[('1.21', l)]) == code_blocks(txt[('1.22', l)]),
              'theorem_heading_lines_v121': len(heads(txt[('1.21', l)])), 'theorem_heading_lines_v122': len(heads(txt[('1.22', l)]))}
en, es = [norm(x) for x in disp(txt[('1.22', 'en')])], [norm(x) for x in disp(txt[('1.22', 'es')])]
out['en_es_display_sequence_equal_mod_text'] = en == es
out['en_es_display_mismatches'] = [(i, a[:120], b[:120]) for i, (a, b) in enumerate(zip(en, es)) if a != b][:20]
out['en_es_display_counts'] = (len(en), len(es))
refs = lambda t: re.findall(r'^\[(\d+)\] (.*)$', t, re.M)
rt = {l: {n: s for n, s in refs(txt[('1.22', l)])} for l in ('en', 'es')}
q = lambda s: re.findall(r'[“«]([^”»]+)[”»]|\*([^*]+)\*', s)
out['ref_title_mismatch'] = {}
for n in rt['en']:
    te = [a or b for a, b in q(rt['en'][n])][:1]; ts = [a or b for a, b in q(rt['es'].get(n, ''))][:1]
    te = [x.rstrip(',') for x in te]; ts = [x.rstrip(',') for x in ts]
    if te != ts: out['ref_title_mismatch'][n] = (te, ts)
json.dump(out, open(sys.argv[1], 'w', encoding='utf-8'), indent=1, ensure_ascii=False)
print(json.dumps(out, indent=1, ensure_ascii=False)[:5000])
