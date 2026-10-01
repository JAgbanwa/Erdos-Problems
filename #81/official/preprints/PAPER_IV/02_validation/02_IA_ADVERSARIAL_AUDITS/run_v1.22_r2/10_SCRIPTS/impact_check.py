"""Impact control (auditor-written, run_v1.22_r2) for E1/E2/E3/E7: where do the r1->r2 ES changes fall?
For each changed MD line: enclosing section heading, whether the paragraph is a result statement
(Teorema/Lema/Proposición/Corolario lead), a proof, a table row, or the reference list; whether it contains
math; and resolution of new code tokens against the frozen Lean cut. Read-only."""
import re, json, sys, pathlib
B = pathlib.Path('C:/Users/jtraverso/e81p4-publish/preprints/PAPER_IV')
r1 = (B / '01_manuscript/v1.22_editorial_candidate/PAPER_IV_preprint_v1.22_es.md').read_text(encoding='utf-8').splitlines()
r2 = (B / '01_manuscript/v1.22_editorial_candidate_r2/PAPER_IV_preprint_v1.22_es.md').read_text(encoding='utf-8').splitlines()
assert len(r1) == len(r2)
changed = [i for i in range(len(r1)) if r1[i] != r2[i]]
refstart = next(i for i, l in enumerate(r2) if re.match(r'^#+ Referencias', l))
out = []
for i in changed:
    head = next((r2[j] for j in range(i, -1, -1) if r2[j].startswith('#')), None)
    # paragraph start
    j = i
    while j > 0 and r2[j - 1].strip() != '':
        j -= 1
    lead = r2[j][:80]
    is_statement = bool(re.match(r'^\*\*(Teorema|Lema|Proposición|Corolario)[^*]*\*\*', r2[j]))
    # inside a proof block: nearest previous paragraph-lead 'Demostración' before next statement
    k = i; in_proof = False
    while k >= 0:
        if re.match(r'^\*\*(Demostración)', r2[k]): in_proof = True; break
        if re.match(r'^\*\*(Teorema|Lema|Proposición|Corolario)', r2[k]) or r2[k].startswith('#'): break
        k -= 1
    out.append({'line': i + 1, 'section': head, 'paragraph_lead': lead, 'is_result_statement_paragraph': is_statement,
                'in_proof': in_proof, 'is_table_row': r2[i].startswith('|'), 'in_reference_list': i >= refstart,
                'r1_math_spans': re.findall(r'\\\((.*?)\\\)', r1[i]) == re.findall(r'\\\((.*?)\\\)', r2[i])})
SRC = B / '05_formalization/lean_piv-v12-fb459343d234'
alltext = '\n'.join(p.read_text(encoding='utf-8') for p in SRC.rglob('*.lean'))
code = lambda L: re.findall(r'`([^`\n]+)`', '\n'.join(L))
new_tokens = sorted(set(code(r2)) - set(code(r1)))
res = {t: bool(re.search(r'^namespace\s+' + re.escape(t) + r'\b', alltext, re.M)) or bool(re.search(r'\b' + re.escape(t) + r'\.', alltext)) for t in new_tokens}
summary = {'changed_lines': [o['line'] for o in out], 'any_result_statement': any(o['is_result_statement_paragraph'] for o in out),
           'any_table_row': any(o['is_table_row'] for o in out), 'any_reference_list': any(o['in_reference_list'] for o in out),
           'all_inline_math_identical': all(o['r1_math_spans'] for o in out), 'new_code_tokens_es': new_tokens, 'new_tokens_resolve_in_lean_cut': res}
json.dump({'summary': summary, 'lines': out}, open(sys.argv[1], 'w', encoding='utf-8'), indent=1, ensure_ascii=False)
print(json.dumps(summary, indent=1, ensure_ascii=False))
for o in out: print(o['line'], '|', (o['section'] or '')[:60], '|', o['paragraph_lead'][:50], '| stmt', o['is_result_statement_paragraph'], '| proof', o['in_proof'])
