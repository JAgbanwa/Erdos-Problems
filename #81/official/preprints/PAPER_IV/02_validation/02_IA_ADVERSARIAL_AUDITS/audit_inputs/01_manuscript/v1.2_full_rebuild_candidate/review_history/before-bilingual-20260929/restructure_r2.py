"""One-time, checked structural edit of the approved English review source.
Moves mathematical text verbatim; renumbers only explicit references/labels.
The before-r2 snapshot is immutable input and remains available for review.
"""
from pathlib import Path
from collections import Counter
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parent
FILE = ROOT / 'PAPER_IV_preprint_v1.2_en.md'
BEFORE = ROOT / 'review_history/before-r2-20260929' / FILE.name
old = BEFORE.read_text(encoding='utf-8')
assert FILE.read_text(encoding='utf-8') == old, 'Unexpected input; do not overwrite later edits'
text = old

def once(a, b):
    global text
    assert text.count(a) == 1, a[:100]
    text = text.replace(a, b)

def cut(start, end):
    global text
    a, b = text.index(start), text.index(end)
    piece = text[a:b]
    text = text[:a] + text[b:]
    return piece

comparator = cut('### 6.6. Equality of mixed optima', '### 6.8. Fixed-defect stability')
comparator = comparator.replace('### 6.6.', '### D.2.').replace('### 6.7.', '### D.3.')
complements = cut('### 8.2. The all-order bound', '## Appendix A.')
complements = complements.replace('### 8.2.', '### G.1.').replace('### 8.3.', '### G.2.')
once('## Appendix D. The complete graph at every order',
     '## Appendix D. Complete graphs and comparator identities\n\n### D.1. The complete graph at every order')
once('## Appendix E. The fixed-defect extension', comparator + '## Appendix E. The fixed-defect extension')
once('## Acknowledgments', '## Appendix G. Packing gaps and limits of cleanup\n\n' + complements + '## Acknowledgments')
once('### 6.8. Fixed-defect stability on one root', '### 6.6. Fixed-defect stability on one root')
once('### 6.9. Uniform bounds and sublinear defect', '### 6.7. Uniform bounds and sublinear defect')

# Replace section locators, not theorem or equation numbers.
for a, b in [('§§6.8–6.9', '§§6.6–6.7'), ('Sections 6.8 and 6.9', 'Sections 6.6 and 6.7'),
             ('Section 6.8', 'Section 6.6'), ('Section 6.9', 'Section 6.7'),
             ('§6.8', '§6.6'), ('§6.9', '§6.7'),
             ('Section 6.6', 'Section 6.6'),
             ('§8.2', 'Appendix G.1'), ('§8.3', 'Appendix G.2')]:
    text = text.replace(a, b)

equations = {'6.10':'D.6', '6.11':'D.7', '6.12':'D.8', '8.1a':'G.1',
             **{f'8.{i}':f'G.{i}' for i in range(2,6)}}
ordered = [f'6.{i}' for i in range(13,23)] + ['6.20a','6.20b'] + [f'6.{i}' for i in range(23,31)]
equations.update({label:f'6.{i}' for i,label in enumerate(ordered,10)})
def retag(match):
    prefix, label, suffix = match.groups()
    return prefix + equations.get(label,label) + suffix
text = re.sub(r'(\\tag\{)([^}]+)(\})', retag, text)
text = re.sub(r'(\()((?:6|8)\.\d+[ab]?)(\))', retag, text)
results = {'Proposition 6.3':'Proposition D.3', 'Corollary 6.4':'Corollary 6.3',
           'Proposition 6.4a':'Proposition 6.3a', 'Proposition 6.5':'Proposition 6.4',
           'Theorem 6.6':'Theorem 6.5', 'Corollary 6.7':'Corollary 6.6',
           'Proposition 8.1':'Proposition G.1'}
text = re.sub('|'.join(re.escape(k) for k in sorted(results,key=len,reverse=True)),
              lambda m: results[m.group()],text)

once('This last assertion answers Erdős Problem 81 [1,8]; there are no exceptions in the order.',
     'This gives the bound asked in Erdős Problem 81 [1,8] for every order, with no exceptions; it also follows from the eventual bound of [5], as discussed in §8.1.')
needle='The absence of these names is a reproducible audit result, not an inference from the import list.'
once(needle, 'Our modules PaperIV.Erdos81Unconditional and PaperIV.Erdos81AllOrders have namespace root PaperIV; they are not the excluded root Erdos81 used by [5]. ' + needle)
once('### E.2. From the terminal to the eventual theorem\n\n',
     '### E.2. From the terminal to the eventual theorem\n\nThe selected explicit proof follows the terminal and minimum-degree reduction described below. Its localization is supplied by E34, and its thresholds are evaluated explicitly; the historical existential assembly has the same reduction structure.\n\n')
once('Appendix B collects complementary tools.',
     'Appendix B collects complementary tools. Appendix D also records the comparator identities, and Appendix G treats the bounded-clique triangle gap and the separate limitation of the cleanup contract.')
needle='The maximum in (6.11) equals'
assert needle in text
figure='''![Proof structure for fixed-defect same-root stability.](figures_en/fig4_same_root_stability.png)

**Figure 4.** Theorem C′: low-degree deletion reaches the controlled terminal, and reinsertion transports its root back to the original graph. The retained accounts then control every partition on that same root. Resizing to an optimal template is a separate step (Corollary 6.3), with the square-root cost illustrated by Proposition 6.3a. The diagram is schematic; Appendix F.1 supplies the induction window.

'''
once('**Proof.** We first explain the retained estimate at the minimum-degree terminal, then the passage to an arbitrary graph in the class.',
     figure + '**Proof.** We first explain the retained estimate at the minimum-degree terminal, then the passage to an arbitrary graph in the class.')

# Account for all protected displays under the exact renumbering, including moves.
def displays(s):
    return re.findall(r'\\\[.*?\\\]',s,re.S)
expected = [re.sub(r'(\\tag\{)([^}]+)(\})',retag,x) for x in displays(old)]
assert Counter(expected) == Counter(displays(text)), 'A displayed formula changed'
assert re.findall(r'```lean.*?```',old,re.S) == re.findall(r'```lean.*?```',text,re.S)
assert len(re.findall(r'\\tag\{([^}]+)\}',text)) == len(set(re.findall(r'\\tag\{([^}]+)\}',text)))
FILE.write_text(text,encoding='utf-8')
report={'input_sha256':hashlib.sha256(BEFORE.read_bytes()).hexdigest(),
        'output_sha256':hashlib.sha256(FILE.read_bytes()).hexdigest(),
        'equation_map':equations,'result_map':results,
        'protected_displays_preserved_modulo_labels':len(expected),
        'lean_blocks_unchanged':True,
        'scope':'Editorial relocation and explicit renumbering only; no mathematical strengthening.'}
(ROOT/'R2_STRUCTURAL_MAP.json').write_text(json.dumps(report,indent=2),encoding='utf-8')
print(json.dumps(report,indent=2))
