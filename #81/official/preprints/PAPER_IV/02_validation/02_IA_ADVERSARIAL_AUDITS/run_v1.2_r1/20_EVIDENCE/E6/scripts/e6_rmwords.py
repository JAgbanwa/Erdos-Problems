"""E6: list roman words in EN math (to spot Spanish fragments in the EN edition)."""
import re, collections
D = "C:/Users/jtraverso/e81p4-publish/preprints/PAPER_IV/01_manuscript/v1.2_full_rebuild_candidate/"
t = open(D + "PAPER_IV_preprint_v1.2_en.md", encoding="utf-8").read()
c = collections.Counter(); where = collections.defaultdict(list)
BS = chr(92)
pat = re.escape(BS) + r"(?:rm|mathrm|text|operatorname)\s*\{?\s*([A-Za-z][A-Za-z ]*)"
for m in re.finditer(pat, t):
    w = m.group(1).strip(); c[w] += 1; where[w].append(t.count("\n", 0, m.start()) + 1)
for w, n in c.most_common():
    print(n, repr(w), where[w][:6])
