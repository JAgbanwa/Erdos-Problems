"""List lines changed/added in v1.21 EN vs v1.2 EN, and print EN/ES pairs of those lines."""
import difflib, sys
D = "C:/Users/jtraverso/e81p4-publish/preprints/PAPER_IV/01_manuscript/"
OUT = "C:/Users/jtraverso/e81p4-publish/preprints/PAPER_IV/02_validation/02_IA_ADVERSARIAL_AUDITS/run_v1.21_r1/20_EVIDENCE/E6/results/"
old = open(D + "v1.2_full_rebuild_candidate/PAPER_IV_preprint_v1.2_en.md", encoding="utf-8").read().split("\n")
en = open(D + "v1.21_editorial_candidate/PAPER_IV_preprint_v1.21_en.md", encoding="utf-8").read().split("\n")
es = open(D + "v1.21_editorial_candidate/PAPER_IV_preprint_v1.21_es.md", encoding="utf-8").read().split("\n")
en_al = en[:1955] + en[1956:]
sm = difflib.SequenceMatcher(None, old, en, autojunk=False)
changed = []
for op, i1, i2, j1, j2 in sm.get_opcodes():
    if op in ("replace", "insert"):
        changed.extend(range(j1, j2))
out = []
for j in changed:
    if not en[j].strip():
        continue
    k = j if j < 1955 else j - 1
    out.append(f"### EN {j+1} / ES {k+1}\nEN: {en[j]}\nES: {es[k]}\n")
open(OUT + "new_passages_pairs.txt", "w", encoding="utf-8").write("\n".join(out))
print(len(changed), "changed EN lines;", len(out), "non-blank pairs written")
