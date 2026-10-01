"""ES lines changed v1.2->v1.21 whose EN counterpart did NOT change (ES-only edits)."""
import difflib
D = "C:/Users/jtraverso/e81p4-publish/preprints/PAPER_IV/01_manuscript/"
r = lambda p: open(D + p, encoding="utf-8").read().split("\n")
oen, oes = r("v1.2_full_rebuild_candidate/PAPER_IV_preprint_v1.2_en.md"), r("v1.2_full_rebuild_candidate/PAPER_IV_preprint_v1.2_es.md")
nen, nes = r("v1.21_editorial_candidate/PAPER_IV_preprint_v1.21_en.md"), r("v1.21_editorial_candidate/PAPER_IV_preprint_v1.21_es.md")
def changed(a, b):
    s = set(); m = {}
    for op, i1, i2, j1, j2 in difflib.SequenceMatcher(None, a, b, autojunk=False).get_opcodes():
        if op == "equal":
            for k in range(j2 - j1): m[j1 + k] = i1 + k
        else:
            s.update(range(j1, j2))
    return s, m
ces, mes = changed(oes, nes)
cen, _ = changed(oen, nen)
cen_al = {j if j < 1955 else j - 1 for j in cen}
out = []
for j in sorted(ces - cen_al):
    if not nes[j].strip(): continue
    old = difflib.get_close_matches(nes[j], oes, n=1, cutoff=0.5)
    out.append(f"### ES {j+1}\nNEW: {nes[j]}\nOLD: {old[0] if old else '(none)'}\n")
open("results/es_only_changes.txt", "w", encoding="utf-8").write("\n".join(out))
print(len(out))
