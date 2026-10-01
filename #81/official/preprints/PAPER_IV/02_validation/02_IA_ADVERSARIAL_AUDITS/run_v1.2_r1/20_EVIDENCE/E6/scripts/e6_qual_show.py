"""E6: show EN sentences with a qualifier and the aligned ES paragraph, for EN>ES flagged cases."""
import re, json, sys
D = "C:/Users/jtraverso/e81p4-publish/preprints/PAPER_IV/01_manuscript/v1.2_full_rebuild_candidate/"
R = json.load(open("../results/qualifiers.json", encoding="utf-8"))
EN = open(D + "PAPER_IV_preprint_v1.2_en.md", encoding="utf-8").read().split("\n")
ES = open(D + "PAPER_IV_preprint_v1.2_es.md", encoding="utf-8").read().split("\n")
PAT = {"explicit": r"explicit", "fixed": r"\bfixed\b", "not_claimed": r"claim|assert", "at_most": r"at most|up to|no more than", "strict": r"strict", "three": r"\bthree\b", "eventual": r"eventual"}
ESP = {"explicit": r"explícit", "fixed": r"fij", "not_claimed": r"reclam|afirm", "at_most": r"a lo sumo|hasta|máximo", "strict": r"estrict", "three": r"\btres\b|3", "eventual": r"eventual|grande"}
def para(L, s):
    out = []
    i = s - 1
    while i < len(L) and L[i].strip():
        out.append(L[i]); i += 1
    return " ".join(out)
for f in R["flags"]:
    for k, (ce, cs) in f["diff"].items():
        if k in PAT and ce > cs:
            a, b = para(EN, f["en_line"]), para(ES, f["es_line"])
            sa = [s for s in re.split(r"(?<=[.;])\s+", a) if re.search(PAT[k], s, re.I)]
            sb = [s for s in re.split(r"(?<=[.;])\s+", b) if re.search(ESP[k], s, re.I)]
            print(f"### EN {f['en_line']} / ES {f['es_line']}  [{k} {ce}->{cs}]")
            for s in sa: print("  EN:", s[:400])
            for s in sb: print("  ES:", s[:400])
