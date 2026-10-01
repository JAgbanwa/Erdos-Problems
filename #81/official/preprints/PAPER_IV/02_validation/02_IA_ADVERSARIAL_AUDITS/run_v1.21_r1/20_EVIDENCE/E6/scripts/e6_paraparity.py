"""Paragraph-level EN/ES parity: sentence counts and length ratios on aligned MD lines."""
import re, json, statistics
D = "C:/Users/jtraverso/e81p4-publish/preprints/PAPER_IV/01_manuscript/v1.21_editorial_candidate/"
OUT = "C:/Users/jtraverso/e81p4-publish/preprints/PAPER_IV/02_validation/02_IA_ADVERSARIAL_AUDITS/run_v1.21_r1/20_EVIDENCE/E6/results/"
en = open(D + "PAPER_IV_preprint_v1.21_en.md", encoding="utf-8").read().split("\n")
es = open(D + "PAPER_IV_preprint_v1.21_es.md", encoding="utf-8").read().split("\n")
# EN has one extra blank line at 1955 (1-based); align by removing it
assert en[1954].strip() == "" and en[1955].strip() == ""
en_al = en[:1955] + en[1956:]
assert len(en_al) == len(es)
def strip(l):
    l = re.sub(r"`[^`]*`", "C", l)
    l = re.sub(r"\\\(.+?\\\)", "M", l)
    l = re.sub(r"https?://\S+", "U", l)
    return l
def nsent(l):
    s = strip(l)
    s = re.sub(r"\b(e\.g|i\.e|cf|vs|Fig|Thm|et al|resp|p|pp|vol|No|núm|pág|Ed|ed|Proc|J|Math|Ann|Comb|Prob|Comput|Sci|Soc|Amer|Natl|Acad|Discrete|Algorithms|Struct|Random|Lemma|Lema)\.", r"\1", s)
    s = re.sub(r"\b[A-Z]\.", "X", s)  # initials
    s = re.sub(r"\d\.\d", "N", s)
    return len(re.findall(r"[.!?](\s|$)", s))
rows = []
ratios = []
for i, (a, b) in enumerate(zip(en_al, es)):
    if len(a.strip()) < 80 or a.startswith(("|", "#", "\\", "$$", "```")):
        continue
    la, lb = len(strip(a)), len(strip(b))
    r = lb / max(la, 1)
    ratios.append(r)
    sa, sb = nsent(a), nsent(b)
    rows.append({"es_line": i + 1, "en_len": la, "es_len": lb, "ratio": round(r, 3), "en_sent": sa, "es_sent": sb})
med = statistics.median(ratios)
flag = [x for x in rows if x["ratio"] < 0.93 or x["ratio"] > 1.45 or x["es_sent"] < x["en_sent"] - 0]
json.dump({"median_ratio": med, "n": len(rows), "flagged": flag}, open(OUT + "para_parity.json", "w", encoding="utf-8"), indent=1)
print("paragraphs", len(rows), "median ES/EN length ratio", round(med, 3), "flagged", len(flag))
for x in flag:
    print(x)
