"""Paragraph-aligned EN/ES token comparison (MD and TeX)."""
import re, json, difflib, sys
D = "C:/Users/jtraverso/e81p4-publish/preprints/PAPER_IV/01_manuscript/v1.21_editorial_candidate/"
OUT = "C:/Users/jtraverso/e81p4-publish/preprints/PAPER_IV/02_validation/02_IA_ADVERSARIAL_AUDITS/run_v1.21_r1/20_EVIDENCE/E6/results/"
kind = sys.argv[1] if len(sys.argv) > 1 else "md"
en = open(D + f"PAPER_IV_preprint_v1.21_en.{kind}", encoding="utf-8").read().split("\n")
es = open(D + f"PAPER_IV_preprint_v1.21_es.{kind}", encoding="utf-8").read().split("\n")
TEXTCMD = re.compile(r"\\(text|textup|textrm|mbox)\s*\{((?:[^{}]|\{[^{}]*\})*)\}")
def toks(l):
    t = {}
    m = TEXTCMD.sub("T", l)
    t["math"] = [re.sub(r"\s+", "", x) for x in re.findall(r"\\\((.+?)\\\)|\$\$(.+?)\$\$", m) for x in x if x] if False else \
        [re.sub(r"\s+", "", a or b) for a, b in re.findall(r"\\\((.+?)\\\)|\$([^$]+)\$", m)]
    if kind == "md":
        t["code"] = re.findall(r"`([^`]+)`", l)
    else:
        t["code"] = [re.sub(r"\\discretionary\{[^{}]*\{[^{}]*\{[^{}]*\}\}\}\{\}\{\}", "", x) for x in re.findall(r"\{\\ttfamily\\small ((?:[^{}]|\{(?:[^{}]|\{(?:[^{}]|\{[^{}]*\})*\})*\})*)\}", l)]
    s = re.sub(r"`[^`]*`|\\\(.+?\\\)|\$[^$]*\$|https?://\S+|\{\\ttfamily.*?\}", " ", l)
    t["num"] = re.findall(r"(?<![\w.])\d+(?:[.,]\d+)*(?:[a-z](?![a-z]))?", s)
    t["url"] = re.findall(r"https?://[^\s)>\]}]+", l)
    t["cite"] = re.findall(r"\[(\d+(?:,\s*\d+)*)\]|\{\[\}(\d+(?:,\s*\d+)*)\{\]\}", l)
    t["sec"] = re.findall(r"§\s?[A-G]?\d+(?:\.\d+)*|\b[A-G]\.\d+[a-z]?\b", s)
    return t
# align by structure signature
def sig(l):
    if kind == "md":
        s = l.lstrip()
        return ("H" + str(len(s) - len(s.lstrip("#")))) if s.startswith("#") else ("B" if not s else ("M" if s.startswith(("\\[", "$$", "\\]", "\\begin", "\\end")) else ("|" if s.startswith("|") else "P")))
    s = l.strip()
    mm = re.match(r"\\(\w+)", s)
    return mm.group(1) if mm else ("B" if not s else "P")
sm = difflib.SequenceMatcher(None, [sig(x) for x in en], [sig(x) for x in es], autojunk=False)
issues, pairs = [], 0
for op, i1, i2, j1, j2 in sm.get_opcodes():
    if op != "equal":
        issues.append({"type": "structure_" + op, "en_lines": [i1 + 1, i2], "es_lines": [j1 + 1, j2],
                       "en": [x[:160] for x in en[i1:i2]], "es": [x[:160] for x in es[j1:j2]]})
        continue
    for a, b in zip(range(i1, i2), range(j1, j2)):
        pairs += 1
        ta, tb = toks(en[a]), toks(es[b])
        for k in ta:
            A, B = ta[k], tb[k]
            if k in ("math", "code", "num", "sec"):
                if sorted(A) != sorted(B):
                    issues.append({"type": k, "en_line": a + 1, "es_line": b + 1,
                                   "only_en": sorted(set(A) - set(B)) or [x for x in A if A.count(x) != B.count(x)],
                                   "only_es": sorted(set(B) - set(A)) or [x for x in B if A.count(x) != B.count(x)]})
            elif A != B:
                issues.append({"type": k, "en_line": a + 1, "es_line": b + 1, "en": A, "es": B})
json.dump({"pairs": pairs, "issues": issues}, open(OUT + f"linealign_{kind}.json", "w", encoding="utf-8"), ensure_ascii=False, indent=1)
print("pairs", pairs, "issues", len(issues))
for x in issues:
    print(json.dumps(x, ensure_ascii=False)[:600])
