"""E6: word-level MD vs TeX diff per language (math and markup stripped)."""
import re, json, difflib
D = "C:/Users/jtraverso/e81p4-publish/preprints/PAPER_IV/01_manuscript/v1.2_full_rebuild_candidate/"
OUT = "C:/Users/jtraverso/e81p4-publish/preprints/PAPER_IV/02_validation/02_IA_ADVERSARIAL_AUDITS/run_v1.2_r1/20_EVIDENCE/E6/results/"

def rd(l, k):
    return open(D + f"PAPER_IV_preprint_v1.2_{l}.{k}", encoding="utf-8").read()

def words_md(t):
    t = re.sub(r"\\\[.+?\\\]", " MATH ", t, flags=re.S)
    t = re.sub(r"\\\(.+?\\\)", " MATH ", t, flags=re.S)
    t = re.sub(r"!\[(.*?)\]\((.*?)\)", r" \1 ", t, flags=re.S)
    t = re.sub(r"\[([^\]]*)\]\((http[^)]*)\)", r"\1", t)
    t = re.sub(r"[`*#|>_]", " ", t)
    return tok(t)

def words_tex(t):
    b = t.find("\\begin{document}")
    t = t[b:] if b >= 0 else t
    t = re.sub(r"(?<!\\)%.*", "", t)
    t = re.sub(r"\\discretionary\{[^{}]*(?:\{[^{}]*(?:\{[^{}]*\}[^{}]*)*\}[^{}]*)*\}\{\}\{\}", "", t)
    t = re.sub(r"\\\[.+?\\\]", " MATH ", t, flags=re.S)
    t = re.sub(r"\\begin\{(equation|align|gather)\*?\}.+?\\end\{\1\*?\}", " MATH ", t, flags=re.S)
    t = re.sub(r"\\\(.+?\\\)", " MATH ", t, flags=re.S)
    t = re.sub(r"(?<![\\$])\$[^$]+?\$", " MATH ", t)
    t = re.sub(r"\\(label|ref|includegraphics|hypertarget|begin|end|url|href|protect|pandocbounded|def|setlength|addcontentsline|phantomsection|bibitem|cite)\*?(\[[^\]]*\])?\{[^{}]*\}", " ", t)
    t = t.replace("``", "\"").replace("''", "\"").replace("~", " ").replace("\\&", "&").replace("\\%", "%").replace("\\#", "#").replace("\\_", "_")
    t = re.sub(r"\\[A-Za-z]+\*?", " ", t)
    t = re.sub(r"[{}\[\]_|&]", " ", t)
    return tok(t)

def tok(t):
    t = t.replace("“", "\"").replace("”", "\"").replace("’", "'").replace("‘", "'").replace("«", "\"").replace("»", "\"")
    return [w for w in re.findall(r"[\wÁÉÍÓÚÜÑáéíóúüñ′'’\-–—.,;:()/§\"]+", t) if w not in (".", ",", ";", ":", "(", ")", "-", "\"")]

res = {}
for l in ("en", "es"):
    a, b = words_md(rd(l, "md")), words_tex(rd(l, "tex"))
    a = [re.sub(r"[.,;:()\"]+$|^[\"(]+", "", w) for w in a]
    b = [re.sub(r"[.,;:()\"]+$|^[\"(]+", "", w) for w in b]
    a = [w for w in a if w]; b = [w for w in b if w]
    sm = difflib.SequenceMatcher(None, a, b, autojunk=False)
    diffs = []
    for op, i1, i2, j1, j2 in sm.get_opcodes():
        if op == "equal":
            continue
        diffs.append(dict(op=op, md=" ".join(a[i1:i2])[:300], tex=" ".join(b[j1:j2])[:300], ctx=" ".join(a[max(0, i1 - 8):i1])))
    res[l] = dict(n_md=len(a), n_tex=len(b), ratio=sm.ratio(), n_diffs=len(diffs), diffs=diffs)
    print(l, len(a), len(b), round(sm.ratio(), 4), len(diffs))
json.dump(res, open(OUT + "md_tex_words.json", "w", encoding="utf-8"), ensure_ascii=False, indent=1)
