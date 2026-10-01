"""E6: EN vs ES token-class comparison for MD (and TeX). Read-only on targets."""
import re, json, sys, difflib, collections
D = "C:/Users/jtraverso/e81p4-publish/preprints/PAPER_IV/01_manuscript/v1.2_full_rebuild_candidate/"
OUT = "C:/Users/jtraverso/e81p4-publish/preprints/PAPER_IV/02_validation/02_IA_ADVERSARIAL_AUDITS/run_v1.2_r1/20_EVIDENCE/E6/results/"
kind = sys.argv[1] if len(sys.argv) > 1 else "md"

def load(lang):
    with open(D + f"PAPER_IV_preprint_v1.2_{lang}.{kind}", encoding="utf-8") as f:
        return f.read()

def norm_math(m):
    # drop translatable \text{...}, \mathrm{words}, spaces
    m = re.sub(r"\\(?:text|textrm|textup|mathrm|operatorname|mbox)\s*\{([^{}]*)\}", lambda g: "\\T{" + ("" if re.search(r"[A-Za-zÁÉÍÓÚáéíóúñ]{3,}", g.group(1)) and not re.match(r"^[a-z]{1,4}$", g.group(1)) else g.group(1)) + "}", m)
    m = re.sub(r"\s+", "", m)
    return m

def math_segments(txt):
    """Return list of (lineno, type, content)."""
    segs = []
    if kind == "md":
        pats = [(r"\\\[(.+?)\\\]", "D"), (r"\\\((.+?)\\\)", "I")]
    else:
        pats = [(r"\\\[(.+?)\\\]", "D"), (r"\\begin\{(equation\*?|align\*?|gather\*?|multline\*?)\}(.+?)\\end\{\1\}", "E"), (r"\\\((.+?)\\\)", "I"), (r"(?<![\\$])\$([^$]+?)\$", "I")]
    spans = []
    for p, t in pats:
        for mo in re.finditer(p, txt, re.S):
            if any(a <= mo.start() < b for a, b in spans):
                continue
            spans.append((mo.start(), mo.end()))
            content = mo.group(mo.lastindex)
            segs.append((txt.count("\n", 0, mo.start()) + 1, t, content))
    segs.sort()
    return segs, spans

def strip_math(txt, spans):
    out = list(txt)
    for a, b in spans:
        for i in range(a, b):
            if out[i] != "\n":
                out[i] = " "
    return "".join(out)

res = {}
T = {l: load(l) for l in ("en", "es")}
S = {}
for l in T:
    segs, spans = math_segments(T[l])
    S[l] = dict(segs=segs, plain=strip_math(T[l], spans))

# ---- 1. math sequence comparison
a = [norm_math(c) for _, _, c in S["en"]["segs"]]
b = [norm_math(c) for _, _, c in S["es"]["segs"]]
sm = difflib.SequenceMatcher(None, a, b, autojunk=False)
math_diffs = []
for op, i1, i2, j1, j2 in sm.get_opcodes():
    if op == "equal":
        continue
    math_diffs.append(dict(op=op,
        en=[(S["en"]["segs"][i][0], S["en"]["segs"][i][2].strip()[:300]) for i in range(i1, i2)],
        es=[(S["es"]["segs"][j][0], S["es"]["segs"][j][2].strip()[:300]) for j in range(j1, j2)]))
res["math_counts"] = {l: len(S[l]["segs"]) for l in S}
res["math_diffs"] = math_diffs

# ---- 2. per-class token extraction from plain text (outside math)
def lines_of(txt):
    return txt.split("\n")

classes = {
    "backtick": r"`([^`\n]+)`",
    "url": r"https?://[^\s)>\]}]+",
    "hash": r"\b[0-9a-f]{12,64}\b|piv-v12-[0-9a-f]+",
    "cite": r"\[(\d[\d,\s–\-]*(?:,\s*[^\]]{0,60})?)\]",
    "number": r"(?<![\w.])\d+(?:[.,]\d+)*(?![\w])",
    "eqref": r"\((?:\d+\.\d+[a-z]?|[A-G]\.\d+[a-z]?|[A-C]′?|A|B|C)\)",
    "thmref": r"(?:Theorem|Teorema|Lemma|Lema|Corollary|Corolario|Proposition|Proposición|Definition|Definición|Remark|Observación|Section|Sección|Appendix|Apéndice|Table|Tabla|Figure|Figura|Example|Ejemplo|Conjecture|Conjetura)s?\s+([A-G]?\d*(?:\.\d+)*[a-z]?′?)",
    "sect": r"§\s?[\dA-G][\d.]*[a-z]?",
    "tt": r"\\texttt\{([^{}]+)\}|\\path\{([^{}]+)\}|\\url\{([^{}]+)\}|\\nolinkurl\{([^{}]+)\}",
}
LANGWORD = {"Theorem": "T", "Teorema": "T", "Theorems": "T", "Teoremas": "T", "Lemma": "L", "Lema": "L", "Lemmas": "L", "Lemas": "L",
            "Corollary": "C", "Corolario": "C", "Corollaries": "C", "Corolarios": "C", "Proposition": "P", "Proposición": "P", "Propositions": "P", "Proposiciones": "P",
            "Definition": "Df", "Definición": "Df", "Remark": "R", "Observación": "R", "Section": "S", "Sección": "S", "Sections": "S", "Secciones": "S",
            "Appendix": "A", "Apéndice": "A", "Table": "Tb", "Tabla": "Tb", "Figure": "F", "Figura": "F", "Example": "E", "Ejemplo": "E", "Conjecture": "Cj", "Conjetura": "Cj"}

def extract(l, cls):
    txt = S[l]["plain"] if cls not in ("backtick", "url", "hash", "tt") else T[l]
    out = []
    for n, line in enumerate(lines_of(txt), 1):
        for mo in re.finditer(classes[cls], line):
            if cls == "thmref":
                w = mo.group(0).split()[0]
                w2 = re.sub(r"s$", "", w) if w not in LANGWORD else w
                out.append((n, LANGWORD.get(w, LANGWORD.get(w2, w)) + ":" + mo.group(1)))
            elif cls == "tt":
                out.append((n, next(g for g in mo.groups() if g)))
            elif cls == "cite":
                c = mo.group(1)
                c = (c.replace("Teorema", "Theorem").replace("Lema", "Lemma").replace("Corolario", "Corollary")
                       .replace("Proposición", "Proposition").replace("Observación", "Remark").replace("Sección", "Section")
                       .replace("Definición", "Definition").replace("Apéndice", "Appendix").replace("Tabla", "Table")
                       .replace("Ejemplo", "Example").replace("Conjetura", "Conjecture"))
                out.append((n, re.sub(r"\s+", " ", c)))
            else:
                out.append((n, mo.group(0) if mo.lastindex is None else mo.group(1)))
    return out

tok = {}
for cls in classes:
    ea, eb = extract("en", cls), extract("es", cls)
    ca, cb = collections.Counter(v for _, v in ea), collections.Counter(v for _, v in eb)
    only_en = {k: v - cb.get(k, 0) for k, v in ca.items() if v > cb.get(k, 0)}
    only_es = {k: v - ca.get(k, 0) for k, v in cb.items() if v > ca.get(k, 0)}
    # sequence diff with line numbers
    sm = difflib.SequenceMatcher(None, [v for _, v in ea], [v for _, v in eb], autojunk=False)
    seq = []
    for op, i1, i2, j1, j2 in sm.get_opcodes():
        if op != "equal":
            seq.append(dict(op=op, en=ea[i1:i2], es=eb[j1:j2]))
    tok[cls] = dict(n_en=len(ea), n_es=len(eb), only_en=only_en, only_es=only_es, seqdiff=seq)
res["tokens"] = tok

# ---- 3. headings (MD) / sectioning (TeX)
if kind == "md":
    hp = r"^(#{1,6})\s+(.*)$"
else:
    hp = r"^\\(section|subsection|subsubsection|paragraph)\*?\{(.*)\}"
H = {}
for l in T:
    H[l] = [(n, mo.group(1), mo.group(2)) for n, line in enumerate(lines_of(T[l]), 1) for mo in [re.match(hp, line)] if mo]
def headkey(h):
    m = re.match(r"^(?:[A-Za-zÁÉÍÓÚáéíóúñ]+\s+)?([A-G]?\d*(?:\.\d+)*[a-z]?′?)\.?", h)
    return m.group(1) if m else ""
hd = []
for i in range(max(len(H["en"]), len(H["es"]))):
    e = H["en"][i] if i < len(H["en"]) else None
    s = H["es"][i] if i < len(H["es"]) else None
    ke = (e[1], headkey(e[2])) if e else None
    ks = (s[1], headkey(s[2])) if s else None
    if ke != ks:
        hd.append(dict(idx=i, en=e, es=s))
res["headings"] = dict(n_en=len(H["en"]), n_es=len(H["es"]), mismatches=hd, en=H["en"], es=H["es"])

# ---- 4. line-aligned numeric check: for aligned blocks, per line digit multiset
LA, LB = lines_of(S["en"]["plain"]), lines_of(S["es"]["plain"])
def sig(x):
    return re.sub(r"\s+", "", x)[:0]
sm = difflib.SequenceMatcher(None, [bool(x.strip()) for x in LA], [bool(x.strip()) for x in LB], autojunk=False)
line_num = []
MONTHS = {}
for op, i1, i2, j1, j2 in sm.get_opcodes():
    if op == "equal":
        for k in range(i2 - i1):
            na = collections.Counter(re.findall(r"(?<![\w])\d+(?:[.,]\d+)*", LA[i1 + k]))
            nb = collections.Counter(re.findall(r"(?<![\w])\d+(?:[.,]\d+)*", LB[j1 + k]))
            if na != nb:
                line_num.append(dict(en_line=i1 + k + 1, es_line=j1 + k + 1,
                                     only_en=dict(na - nb), only_es=dict(nb - na),
                                     en=LA[i1 + k].strip()[:260], es=LB[j1 + k].strip()[:260]))
    else:
        line_num.append(dict(op=op, en_lines=[i1 + 1, i2], es_lines=[j1 + 1, j2]))
res["line_numeric"] = line_num

json.dump(res, open(OUT + f"compare_{kind}.json", "w", encoding="utf-8"), ensure_ascii=False, indent=1)
print("math", res["math_counts"], "diffs", len(math_diffs))
for cls in tok:
    print(cls, tok[cls]["n_en"], tok[cls]["n_es"], "onlyEN", tok[cls]["only_en"], "onlyES", tok[cls]["only_es"])
print("headings", res["headings"]["n_en"], res["headings"]["n_es"], "mismatch", len(hd))
print("line_numeric issues", len(line_num))
