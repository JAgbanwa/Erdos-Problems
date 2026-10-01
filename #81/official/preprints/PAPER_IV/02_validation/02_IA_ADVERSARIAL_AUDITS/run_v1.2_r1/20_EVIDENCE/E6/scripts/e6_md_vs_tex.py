"""E6: MD vs TeX within each language: math, identifiers, numbers in plain text."""
import re, json, difflib, collections
D = "C:/Users/jtraverso/e81p4-publish/preprints/PAPER_IV/01_manuscript/v1.2_full_rebuild_candidate/"
OUT = "C:/Users/jtraverso/e81p4-publish/preprints/PAPER_IV/02_validation/02_IA_ADVERSARIAL_AUDITS/run_v1.2_r1/20_EVIDENCE/E6/results/"

def rd(l, k):
    return open(D + f"PAPER_IV_preprint_v1.2_{l}.{k}", encoding="utf-8").read()

def lineno(t, pos):
    return t.count("\n", 0, pos) + 1

def clean_tt(s):
    s = re.sub(r"\\discretionary\{[^{}]*(?:\{[^{}]*(?:\{[^{}]*\}[^{}]*)*\}[^{}]*)*\}\{\}\{\}", "", s)
    s = s.replace("\\allowbreak{}", "").replace("\\allowbreak", "").replace("\\-", "")
    s = re.sub(r"\\textbackslash\{\}", "\\\\", s)
    s = re.sub(r"\\char`\\(.)", r"\1", s)
    s = re.sub(r"\\([_#%&$\{\}])", r"\1", s)
    s = s.replace("\\textasciitilde{}", "~").replace("\\textasciicircum{}", "^")
    s = s.replace("{}", "")
    return s.strip()

def tex_idents(t):
    out = []
    # find {\ttfamily\small ...} with balanced braces
    for mo in re.finditer(r"\{\\ttfamily(?:\\small)?\s?", t):
        i = mo.end(); depth = 1
        while depth and i < len(t):
            if t[i] == "{" and t[i - 1] != "\\": depth += 1
            elif t[i] == "}" and t[i - 1] != "\\": depth -= 1
            i += 1
        out.append((mo.start(), clean_tt(t[mo.end():i - 1])))
    for mo in re.finditer(r"\\(?:texttt|path|nolinkurl)\{([^{}]*)\}", t):
        out.append((mo.start(), clean_tt(mo.group(1))))
    out.sort()
    return [(lineno(t,a),v) for a,v in out]

def md_idents(t):
    return [(lineno(t, mo.start()), mo.group(1)) for mo in re.finditer(r"`([^`\n]+)`", t)]

def math(t, tex):
    pats = [r"\\\[(.+?)\\\]", r"\\\((.+?)\\\)"]
    if tex:
        pats += [r"\\begin\{(?:equation|align|gather)\*?\}(.+?)\\end\{(?:equation|align|gather)\*?\}", r"(?<![\\$])\$([^$]+?)\$"]
    segs, spans = [], []
    for p in pats:
        for mo in re.finditer(p, t, re.S):
            if any(a <= mo.start() < b for a, b in spans): continue
            spans.append((mo.start(), mo.end()))
            segs.append((mo.start(), re.sub(r"\s+", "", mo.group(1))))
    segs.sort()
    return [(lineno(t,a),v) for a,v in segs]

res = {}
for l in ("en", "es"):
    md, tx = rd(l, "md"), rd(l, "tex")
    mi, ti = md_idents(md), tex_idents(tx)
    sm = difflib.SequenceMatcher(None, [v for _, v in mi], [v for _, v in ti], autojunk=False)
    idd = [dict(op=op, md=mi[i1:i2], tex=ti[j1:j2]) for op, i1, i2, j1, j2 in sm.get_opcodes() if op != "equal"]
    mm, tm = math(md, False), math(tx, True)
    sm = difflib.SequenceMatcher(None, [v for _, v in mm], [v for _, v in tm], autojunk=False)
    mdd = [dict(op=op, md=mm[i1:i2][:6], tex=tm[j1:j2][:6]) for op, i1, i2, j1, j2 in sm.get_opcodes() if op != "equal"]
    C=collections.Counter
    res[l+'_ms']=dict(ident_only_md=dict(C(v for _,v in mi)-C(v for _,v in ti)),ident_only_tex=dict(C(v for _,v in ti)-C(v for _,v in mi)),math_only_md=dict(C(v for _,v in mm)-C(v for _,v in tm)),math_only_tex=dict(C(v for _,v in tm)-C(v for _,v in mm)))
    res[l] = dict(n_ident_md=len(mi), n_ident_tex=len(ti), ident_diffs=idd, n_math_md=len(mm), n_math_tex=len(tm), math_diffs=mdd)
    print(l, "idents", len(mi), len(ti), "diffs", len(idd), "| math", len(mm), len(tm), "diffs", len(mdd))
json.dump(res, open(OUT + "md_vs_tex.json", "w", encoding="utf-8"), ensure_ascii=False, indent=1)
