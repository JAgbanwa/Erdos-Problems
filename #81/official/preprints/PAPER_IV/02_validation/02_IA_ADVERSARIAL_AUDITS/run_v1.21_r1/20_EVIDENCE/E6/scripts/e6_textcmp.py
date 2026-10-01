"""E6: EN vs ES and MD vs TeX consistency extraction (read-only on targets)."""
import re, json, difflib, sys, collections, os
D = "C:/Users/jtraverso/e81p4-publish/preprints/PAPER_IV/01_manuscript/v1.21_editorial_candidate/"
OUT = "C:/Users/jtraverso/e81p4-publish/preprints/PAPER_IV/02_validation/02_IA_ADVERSARIAL_AUDITS/run_v1.21_r1/20_EVIDENCE/E6/results/"
F = {k: D + f"PAPER_IV_preprint_v1.21_{k}" for k in ["en.md", "es.md", "en.tex", "es.tex"]}
T = {k: open(v, encoding="utf-8").read() for k, v in F.items()}

def lineno(txt, pos):
    return txt.count("\n", 0, pos) + 1

def strip_code(txt, kind):
    # blank out fenced code / verbatim so $ inside code is ignored; keep length
    if kind == "md":
        pat = re.compile(r"```.*?```", re.S)
    else:
        pat = re.compile(r"\\begin\{(verbatim|lstlisting|Verbatim|minted)\}.*?\\end\{\1\}", re.S)
    return pat.sub(lambda m: re.sub(r"[^\n]", " ", m.group(0)), txt)

def math_segments(txt, kind):
    t = strip_code(txt, kind)
    if kind == "md":
        t = re.sub(r"`[^`\n]*`", lambda m: " " * len(m.group(0)), t)
    segs = []
    pats = [r"\$\$(.+?)\$\$", r"\\\[(.+?)\\\]",
            r"\\begin\{(equation\*?|align\*?|gather\*?|multline\*?)\}(.+?)\\end\{\1\}"]
    used = [False] * len(t)
    for p in pats:
        for m in re.finditer(p, t, re.S):
            if any(used[m.start():m.end()]):
                continue
            body = m.group(m.lastindex)
            segs.append((m.start(), "D", body))
            for i in range(m.start(), m.end()):
                used[i] = True
    t2 = "".join(" " if used[i] else c for i, c in enumerate(t))
    for m in re.finditer(r"(?<!\\)\$(.+?)(?<!\\)\$", t2, re.S):
        segs.append((m.start(), "I", m.group(1)))
    for m in re.finditer(r"\\\((.+?)\\\)", t2, re.S):
        segs.append((m.start(), "I", m.group(1)))
    segs.sort()
    return [(lineno(txt, p), k, b) for p, k, b in segs]

TEXTCMD = re.compile(r"\\(text|textup|textrm|textit|mbox|textnormal|intertext)\s*\{((?:[^{}]|\{[^{}]*\})*)\}")
def norm(b):
    words = [m.group(2) for m in TEXTCMD.finditer(b)]
    b = TEXTCMD.sub(r"\\\1{#}", b)
    b = re.sub(r"\s+", "", b)
    return b, words

res = {}
for kind in ["md", "tex"]:
    en = math_segments(T["en." + kind], kind)
    es = math_segments(T["es." + kind], kind)
    en_n = [norm(b)[0] for _, _, b in en]
    es_n = [norm(b)[0] for _, _, b in es]
    sm = difflib.SequenceMatcher(None, en_n, es_n, autojunk=False)
    diffs = []
    for op, i1, i2, j1, j2 in sm.get_opcodes():
        if op == "equal":
            continue
        diffs.append({"op": op,
                      "en": [(en[i][0], en[i][2][:300]) for i in range(i1, i2)],
                      "es": [(es[j][0], es[j][2][:300]) for j in range(j1, j2)]})
    # text-word pairs for equal segments (translation check)
    textpairs = collections.Counter()
    for op, i1, i2, j1, j2 in sm.get_opcodes():
        if op == "equal":
            for a, b in zip(range(i1, i2), range(j1, j2)):
                wa, wb = norm(en[a][2])[1], norm(es[b][2])[1]
                for x, y in zip(wa, wb):
                    textpairs[(x.strip(), y.strip())] += 1
    res[kind] = {"n_en": len(en), "n_es": len(es), "n_diff_blocks": len(diffs), "diffs": diffs,
                 "text_pairs": sorted([[a, b, c] for (a, b), c in textpairs.items()], key=lambda r: -r[2])}

# MD vs TeX within language: compare normalized math multisets
def md2texnorm(b):
    b, _ = norm(b)
    return b
mt = {}
for lang in ["en", "es"]:
    a = collections.Counter(md2texnorm(b) for _, _, b in math_segments(T[lang + ".md"], "md"))
    c = collections.Counter(md2texnorm(b) for _, _, b in math_segments(T[lang + ".tex"], "tex"))
    only_md = list((a - c).elements()); only_tex = list((c - a).elements())
    mt[lang] = {"n_md": sum(a.values()), "n_tex": sum(c.values()),
                "only_md": only_md, "only_tex": only_tex}
res["md_vs_tex"] = mt

# token inventories
def inv(txt, kind):
    d = {}
    d["tags"] = re.findall(r"\\tag\*?\{([^}]*)\}", txt)
    d["urls"] = sorted(set(re.findall(r"https?://[^\s)>\]}\"'`\\]+", txt)))
    d["hex"] = sorted(set(re.findall(r"\b[0-9a-f]{12,64}\b", txt)))
    d["cites"] = collections.Counter(re.findall(r"\[(\d+(?:[,–-]\s*\d+)*)\]", txt)) if kind == "md" else collections.Counter(re.findall(r"\\cite[pt]?\{([^}]*)\}", txt))
    if kind == "md":
        d["code"] = collections.Counter(re.findall(r"`([^`\n]+)`", strip_code(txt, "md")))
    else:
        d["code"] = collections.Counter(re.findall(r"\\(?:texttt|lean|code|path|nolinkurl|LeanId|leanid)\{((?:[^{}]|\{[^{}]*\})*)\}", txt))
    d["nums"] = collections.Counter(re.findall(r"(?<![\w.])\d[\d,.]*\d|(?<![\w.])\d(?![\w])", re.sub(r"https?://\S+", "", txt)))
    return d
I = {k: inv(T[k], k.split(".")[1]) for k in T}
cmp = {}
for kind in ["md", "tex"]:
    a, b = I["en." + kind], I["es." + kind]
    c = {}
    c["tags_equal"] = a["tags"] == b["tags"]
    c["tags_en"] = a["tags"]; c["tags_es"] = b["tags"]
    c["urls_only_en"] = sorted(set(a["urls"]) - set(b["urls"])); c["urls_only_es"] = sorted(set(b["urls"]) - set(a["urls"]))
    c["hex_only_en"] = sorted(set(a["hex"]) - set(b["hex"])); c["hex_only_es"] = sorted(set(b["hex"]) - set(a["hex"]))
    c["cites_diff"] = {k: [a["cites"].get(k, 0), b["cites"].get(k, 0)] for k in set(a["cites"]) | set(b["cites"]) if a["cites"].get(k, 0) != b["cites"].get(k, 0)}
    c["code_diff"] = {k: [a["code"].get(k, 0), b["code"].get(k, 0)] for k in set(a["code"]) | set(b["code"]) if a["code"].get(k, 0) != b["code"].get(k, 0)}
    c["n_code_en"] = sum(a["code"].values()); c["n_code_es"] = sum(b["code"].values())
    c["nums_diff"] = {k: [a["nums"].get(k, 0), b["nums"].get(k, 0)] for k in set(a["nums"]) | set(b["nums"]) if a["nums"].get(k, 0) != b["nums"].get(k, 0)}
    cmp[kind] = c
res["inventories"] = cmp
json.dump(res, open(OUT + "textcmp.json", "w", encoding="utf-8"), ensure_ascii=False, indent=1, default=list)
for kind in ["md", "tex"]:
    print(kind, "math segs", res[kind]["n_en"], res[kind]["n_es"], "diff blocks", res[kind]["n_diff_blocks"])
for lang in ["en", "es"]:
    print("md_vs_tex", lang, mt[lang]["n_md"], mt[lang]["n_tex"], len(mt[lang]["only_md"]), len(mt[lang]["only_tex"]))
for kind in ["md", "tex"]:
    c = cmp[kind]
    print(kind, "tags_equal", c["tags_equal"], len(c["tags_en"]), len(c["tags_es"]), "urls", c["urls_only_en"], c["urls_only_es"], "hex", c["hex_only_en"], c["hex_only_es"])
    print(" cites_diff", c["cites_diff"])
    print(" code n", c["n_code_en"], c["n_code_es"], "code_diff", len(c["code_diff"]))
    print(" nums_diff", len(c["nums_diff"]))
