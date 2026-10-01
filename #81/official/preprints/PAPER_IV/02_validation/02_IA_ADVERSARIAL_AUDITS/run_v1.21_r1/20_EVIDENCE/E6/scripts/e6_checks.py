"""E6 targeted checks: refs, numbers, holgura, English words in ES, code-formatted ordinary words."""
import re, collections, json
D = "C:/Users/jtraverso/e81p4-publish/preprints/PAPER_IV/01_manuscript/v1.21_editorial_candidate/"
P = "C:/Users/jtraverso/e81p4-publish/preprints/PAPER_IV/01_manuscript/v1.2_full_rebuild_candidate/"
OUT = "C:/Users/jtraverso/e81p4-publish/preprints/PAPER_IV/02_validation/02_IA_ADVERSARIAL_AUDITS/run_v1.21_r1/20_EVIDENCE/E6/results/"
T = {k: open(D + f"PAPER_IV_preprint_v1.21_{k}", encoding="utf-8").read() for k in ["en.md", "es.md", "en.tex", "es.tex"]}
T["old_en.md"] = open(P + "PAPER_IV_preprint_v1.2_en.md", encoding="utf-8").read()
T["old_es.md"] = open(P + "PAPER_IV_preprint_v1.2_es.md", encoding="utf-8").read()
L = {k: v.split("\n") for k, v in T.items()}
out = {}

def nocode_md(line):
    return re.sub(r"`[^`]*`", " ", line)

def mathless(line):
    line = re.sub(r"\\\((.+?)\\\)", " ", line)
    line = re.sub(r"\$[^$]*\$", " ", line)
    return line

# 1. cross-reference inventories
refpat = {
    "sec": r"§\s?([A-G]?\d+(?:\.\d+)*[a-z]?)",
    "thm_en": r"\b(Theorem|Lemma|Corollary|Proposition|Figure|Table|Appendix|Remark|Definition)\s+([A-G]?\d*[′']?(?:\.\d+[a-z]?)*|[A-G]′?)",
    "thm_es": r"\b(Teorema|Lema|Corolario|Proposición|Figura|Tabla|Apéndice|Observación|Definición)\s+([A-G]?\d*[′']?(?:\.\d+[a-z]?)*|[A-G]′?)",
    "eq": r"\(((?:[A-G]\.)?\d+\.\d+[a-z]?|[A-G]\.\d+[a-z]?)\)",
}
MAP = {"Teorema": "Theorem", "Lema": "Lemma", "Corolario": "Corollary", "Proposición": "Proposition", "Figura": "Figure",
       "Tabla": "Table", "Apéndice": "Appendix", "Observación": "Remark", "Definición": "Definition"}
for kind in ["md", "tex"]:
    en, es = T["en." + kind], T["es." + kind]
    r = {}
    for nm in ["sec", "eq"]:
        a = collections.Counter(re.findall(refpat[nm], en)); b = collections.Counter(re.findall(refpat[nm], es))
        r[nm] = {k: [a.get(k, 0), b.get(k, 0)] for k in set(a) | set(b) if a.get(k, 0) != b.get(k, 0)}
    a = collections.Counter(f"{x} {y}" for x, y in re.findall(refpat["thm_en"], en))
    b = collections.Counter(f"{MAP[x]} {y}" for x, y in re.findall(refpat["thm_es"], es))
    r["named"] = {k: [a.get(k, 0), b.get(k, 0)] for k in set(a) | set(b) if a.get(k, 0) != b.get(k, 0)}
    out["refs_" + kind] = r

# 2. key numbers
keys = ["33\\delta", "138\\delta", "11\\delta", "23\\delta", "2208", "59485", "a_0+31", "a0+31", "191424", "12748", "12749", "392",
        "\\rho/40", "\\rho/200", "10^{10}", "n/9", "4n/10^4", "10^4", "2^{-59485}", "\\rho/40", "Z=191424"]
kn = {}
for k in keys:
    kn[k] = {f: T[f].count(k) for f in ["en.md", "es.md", "en.tex", "es.tex", "old_en.md"]}
out["key_numbers"] = kn
# where do they occur (line numbers) in en/es md
kl = {}
for k in keys:
    kl[k] = {f: [i + 1 for i, l in enumerate(L[f]) if k in l] for f in ["en.md", "es.md"]}
out["key_number_lines"] = kl

# 3. holgura / margen
h = {}
for f in ["es.md", "es.tex", "old_es.md"]:
    h[f] = [(i + 1, l.strip()[:220]) for i, l in enumerate(L[f]) if re.search(r"holgura", l, re.I)]
out["holgura"] = h

# 4. English words in ES prose outside code/math
EW = ["baseline", "build", "builds", "packing", "packings", "target", "targets", "log", "logs", "gap", "gaps", "slack", "cleanup",
      "wrapper", "wrappers", "checker", "output", "input", "script", "scripts", "commit", "hash", "prefix", "cut", "release",
      "audit", "sorry", "axiom", "gate", "bridge", "adapter", "near", "far", "matching", "the", "and", "of", "with", "for",
      "proof", "bound", "default", "fallback", "pipeline", "framework", "checkpoint", "seed", "benchmark", "dataset", "overall",
      "workflow", "tooling", "upstream", "downstream", "trade-off", "subset", "snapshot"]
ew = collections.defaultdict(list)
inblock = False
for i, l in enumerate(L["es.md"]):
    if l.strip().startswith("```"):
        inblock = not inblock; continue
    if inblock:
        continue
    s = mathless(nocode_md(l))
    s = re.sub(r"https?://\S+", " ", s)
    for w in EW:
        for m in re.finditer(r"(?<![\w\-/.])" + re.escape(w) + r"(?![\w\-/])", s, re.I):
            ew[w].append((i + 1, s[max(0, m.start() - 60):m.end() + 60].strip()))
out["english_in_es"] = dict(ew)
# same in ES tex outside \texttt and verbatim
ewt = collections.defaultdict(list)
inv = False
for i, l in enumerate(L["es.tex"]):
    if re.search(r"\\begin\{(verbatim|Verbatim|lstlisting|Highlighting)\}", l): inv = True
    if re.search(r"\\end\{(verbatim|Verbatim|lstlisting|Highlighting)\}", l): inv = False; continue
    if inv: continue
    s = re.sub(r"\\(texttt|lean|nolinkurl|url|href|LeanName|path|leanid|LeanId|passthrough|code|NormalTok|VerbatimStringTok)\{((?:[^{}]|\{[^{}]*\})*)\}", " ", l)
    s = mathless(s)
    for w in EW:
        for m in re.finditer(r"(?<![\w\-/.\\])" + re.escape(w) + r"(?![\w\-/])", s, re.I):
            ewt[w].append((i + 1, s[max(0, m.start() - 60):m.end() + 60].strip()))
out["english_in_es_tex"] = dict(ewt)

# 5. code-formatted ordinary words: backtick spans consisting of a single capitalised/lower dictionary-like word
def spans(txt):
    res = []
    for i, l in enumerate(txt.split("\n")):
        for m in re.finditer(r"`([^`]+)`", l):
            res.append((i + 1, m.group(1), l))
    return res
single = {}
for f in ["en.md", "es.md", "old_en.md", "old_es.md"]:
    c = collections.Counter(s for _, s, _ in spans(T[f]) if re.fullmatch(r"[A-Za-z][a-z]+", s))
    single[f] = dict(c)
out["single_word_code_spans"] = single
# headings containing code spans
hd = {}
for f in ["en.md", "es.md", "old_en.md", "old_es.md"]:
    hd[f] = [(i + 1, l) for i, l in enumerate(L[f]) if l.startswith("#") and "`" in l]
out["headings_with_code"] = hd
# words in code in one language but plain in the other (per line, lines aligned approximately)
cross = []
for f1, f2 in [("en.md", "es.md"), ("es.md", "en.md"), ("en.md", "old_en.md"), ("es.md", "old_es.md")]:
    for ln, s, l in spans(T[f1]):
        if not re.fullmatch(r"[A-Za-z][A-Za-z]+", s):
            continue
        # look at same neighbourhood in f2
        lo, hi = max(0, ln - 6), ln + 6
        seg = "\n".join(L[f2][lo:hi])
        if s in seg and ("`" + s + "`") not in seg:
            cross.append({"file": f1, "line": ln, "word": s, "other": f2, "ctx": l.strip()[:200]})
out["code_vs_plain"] = cross
# 6. §3.2 in A.2 and anywhere
out["sec3_2"] = {f: [(i + 1, l.strip()[:200]) for i, l in enumerate(L[f]) if "§3.2" in l or "§ 3.2" in l or "S3.2" in l] for f in ["en.md", "es.md", "en.tex", "es.tex", "old_en.md"]}
# 7. C′ and prime notation
out["prime"] = {f: {"C′": T[f].count("C′"), "C'": len(re.findall(r"\bC'(?!')", T[f])), "C^\\prime": T[f].count("C^\\prime"), "C^{\\prime}": T[f].count("C^{\\prime}")} for f in ["en.md", "es.md", "en.tex", "es.tex"]}
json.dump(out, open(OUT + "checks.json", "w", encoding="utf-8"), ensure_ascii=False, indent=1)
for k in ["refs_md", "refs_tex", "key_numbers", "sec3_2", "prime", "headings_with_code", "single_word_code_spans"]:
    print("##", k); print(json.dumps(out[k], ensure_ascii=False))
print("## holgura"); [print(f, x) for f in out["holgura"] for x in out["holgura"][f]]
print("## english_in_es (md)"); [print(w, len(v), v[:6]) for w, v in out["english_in_es"].items()]
print("## english_in_es_tex"); [print(w, len(v), v[:3]) for w, v in out["english_in_es_tex"].items()]
print("## code_vs_plain"); [print(x) for x in out["code_vs_plain"]]
