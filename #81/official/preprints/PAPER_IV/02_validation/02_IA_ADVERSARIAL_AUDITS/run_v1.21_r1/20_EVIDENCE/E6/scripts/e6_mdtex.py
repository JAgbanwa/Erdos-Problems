"""MD vs TeX within each language: code identifiers, numbers, cites, words."""
import re, collections, json
D = "C:/Users/jtraverso/e81p4-publish/preprints/PAPER_IV/01_manuscript/v1.21_editorial_candidate/"
OUT = "C:/Users/jtraverso/e81p4-publish/preprints/PAPER_IV/02_validation/02_IA_ADVERSARIAL_AUDITS/run_v1.21_r1/20_EVIDENCE/E6/results/"
DISC = re.compile(r"\\discretionary\{\\hbox\{\\ensuremath\{\\hookrightarrow\}\}\}\{\}\{\}")
def tex_code(t):
    out = []
    i = 0
    key = "{\\ttfamily\\small "
    while True:
        j = t.find(key, i)
        if j < 0: break
        k = j + len(key); depth = 1; s = k
        while depth:
            c = t[k]
            if c == "\\" : k += 2; continue
            if c == "{": depth += 1
            elif c == "}": depth -= 1
            k += 1
        body = t[s:k - 1]
        body = DISC.sub("", body)
        body = re.sub(r"\\textbackslash\{\}", "\\\\", body)
        body = re.sub(r"\\textasciitilde\{\}", "~", body)
        body = re.sub(r"\\textasciicircum\{\}", "^", body)
        body = re.sub(r"\\([_#%&$])", r"\1", body)
        body = body.replace("\\{", "{").replace("\\}", "}")
        out.append(body)
        i = k
    return out
res = {}
for lang in ["en", "es"]:
    md = open(D + f"PAPER_IV_preprint_v1.21_{lang}.md", encoding="utf-8").read()
    tx = open(D + f"PAPER_IV_preprint_v1.21_{lang}.tex", encoding="utf-8").read()
    mdc = collections.Counter(re.findall(r"`([^`\n]+)`", re.sub(r"```.*?```", "", md, flags=re.S)))
    txc = collections.Counter(tex_code(tx))
    res[lang] = {"md_code": sum(mdc.values()), "tex_code": sum(txc.values()),
                 "only_md": sorted((mdc - txc).elements()), "only_tex": sorted((txc - mdc).elements())}
    # check that every line-break opportunity in tex code uses the arrow (no plain hyphen breaks)
    res[lang]["disc_arrow_count"] = len(DISC.findall(tx))
    res[lang]["other_discretionary"] = re.findall(r"\\discretionary\{(?!\\hbox\{\\ensuremath\{\\hookrightarrow)[^}]*\}", tx)[:20]
    res[lang]["hyphenation_in_tt"] = [b for b in tex_code(tx) if "\\-" in b][:20]
    # verbatim/highlighting blocks
    res[lang]["verbatim_blocks"] = len(re.findall(r"\\begin\{(verbatim|Verbatim|lstlisting|Highlighting)\}", tx))
    res[lang]["md_fences"] = len(re.findall(r"^```", md, flags=re.M)) // 2
json.dump(res, open(OUT + "md_vs_tex.json", "w", encoding="utf-8"), ensure_ascii=False, indent=1)
for l in res:
    r = res[l]
    print(l, r["md_code"], r["tex_code"], "only_md", r["only_md"][:30], "only_tex", r["only_tex"][:30], "arrows", r["disc_arrow_count"], "otherdisc", r["other_discretionary"], "hy", r["hyphenation_in_tt"], "verb", r["verbatim_blocks"], "fences", r["md_fences"])
