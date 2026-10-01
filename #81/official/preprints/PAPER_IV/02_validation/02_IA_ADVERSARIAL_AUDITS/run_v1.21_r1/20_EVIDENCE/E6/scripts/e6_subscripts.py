import re, collections
D = "C:/Users/jtraverso/e81p4-publish/preprints/PAPER_IV/01_manuscript/v1.21_editorial_candidate/"
P = "C:/Users/jtraverso/e81p4-publish/preprints/PAPER_IV/01_manuscript/v1.2_full_rebuild_candidate/"
files = {f: D + "PAPER_IV_preprint_v1.21_" + f for f in ["en.md", "es.md", "en.tex", "es.tex"]}
files["old_en.md"] = P + "PAPER_IV_preprint_v1.2_en.md"
files["old_es.md"] = P + "PAPER_IV_preprint_v1.2_es.md"
pat = re.compile(r"\\(?:mathrm|operatorname\*?|mathsf|mathit|mathtt|mathbf|textsf)\s*\{([^{}]*)\}")
for f, p in files.items():
    t = open(p, encoding="utf-8").read()
    c = collections.Counter(pat.findall(t))
    print("==", f, len(c))
    print(sorted(c.items()))
SP = ["lej", "cruz", "limp", "lejano", "cub", "mis", "nuev", "viej", "cerc", "resto", "perd", "marc", "tot", "fis"]
print("\n-- Spanish-root subscripts in EN files")
for f in ["en.md", "en.tex", "old_en.md"]:
    t = open(files[f], encoding="utf-8").read()
    for m in pat.finditer(t):
        a = m.group(1)
        if any(a.lower().startswith(s) for s in SP):
            print(f, t.count("\n", 0, m.start()) + 1, m.group(0))
    for m in re.finditer(r"_\{?(lej|cruz|limpio|lejano|cub|mis)\b", t):
        print(f, "bare", t.count("\n", 0, m.start()) + 1, t[m.start()-10:m.end()+5])
