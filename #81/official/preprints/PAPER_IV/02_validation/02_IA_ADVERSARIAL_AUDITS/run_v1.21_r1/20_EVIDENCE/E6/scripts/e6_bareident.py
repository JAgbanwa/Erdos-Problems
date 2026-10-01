"""Identifier-like tokens in prose outside code/math (X-12 source side)."""
import re, collections, json
D = "C:/Users/jtraverso/e81p4-publish/preprints/PAPER_IV/01_manuscript/v1.21_editorial_candidate/"
OUT = "C:/Users/jtraverso/e81p4-publish/preprints/PAPER_IV/02_validation/02_IA_ADVERSARIAL_AUDITS/run_v1.21_r1/20_EVIDENCE/E6/results/"
res = {}
for lang in ["en", "es"]:
    t = open(D + f"PAPER_IV_preprint_v1.21_{lang}.md", encoding="utf-8").read()
    t = re.sub(r"```.*?```", lambda m: "\n" * m.group(0).count("\n"), t, flags=re.S)
    hits = []
    for i, l in enumerate(t.split("\n")):
        s = re.sub(r"`[^`]*`", " ", l)
        s = re.sub(r"\\\(.+?\\\)|\$[^$]*\$", " ", s)
        s = re.sub(r"https?://\S+|<[^>]+>", " ", s)
        for m in re.finditer(r"(?<![\w/.\\-])([A-Za-z]+[a-z][A-Z]\w*|[A-Za-z]\w*_\w+|[A-Z][A-Za-z0-9]*\.[A-Za-z]\w+)(?![\w])", s):
            hits.append((i + 1, m.group(1)))
    res[lang] = hits
json.dump(res, open(OUT + "bare_identifiers.json", "w", encoding="utf-8"), ensure_ascii=False, indent=1)
for l in res:
    c = collections.Counter(w for _, w in res[l])
    print(l, len(res[l]), sorted(c.items()))
    print("  lines:", [(n, w) for n, w in res[l]][:80])
