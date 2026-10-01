"""Bilingual structure and protected-token comparisons; not a semantic proof."""
from pathlib import Path
import hashlib
import json
import re
from prepare_bilingual import blocks
from assemble_bilingual import mask

ROOT=Path(__file__).resolve().parent
en=(ROOT/"PAPER_IV_preprint_v1.2_en.md").read_text(encoding="utf-8")
es=(ROOT/"PAPER_IV_preprint_v1.2_es.md").read_text(encoding="utf-8")
def norm(s):
    translations={"cordal":"chordal"," cordal":" chordal","si ":"if ","impar":"odd","par":"even","o":"or"," o ":" or ",
        "testigo estructural cercano de ":"near-structure witness for ",
        "enlaces ausentes entre ":"missing links between "," y ":" and ",
        " es completo-split con núcleo óptimo":" is complete-split with an optimal core",
        " activo":" active"}
    s=re.sub(r"\\text\{([^}]*)\}",lambda m:r"\text{"+translations.get(m[1],m[1])+"}",s)
    return re.sub(r"\s+","",s)
eb,sb=blocks(en),blocks(es)
mismatches=[]
for i,(a,b) in enumerate(zip(eb,sb)):
    ap,bp=mask(a)[1],mask(b)[1]
    if list(map(norm,ap))!=list(map(norm,bp)):
        mismatches.append({"block":i,"en":ap,"es":bp})
def head(x):
    results=[]
    for m in re.finditer(r"(?m)^(#+) (.*)$",x):
        title=re.sub(r"^(?:Appendix|Apéndice|Theorem|Teorema|Lemma|Lema|Corollary|Corolario|Proposition|Proposición) ","",m[2])
        n=re.match(r"(?:\d+|[A-G])(?:\.\d+)*(?:a|b|′)?(?=[. :]|$)",title)
        results.append((len(m[1]), n[0] if n else ""))
    return results
report={
 "scope":"Static bilingual parity; authorial translation reviewed separately.",
 "en_sha256":hashlib.sha256(en.encode()).hexdigest(),
 "es_sha256":hashlib.sha256(es.encode()).hexdigest(),
 "block_counts":[len(eb),len(sb)],
 "math_and_code_mismatches":mismatches,
 "headings_match":head(en)==head(es),
 "equation_labels_match":re.findall(r"\\tag\{([^}]+)\}",en)==re.findall(r"\\tag\{([^}]+)\}",es),
 "image_counts":[len(re.findall(r"!\[",x)) for x in (en,es)],
 "english_only_metadata_remaining": bool(re.search(r"English Markdown review|Spanish synchronization",en)),
}
(ROOT/"BILINGUAL_CHECKS.json").write_text(json.dumps(report,ensure_ascii=False,indent=2)+"\n",encoding="utf-8")
print("Blocks",report["block_counts"],"headings",report["headings_match"],
      "labels",report["equation_labels_match"],"mismatch blocks",[m["block"] for m in mismatches])
for m in mismatches:
    print(json.dumps(m,ensure_ascii=False))
