"""Reuse aligned, reviewed paragraphs; new or changed text requires editorial translation."""
from pathlib import Path
import re
import json
from difflib import SequenceMatcher

ROOT = Path(__file__).resolve().parent
def blocks(text):
    return re.split(r"\n\s*\n", text.strip())
def signature(block):
    protected = re.findall(r"\\\(.*?\\\)|\\\[.*?\\\]|\\tag\{[^}]+\}", block, re.S)
    if protected:
        return re.sub(r"\\text\{[^}]+\}", r"\\text{}", "|".join(protected))
    if block.startswith("#"):
        return "#" + (re.search(r"\d+(?:\.\d+)*|[A-G](?:\.\d+)*", block) or [""])[0]
    if block.startswith("|"):
        return "|:" + str(block.count("\n"))
    return ""

def relocated(text, spanish=False):
    spec = json.loads((ROOT / "R2_STRUCTURAL_MAP.json").read_text(encoding="utf-8"))
    for prefix in (r"(\\tag\{)([^}]+)(\})", r"(\()((?:6|8)\.\d+[ab]?)(\))"):
        text = re.sub(prefix, lambda m: m[1]+spec["equation_map"].get(m[2],m[2])+m[3], text)
    names = spec["result_map"]
    if spanish:
        names = {k.replace("Proposition","Proposición").replace("Corollary","Corolario").replace("Theorem","Teorema"):
                 v.replace("Proposition","Proposición").replace("Corollary","Corolario").replace("Theorem","Teorema")
                 for k,v in names.items()}
    text = re.sub("|".join(re.escape(k) for k in sorted(names,key=len,reverse=True)), lambda m:names[m[0]],text)
    for a,b in [("§§6.8–6.9","§§6.6–6.7"),("Section 6.8","Section 6.6"),("Section 6.9","Section 6.7"),
                ("Sección 6.8","Sección 6.6"),("Sección 6.9","Sección 6.7"),("§6.8","§6.6"),("§6.9","§6.7"),
                ("§8.2","Apéndice G.1" if spanish else "Appendix G.1"),("§8.3","Apéndice G.2" if spanish else "Appendix G.2")]:
        text=text.replace(a,b)
    return text

if __name__ == "__main__":
    en = blocks((ROOT.parent / "v1.0.1_candidate/PAPER_IV_preprint_v1.0.1_en.md").read_text(encoding="utf-8"))
    es = blocks((ROOT.parent / "v1.0.1_candidate/PAPER_IV_preprint_v1.0.1_es.md").read_text(encoding="utf-8"))
    print("Baseline blocks:", len(en), len(es))
    matcher = SequenceMatcher(None, [signature(b) for b in en], [signature(b) for b in es], autojunk=False)
    mapping = {}
    for op, a, b, c, d in matcher.get_opcodes():
        if op == "equal":
            for i, j in zip(range(a,b), range(c,d)):
                mapping[en[i]] = es[j]
        else:
            print(op, (a,b), (c,d), repr(en[a][:130]) if a<len(en) else "")
    current = blocks((ROOT / "PAPER_IV_preprint_v1.2_en.md").read_text(encoding="utf-8"))
    stage_en = blocks((ROOT / "review_history/before-editor-20260929/PAPER_IV_preprint_v1.2_en.md").read_text(encoding="utf-8"))
    stage_es = blocks((ROOT / "review_history/before-bilingual-20260929/PAPER_IV_preprint_v1.2_es.md").read_text(encoding="utf-8"))
    stage_match = SequenceMatcher(None, [signature(b) for b in stage_en], [signature(b) for b in stage_es], autojunk=False)
    for op,a,b,c,d in stage_match.get_opcodes():
        if op == "equal":
            for i,j in zip(range(a,b),range(c,d)):
                mapping.setdefault(stage_en[i], stage_es[j])
                mapping.setdefault(relocated(stage_en[i]), relocated(stage_es[j],True))
        else:
            print("Stage", op, (a,b), (c,d))
    records = []
    for i, block in enumerate(current):
        translation = mapping.get(block)
        if translation is None and not re.search(r"[A-Za-z]{3}", re.sub(r"\\[A-Za-z]+", "", block)):
            translation = block
        records.append({"id":i, "en":block, "es":translation})
    (ROOT / "BILINGUAL_BLOCKS.json").write_text(json.dumps(records,ensure_ascii=False,indent=2),encoding="utf-8")
    print("Total:",len(records),"Reused:",sum(x["es"] is not None for x in records),
          "Translate:",sum(len(x["en"]) for x in records if x["es"] is None))
