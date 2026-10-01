"""Assemble human-edited Spanish segments without retyping protected mathematics."""
from pathlib import Path
import re
import json

ROOT = Path(__file__).resolve().parent
def mask(text):
    pieces = []
    def keep(m):
        pieces.append(m[0])
        return "{{"+str(len(pieces)-1)+"}}"
    pattern = r"\\\[.*?\\\]|\\\(.*?\\\)|" + chr(96)*3 + r".*?" + chr(96)*3 + r"|" + chr(96) + r"[^" + chr(96) + r"]+" + chr(96)
    return re.sub(pattern,keep,text,flags=re.S),pieces

if __name__ == "__main__":
    import sys
    records=json.loads((ROOT/"BILINGUAL_BLOCKS.json").read_text(encoding="utf-8"))
    if "--show" in sys.argv:
        a,b=map(int,sys.argv[-2:])
        for item in records:
            if a<=item["id"]<b and item["es"] is None:
                print("@@"+str(item["id"])+"\n"+mask(item["en"])[0]+"\n")
    else:
        translations={}
        for path in sorted((ROOT/"translation").glob("*.txt")):
            for m in re.finditer(r"(?ms)^@@(\d+)\n(.*?)(?=^@@\d+\n|\Z)",path.read_text(encoding="utf-8")):
                key=int(m[1])
                assert key not in translations,key
                translations[key]=m[2].strip()
        result=[]
        for item in records:
            key=item["id"]
            if key in translations:
                _,pieces=mask(item["en"])
                rendered=translations[key]
                assert sorted(map(int,re.findall(r"\{\{(\d+)\}\}",rendered)))==list(range(len(pieces))),key
                rendered=re.sub(r"\{\{(\d+)\}\}",lambda m:pieces[int(m[1])],rendered)
            else:
                rendered=item["es"]
            assert rendered is not None, f"Missing translation {key}"
            result.append(rendered.replace("figures_en/","figures/"))
        (ROOT/"PAPER_IV_preprint_v1.2_es.md").write_text("\n\n".join(result)+"\n",encoding="utf-8")
        print("Assembled",len(result),"paragraph blocks")
