#!/usr/bin/env python3
"""Paper III v1.4, gate E5 -- render and inspect every page of both PDFs, and compare
MD against generated TeX and extracted PDF text.

Per-page checks: ink coverage (blank/near-blank detection), right-margin overflow
(clipping), replacement characters, and per-page text length. Document checks: page counts,
producer, and the presence of every equation tag, theorem number and reference in the
extracted text.
"""
import glob
import json
import os
import re
import subprocess

T = "C:/p3v14/01_manuscript"
OUT = "C:/erdos_audit/v14/E5"
DOCS = {"EN": ("PAPER_III_preprint_draft_v1.4.md",
               "PAPER_III_preprint_draft_v1.4_en.tex",
               "PAPER_III_preprint_draft_v1.4_en.pdf"),
        "ES": ("PAPER_III_preprint_draft_v1.4_es.md",
               "PAPER_III_preprint_draft_v1.4_es.tex",
               "PAPER_III_preprint_draft_v1.4_es.pdf")}


def rd(p):
    return open(p, encoding="utf-8", errors="replace").read()


def pdftotext(pdf):
    out = os.path.join(OUT, os.path.basename(pdf) + ".txt")
    subprocess.run(["pdftotext", "-enc", "UTF-8", pdf, out], check=True)
    return rd(out)


def pdfinfo(pdf):
    r = subprocess.run(["pdfinfo", pdf], capture_output=True, text=True,
                       encoding="utf-8", errors="replace")
    d = {}
    for line in r.stdout.splitlines():
        if ":" in line:
            k, v = line.split(":", 1)
            d[k.strip()] = v.strip()
    return d


def page_qa(pdf, tag):
    from PIL import Image
    d = os.path.join(OUT, "pages_" + tag)
    os.makedirs(d, exist_ok=True)
    for f in glob.glob(d + "/*.png"):
        os.remove(f)
    subprocess.run(["pdftoppm", "-r", "60", "-gray", "-png", pdf, d + "/p"], check=True)
    rows = []
    for f in sorted(glob.glob(d + "/*.png")):
        im = Image.open(f).convert("L")
        w, h = im.size
        px = im.tobytes()
        ink = sum(1 for v in px if v < 200) / len(px)
        right = im.crop((int(w * 0.97), 0, w, h)).tobytes()
        edge = sum(1 for v in right if v < 200) / max(1, len(right))
        bottom = im.crop((0, int(h * 0.985), w, h)).tobytes()
        bot = sum(1 for v in bottom if v < 200) / max(1, len(bottom))
        rows.append({"page": os.path.basename(f), "size": [w, h],
                     "ink": round(ink, 5), "right_edge": round(edge, 6),
                     "bottom_edge": round(bot, 6),
                     "blank": ink < 0.004, "right_overflow": edge > 0.0005,
                     "bottom_overflow": bot > 0.002})
    return rows


def main():
    os.makedirs(OUT, exist_ok=True)
    res = {"gate": "E5", "docs": {}}
    for lang, (md, tex, pdf) in DOCS.items():
        mdp, texp, pdfp = f"{T}/{md}", f"{T}/{tex}", f"{T}/{pdf}"
        m, x = rd(mdp), rd(texp)
        txt = pdftotext(pdfp)
        info = pdfinfo(pdfp)
        pages = page_qa(pdfp, lang)

        tags = sorted(set(re.findall(r"\\tag\{([^}]+)\}", m)))
        thms = sorted(set(re.findall(
            r"(?:Theorem|Teorema|Lemma|Lema|Corollary|Corolario|Proposition|"
            r"Proposici[oó]n)\s+(\d+\.\d+[a-z]?)", m)))
        refs = sorted(set(re.findall(r"^\s*\[(\d+)\]", m, re.M)), key=int)
        idents = sorted(set(re.findall(r"`([A-Za-z][A-Za-z0-9_.]*\.[A-Za-z0-9_.]+)`", m)))

        # everything the markdown promises must survive into the pdf text
        flat = re.sub(r"\s+", " ", txt)
        res["docs"][lang] = {
            "pdf_pages_declared": info.get("Pages"),
            "pdf_pages_rendered": len(pages),
            "producer": info.get("Producer"),
            "pdf_bytes": os.path.getsize(pdfp),
            "replacement_chars_in_pdf_text": txt.count("\ufffd"),
            "pdf_text_chars": len(txt),
            "tex_from_md": {
                "equation_tags_md": len(tags),
                "equation_tags_in_tex": sum(1 for t in tags if t in x),
                "theorem_numbers_md": len(thms),
                "theorem_numbers_in_tex": sum(1 for t in thms if t in x),
                "formal_identifiers_md": len(idents),
                "formal_identifiers_in_tex": sum(1 for i in idents if i in x)},
            "pdf_from_md": {
                "equation_tags_in_pdf": sum(1 for t in tags if t in flat),
                "equation_tags_missing": [t for t in tags if t not in flat][:12],
                "theorem_numbers_in_pdf": sum(1 for t in thms if t in flat),
                "theorem_numbers_missing": [t for t in thms if t not in flat][:12],
                "refs_md": len(refs),
                "refs_in_pdf": sum(1 for r in refs if f"[{r}]" in flat),
                "formal_identifiers_in_pdf":
                    sum(1 for i in idents if i in flat),
                "formal_identifiers_missing":
                    [i for i in idents if i not in flat][:12]},
            "pages": {
                "count": len(pages),
                "blank": [p["page"] for p in pages if p["blank"]],
                "right_overflow": [p["page"] for p in pages if p["right_overflow"]],
                "bottom_overflow": [p["page"] for p in pages if p["bottom_overflow"]],
                "min_ink": min(p["ink"] for p in pages),
                "max_ink": max(p["ink"] for p in pages),
                "detail": pages}}

    # cross-language page count and the A_2J regression, in the pdf text
    en = rd(os.path.join(OUT, os.path.basename(DOCS["EN"][2]) + ".txt"))
    es = rd(os.path.join(OUT, os.path.basename(DOCS["ES"][2]) + ".txt"))
    res["cross_language_pdf"] = {
        "A_2J_en": len(re.findall(r"A2J|A_\{2J\}|A2J", en)),
        "A_2J_es": len(re.findall(r"A2J|A_\{2J\}|A2J", es)),
        "prop_7_4_en": en.count("7.4"), "prop_7_4_es": es.count("7.4"),
        "pages_en": res["docs"]["EN"]["pdf_pages_rendered"],
        "pages_es": res["docs"]["ES"]["pdf_pages_rendered"]}

    json.dump(res, open(f"{OUT}/E5_pdf_qa.json", "w"), indent=1)

    for lang, d in res["docs"].items():
        print(f"===== {lang}: {d['pdf_pages_rendered']} paginas "
              f"({d['pdf_bytes']:,} bytes), productor {d['producer']}")
        print(f"   U+FFFD en el texto extraido : {d['replacement_chars_in_pdf_text']}")
        t = d["tex_from_md"]
        print(f"   MD -> TeX  etiquetas {t['equation_tags_in_tex']}/"
              f"{t['equation_tags_md']}  teoremas {t['theorem_numbers_in_tex']}/"
              f"{t['theorem_numbers_md']}  identificadores "
              f"{t['formal_identifiers_in_tex']}/{t['formal_identifiers_md']}")
        p = d["pdf_from_md"]
        print(f"   MD -> PDF  etiquetas {p['equation_tags_in_pdf']}/"
              f"{t['equation_tags_md']}  teoremas {p['theorem_numbers_in_pdf']}/"
              f"{t['theorem_numbers_md']}  refs {p['refs_in_pdf']}/{p['refs_md']}  "
              f"identificadores {p['formal_identifiers_in_pdf']}/"
              f"{t['formal_identifiers_md']}")
        if p["equation_tags_missing"]:
            print(f"      etiquetas ausentes en PDF: {p['equation_tags_missing']}")
        if p["theorem_numbers_missing"]:
            print(f"      teoremas ausentes en PDF: {p['theorem_numbers_missing']}")
        if p["formal_identifiers_missing"]:
            print(f"      identificadores ausentes: {p['formal_identifiers_missing']}")
        g = d["pages"]
        print(f"   paginas en blanco: {g['blank'] or 'ninguna'}")
        print(f"   desborde derecho : {g['right_overflow'] or 'ninguno'}")
        print(f"   desborde inferior: {g['bottom_overflow'] or 'ninguno'}")
        print(f"   tinta min/max    : {g['min_ink']:.3%} / {g['max_ink']:.3%}")
        print()
    print("=== comparacion entre idiomas en el texto del PDF")
    print(json.dumps(res["cross_language_pdf"], indent=1))


if __name__ == "__main__":
    main()
