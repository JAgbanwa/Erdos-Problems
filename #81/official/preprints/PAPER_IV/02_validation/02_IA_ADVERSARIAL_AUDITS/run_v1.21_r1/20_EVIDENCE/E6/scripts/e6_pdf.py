"""PDF checks: pages, fonts, bad strings, figure captions/refs, render pages at 110 dpi."""
import pymupdf, json, re, sys
D = "C:/Users/jtraverso/e81p4-publish/preprints/PAPER_IV/01_manuscript/v1.21_editorial_candidate/"
E = "C:/Users/jtraverso/e81p4-publish/preprints/PAPER_IV/02_validation/02_IA_ADVERSARIAL_AUDITS/run_v1.21_r1/20_EVIDENCE/E6/"
render = "--render" in sys.argv
res = {}
for lang in ["en", "es"]:
    doc = pymupdf.open(D + f"PAPER_IV_preprint_v1.21_{lang}.pdf")
    r = {"pages": doc.page_count, "metadata": doc.metadata}
    fonts = {}
    for p in doc:
        for f in p.get_fonts(full=True):
            xref, ext, typ, base, name, enc = f[0], f[1], f[2], f[3], f[4], f[5]
            fonts[base] = {"type": typ, "ext": ext, "embedded": ext not in ("n/a", "")}
    r["fonts"] = fonts
    r["non_embedded"] = [k for k, v in fonts.items() if not v["embedded"]]
    bad = []
    pages_text = []
    for i, p in enumerate(doc):
        t = p.get_text()
        pages_text.append(t)
        for pat in ["??", "\ufffd", "Undefined", "undefined", "[?]", "Missing character"]:
            if pat in t:
                for m in re.finditer(re.escape(pat), t):
                    bad.append((i + 1, pat, t[max(0, m.start() - 60):m.end() + 40].replace("\n", " ")))
    r["bad_strings"] = bad
    # figure captions and references
    cap = []
    for i, t in enumerate(pages_text):
        for m in re.finditer(r"(Figure|Figura)\s+(\d)", t):
            cap.append((i + 1, m.group(0), t[max(0, m.start() - 50):m.end() + 70].replace("\n", " ")))
    r["figure_mentions"] = cap
    imgs = []
    for i, p in enumerate(doc):
        il = p.get_images(full=True)
        dr = [d for d in p.get_drawings()] if False else []
        if il:
            imgs.append((i + 1, len(il)))
    r["pages_with_images"] = imgs
    # xobject forms (included PDFs) per page
    forms = []
    for i, p in enumerate(doc):
        try:
            xo = p.get_xobjects()
            if xo:
                forms.append((i + 1, [x[1] for x in xo]))
        except Exception as ex:
            pass
    r["pages_with_xobjects"] = forms
    r["page1_text"] = pages_text[0][:3000]
    res[lang] = r
    open(E + f"results/pdftext_{lang}.txt", "w", encoding="utf-8").write("\n\f".join(f"=== PAGE {i+1}\n{t}" for i, t in enumerate(pages_text)))
    if render:
        for i, p in enumerate(doc):
            p.get_pixmap(dpi=110).save(E + f"pages_{lang}/p{i+1:03d}.png")
json.dump(res, open(E + "results/pdf_checks.json", "w", encoding="utf-8"), ensure_ascii=False, indent=1)
for l in res:
    r = res[l]
    print(l, "pages", r["pages"], "nfonts", len(r["fonts"]), "non_embedded", r["non_embedded"])
    print(" fonts", {k: v["type"] for k, v in r["fonts"].items()})
    print(" bad", r["bad_strings"])
    print(" imgs", r["pages_with_images"], "xobj", r["pages_with_xobjects"])
    for c in r["figure_mentions"]:
        print("  ", c)
