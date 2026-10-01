"""E6: PDF checks (page count, fonts, text anomalies, mono line-breaks, prime notation, figures) + page renders."""
import pymupdf, json, re, collections, sys
D = "C:/Users/jtraverso/e81p4-publish/preprints/PAPER_IV/01_manuscript/v1.2_full_rebuild_candidate/"
E = "C:/Users/jtraverso/e81p4-publish/preprints/PAPER_IV/02_validation/02_IA_ADVERSARIAL_AUDITS/run_v1.2_r1/20_EVIDENCE/E6/"
render = "--render" in sys.argv
res = {}
for l in ("en", "es"):
    doc = pymupdf.open(D + f"PAPER_IV_preprint_v1.2_{l}.pdf")
    r = dict(pages=doc.page_count, metadata=doc.metadata)
    fonts = {}
    for p in doc:
        for f in p.get_fonts(full=True):
            xref, ext, typ, base, name, enc = f[0], f[1], f[2], f[3], f[4], f[5]
            fonts.setdefault(base, dict(type=typ, ext=ext, embedded=ext not in ("", "n/a"), pages=set()))["pages"].add(p.number + 1)
    for k in fonts:
        fonts[k]["pages"] = sorted(fonts[k]["pages"])
        fonts[k]["npages"] = len(fonts[k]["pages"]); fonts[k]["pages"] = fonts[k]["pages"][:10]
    r["fonts"] = fonts
    r["nonembedded_fonts"] = [k for k, v in fonts.items() if not v["embedded"]]
    anomalies = []
    texts = []
    mono_breaks = []
    prime = collections.Counter()
    prime_ctx = []
    for p in doc:
        t = p.get_text()
        texts.append(t)
        for pat in ["??", "[?]", "\ufffd", "Undefined", "undefined", "Missing", "\\", "{[}", "{]}", "¿?"]:
            for mo in re.finditer(re.escape(pat), t):
                anomalies.append(dict(page=p.number + 1, pat=pat, ctx=t[max(0, mo.start() - 60):mo.end() + 60].replace("\n", " ⏎ ")))
        # prime check: "Theorem C" / "Teorema C" followed by what
        for mo in re.finditer(r"(Theorems?|Teoremas?|Teorema|del Teorema)\s+C(.{0,3})", t):
            nxt = mo.group(2)
            prime[repr(nxt[:1])] += 1
            prime_ctx.append(dict(page=p.number + 1, ctx=t[mo.start():mo.end() + 25].replace("\n", " ⏎ ")))
        # mono spans at line ends
        d = p.get_text("dict")
        for b in d["blocks"]:
            for ln in b.get("lines", []):
                spans = ln["spans"]
                if not spans:
                    continue
                last = spans[-1]
                if "Mono" in last["font"] or "mono" in last["font"].lower() or "TT" in last["font"]:
                    txt = last["text"].rstrip()
                    mono_breaks.append(dict(page=p.number + 1, font=last["font"], end=txt[-40:], y=round(ln["bbox"][1], 1)))
    # identify mono line-ends that are mid-identifier: i.e. next line starts with mono span too; flag if no arrow
    r["anomalies"] = anomalies
    r["prime_next_char"] = dict(prime)
    r["prime_ctx"] = prime_ctx
    r["mono_line_ends"] = mono_breaks
    full = "\n".join(texts)
    r["arrow_count"] = full.count("↪")
    r["arrow_pages"] = sorted({i + 1 for i, t in enumerate(texts) if "↪" in t})
    # captions
    r["captions"] = [dict(page=i + 1, ctx=m.group(0)[:160].replace("\n", " ")) for i, t in enumerate(texts) for m in re.finditer(r"(Figure|Figura) \d+[.:].{0,150}", t, re.S)]
    r["fig_refs"] = [dict(page=i + 1, ctx=t[max(0, m.start() - 50):m.end() + 30].replace("\n", " ")) for i, t in enumerate(texts) for m in re.finditer(r"(Figure|Figura) \d", t)]
    # images per page
    r["images"] = {i + 1: len(pg.get_images()) for i, pg in enumerate(doc) if pg.get_images()}
    r["drawings_pages"] = {}
    # status paragraph page 1
    r["page1_text"] = texts[0]
    # section 7 counts
    for kw in ["607", "615", "421", "186", "461", "224", "75 ", "81 ", "19 ", "fb459343", "cb274145", "piv-v12"]:
        r.setdefault("kw_pages", {})[kw] = [i + 1 for i, t in enumerate(texts) if kw in t.replace("↪", "").replace("\n", "")]
    open(E + f"results/pdf_text_{l}.txt", "w", encoding="utf-8").write("\n\f".join(f"=== PAGE {i+1} ===\n" + t for i, t in enumerate(texts)))
    if render:
        for pg in doc:
            pix = pg.get_pixmap(dpi=110)
            pix.save(E + f"pages_{l}/p{pg.number + 1:03d}.png")
    res[l] = r
    print(l, "pages", doc.page_count, "fonts", len(fonts), "nonembedded", r["nonembedded_fonts"], "anomalies", len(anomalies), "arrows", r["arrow_count"], "prime", dict(prime))
json.dump(res, open(E + "results/pdf_checks.json", "w", encoding="utf-8"), ensure_ascii=False, indent=1, default=str)
