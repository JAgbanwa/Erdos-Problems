"""Span-level PDF analysis for X-12: identifiers in roman fonts, mono line-end hyphens, continuation arrows."""
import pymupdf, re, json, collections
D = "C:/Users/jtraverso/e81p4-publish/preprints/PAPER_IV/01_manuscript/v1.21_editorial_candidate/"
E = "C:/Users/jtraverso/e81p4-publish/preprints/PAPER_IV/02_validation/02_IA_ADVERSARIAL_AUDITS/run_v1.21_r1/20_EVIDENCE/E6/"
IDRE = re.compile(r"(?<![\w.])([A-Za-z]+[a-z][A-Z]\w*(?:\.\w+)*|[A-Za-z]\w*_\w+|[A-Z][A-Za-z0-9]+\.[A-Za-z_]\w*)")
res = {}
for lang in ["en", "es"]:
    doc = pymupdf.open(D + f"PAPER_IV_preprint_v1.21_{lang}.pdf")
    roman_ids, mono_hyph, arrows, mono_lines = [], [], collections.Counter(), 0
    arrow_fonts = collections.Counter()
    for pno, p in enumerate(doc):
        d = p.get_text("dict")
        for b in d["blocks"]:
            for l in b.get("lines", []):
                spans = l["spans"]
                for si, s in enumerate(spans):
                    f, t = s["font"], s["text"]
                    if "↪" in t:
                        arrows[pno + 1] += t.count("↪"); arrow_fonts[f] += 1
                    if "Mono" in f:
                        mono_lines += 1
                        if si == len(spans) - 1 and t.rstrip().endswith("-"):
                            mono_hyph.append((pno + 1, t))
                    elif "LMRoman" in f or "CMR" in f:
                        for m in IDRE.finditer(t):
                            w = m.group(1)
                            roman_ids.append((pno + 1, f, w, t[:120]))
    # also check whether an arrow glyph appears at a line end next to mono text
    res[lang] = {"roman_identifier_like": roman_ids, "mono_line_end_hyphen": mono_hyph,
                 "arrow_pages": dict(arrows), "arrow_total": sum(arrows.values()), "arrow_fonts": dict(arrow_fonts)}
json.dump(res, open(E + "results/pdf_spans.json", "w", encoding="utf-8"), ensure_ascii=False, indent=1)
for l in res:
    r = res[l]
    print(l, "arrows", r["arrow_total"], r["arrow_fonts"], "pages", sorted(r["arrow_pages"]))
    print(" mono line-end hyphens:", r["mono_line_end_hyphen"])
    print(" roman identifier-like:")
    for x in r["roman_identifier_like"]:
        print("   ", x)
