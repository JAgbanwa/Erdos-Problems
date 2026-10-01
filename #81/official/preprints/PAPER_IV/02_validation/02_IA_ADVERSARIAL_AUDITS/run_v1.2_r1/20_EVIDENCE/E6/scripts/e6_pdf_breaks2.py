"""E6: per-page arrow markers, hyphenated breaks of identifier-like tokens, page-boundary identifier splits, prime contexts."""
import pymupdf, json, re
D = "C:/Users/jtraverso/e81p4-publish/preprints/PAPER_IV/01_manuscript/v1.2_full_rebuild_candidate/"
E = "C:/Users/jtraverso/e81p4-publish/preprints/PAPER_IV/02_validation/02_IA_ADVERSARIAL_AUDITS/run_v1.2_r1/20_EVIDENCE/E6/"
res = {}
for l in ("en", "es"):
    doc = pymupdf.open(D + f"PAPER_IV_preprint_v1.2_{l}.pdf")
    arrows, hyph, pagesplit, prime, footer = [], [], [], [], []
    for p in doc:
        t = p.get_text()
        pn = p.number + 1
        lines = [x for x in t.split("\n")]
        nonempty = [x for x in lines if x.strip()]
        footer.append((pn, nonempty[-1].strip() if nonempty else ""))
        for m in re.finditer(r",→\n", t):
            arrows.append((pn, t[max(0, m.start() - 35):m.start()].split("\n")[-1] + " ,→ " + t[m.end():m.end() + 25].split("\n")[0]))
        # hyphen at line end in identifier-like context (CamelCase or with _ .)
        for m in re.finditer(r"(\S+)-\n(\S+)", t):
            a, b = m.group(1), m.group(2)
            if re.search(r"[_.]|[a-z][A-Z]", a + b) and not a.endswith("-"):
                hyph.append((pn, a + "-⏎" + b))
        # identifier split across page end: last content line before page number ends with ,→
        if len(nonempty) >= 2 and nonempty[-2].rstrip().endswith(",→"):
            pagesplit.append((pn, nonempty[-2][-50:]))
        for m in re.finditer(r"(Theorems?|Teoremas?)\s+C(.{0,12})", t, re.S):
            prime.append((pn, ("C" + m.group(2)).replace("\n", "⏎")))
    res[l] = dict(arrows=arrows, n_arrows=len(arrows), hyphen_ident=hyph, page_boundary_splits=pagesplit, prime=prime,
                  footer_mismatch=[f for f in footer if f[1] != str(f[0])])
    print(l, "arrows", len(arrows), "hyph_ident", hyph, "page_splits", pagesplit)
    print("  footer mismatches:", res[l]["footer_mismatch"][:80])
    print("  prime:", sorted(set(x[1][:4] for x in prime)))
    for x in prime:
        if not x[1].startswith("C′") and not re.match(r"C[ ,.:;⏎]", x[1]):
            print("   odd prime ctx", x)
json.dump(res, open(E + "results/pdf_breaks2.json", "w", encoding="utf-8"), ensure_ascii=False, indent=1)
