"""E6: write E6_RESULTS.json, E6_RECORD.md, PAGE_INSPECTION_LOG.csv from collected evidence."""
import json, csv
E = "C:/Users/jtraverso/e81p4-publish/preprints/PAPER_IV/02_validation/02_IA_ADVERSARIAL_AUDITS/run_v1.2_r1/20_EVIDENCE/E6/"

hashes = {
    "en.md": "a501d53b527da22f20112db2b05917fb61f46dd8e080faf14b69349b240cc152",
    "en.tex": "8068d4c6936cee54ad58d4e8e0bd12035c3aa2936101561647b6ab735a753995",
    "en.pdf": "76a9ff8e3d9a02b8e745bcdd101b8272ff15430e285fc403c18b958c7073e667",
    "es.md": "2b6f73bf09ef905ea2c92206ee254b4ae46e64f1a51533cb4d8bcdc4e68c7be9",
    "es.tex": "356e844bf75d55505241f7dca00f38c79d98233a776bc191e267c2052575d6e5",
    "es.pdf": "bfa83e0e9fa50f9d391af462bb6b24a786c68e7d39d47cf78786f09d6aa7afc4",
}

findings = [
 dict(id="E6-01", severity="MODERATE", where="ES md 37, 150, 269 (Sec. 3 title), 303; ES pdf p5-p10; cf. EN md 37,150,269,303 and EN/ES md 159",
      evidence="EN 'margin' is rendered 'holgura' (ES 150: 'una perdida menor que la holgura en el regimen lejano'; 269: 'Redondeo mixto y regimen con holgura'; 303: 'menor que la holgura de la instancia'), while ES 159 defines 'margen' = Delta(G) and 'holgura del selector' = unused auxiliary capacity and says the latter 'no debe confundirse con el margen del grafo'. EN keeps 'margin' vs 'selector slack' distinct.",
      description="Terminology conflict in the ES edition: the term the paper reserves for selector slack is used for the graph margin in four places, blurring a distinction the text itself declares essential. Substantive translation defect (meaning), not a math change."),
 dict(id="E6-02", severity="MINOR", where="EN pdf p31 (Defect-SharpPublication, PublicationIncrementAu-dit, Optimal-TemplateObstructionAudit, Release-ExportCheck), p63 (FD-Check.ASCheck); ES pdf p27 (NormalizedStabi-lity), p31 (DefectSharp-Publication, ResearchAu-dit), p33 (OptimalTemplateObs-tructionAudit), p65 (FD-Check.ASCheck); TeX EN 1005/1007/1058/2160 (same in ES)",
      evidence="These Lean names are set in roman (not {\\ttfamily}) in TeX and in plain text in MD, so TeX hyphenates them with an ordinary hyphen and no continuation arrow.",
      description="Contradicts the declared convention in Sec. 7 ('Formal identifiers are printed in monospaced type. A continuation arrow at a line break is a typesetting marker'). A reader may copy e.g. 'FD-Check.ASCheck'. All monospace breaks do carry the arrow (45 EN / 49 ES markers found)."),
 dict(id="E6-03", severity="MINOR", where="EN md 726-727 (N_lej), 819 (e_int, e_cruz), 1610 (x^limpio), 1661, 1685 (N_lejano), 1734 (E_cub), 2333 (mis_c); EN pdf p21, p23, p47, p48, p49, App. F.5",
      evidence="Spanish-derived subscripts inside math of the EN edition, e.g. \\(N_{\\mathrm{lej}}\\), \\(e_{\\rm cruz}(C)\\), \\(x_K^{\\rm limpio}\\), \\(N_{\\rm lejano}(\\eta_0)\\le T(h+7)\\).",
      description="Wrong-language fragments left in the English edition (math identical to ES by construction, which is why the math-sequence comparison is clean). Notation otherwise consistent; no meaning change."),
 dict(id="E6-04", severity="MINOR", where="EN pdf p38-39, ES pdf p39-40 (A.1 'Literal definitions'); TeX EN/ES 1261-1300 vs MD 1303-1345",
      evidence="MD code block has '\\u2200 \\u2983v : V\\u2984' (strict-implicit binder) and indented structure fields; TeX renders '\\{\\!\\{v : V\\}\\!\\}' -> PDF shows '{{v : V}}', and leading indentation is lost (fields of 'structure CliquePartition' flush-left, double-spaced).",
      description="The text calls these 'literal definitions ... omitting proofs but not hypotheses'; the PDF rendering is not literal Lean syntax. MD vs TeX/PDF mismatch in both languages (no semantic change to the statements)."),
 dict(id="E6-05", severity="MINOR", where="ES md 1034 ('Restar este baseline'), 1351 ('un build exitoso'), 1371 ('packings'), 1375 ('target', 'log'), 2351-2362 ('gap mixto', 'gap triangular'); ES pdf p28, p40-41, p51, p65",
      evidence="Untranslated English words in ES prose, while elsewhere ES uses 'valor base', 'compilacion', 'empaquetamientos', 'brecha'. Title of App. G uses 'Brechas' but G.1 body uses 'gap'.",
      description="Translation-quality / terminology consistency defects; translation-equivalent in meaning."),
 dict(id="E6-06", severity="OBSERVATION", where="ES md 45 vs 1070 vs 1257; ES md 1438; ES md 1189; ES md 837",
      evidence="'estrella con signos' (45, 1257) vs 'estrella con pesos de ambos signos' (1070); 'explicit hypothesis' -> 'hipotesis visible'; 'explicitly attributed support' -> 'soporte identificado'; Thm 6.1 'Existe gamma>0 y un umbral ... tales que' (agreement).",
      description="Minor nuance/consistency differences; qualifiers otherwise preserved. Classified translation-equivalent."),
 dict(id="E6-07", severity="OBSERVATION", where="PDF outline (bookmarks) EN and ES; TeX \\texorpdfstring{C\\ensuremath{^{\\prime}}}{C'} (13x each)",
      evidence="Bookmark titles read \"Theorem C'. Fixed-defect ...\" / \"Teorema C'. ...\" with ASCII apostrophe; body text renders C\\u2032 correctly (18 occurrences per PDF, 0 apostrophe variants).",
      description="Prime notation is correct in body text of both PDFs and in Figure 3; only bookmarks use the ASCII fallback."),
 dict(id="E6-08", severity="OBSERVATION", where="figures/ and figures_en/ file names; TeX 187, 502, 846, 1131; MD 180, 522, 940-942, 1228",
      evidence="Figure numbers vs file names: EN fig1_proof_map=Fig.1, fig2_host_realization=Fig.2, fig4_same_root_stability=Fig.3, fig3_budget_comparison=Fig.4; ES fig2_prueba_y_variantes=Fig.1, fig3_anfitrion=Fig.2, fig4_same_root_stability=Fig.3, fig1_presupuesto_comparado=Fig.4. All 4+4 referenced PDFs/PNGs exist. Only Figure 3 has an explicit 'Figure 3.' label in MD; Figure 3 is never cited in running text (EN/ES).",
      description="No broken reference; file-name/number mismatch is a maintenance hazard. Captions and figure contents agree EN/ES (labels translated, numbers/refs such as (6.12)-(6.16), Prop. 6.3a, Cor. 6.3 identical)."),
 dict(id="E6-09", severity="OBSERVATION", where="EN/ES PDFs, fonts from figure PDFs",
      evidence="17 Type3 fonts (DejaVuSans/Serif, STIXNonUnicode) reported with ext 'n/a' by pymupdf; all Type0/Type1 text fonts embedded as subsets.",
      description="Type3 fonts are embedded glyph procedures (render correctly) but some journal/arXiv pipelines flag them."),
 dict(id="E6-10", severity="OBSERVATION", where="ES pdf p32->p33 ('MixedRoundin' arrow at page foot); ES pdf p33 ('import' / 'PaperIV' split at line end)",
      evidence="Continuation arrow at a page break inside MixedRoundingAdapter; 'import\\ PaperIV' broken at the control space without marker.",
      description="Legal under the stated convention (first) / cosmetic (second)."),
 dict(id="E6-11", severity="OBSERVATION", where="MD EN/ES vs TeX EN/ES (identifiers)",
      evidence="208 backtick identifiers in MD vs 260 monospace identifiers in TeX; 52 Lean names (e.g. E35.Fexp_le_tower, FREEZE_SCOPE.json, A.1/F.4 table entries, F.5 lemma names) are plain text in MD.",
      description="Presentation inconsistency MD vs TeX (identical in both languages); text content is identical (word-level diff shows only markup)."),
 dict(id="E6-12", severity="OBSERVATION", where="EN md 1899-1901",
      evidence="Three consecutive blank lines after (E.2d) paragraph in EN MD (ES has one); causes the EN/ES MD 2-line offset after 1899.",
      description="Cosmetic source-only."),
]

results = dict(
  gate="E6", run="run_v1.2_r1", date="2026-09-30",
  inputs_verified_sha256=hashes, identity_check="PASS (all 6 hashes match)",
  reading_boundary="Only the 6 bound manuscript files and figures/ + figures_en/ fig1..fig4 were read. Directory listing (ls, wc -l) of D was run once and showed names/line counts of other files; their contents were not opened.",
  automated_comparison=dict(
    md_en_vs_es=dict(math_segments=[1988,1988], math_diffs_only_text_inside_math=4, math_substantive_diffs=0,
       equation_tags=[196,196], cite_keys=[129,129], cite_diffs="2 translation-equivalent ('and'->'y')", backtick_identifiers=[208,208], urls=[32,32], hashes=[9,9],
       sect_refs=[52,52], headings=[80,80], numbers_outside_math="754 vs 753: only extra 'SHA-256' repetition in EN line 1179 (translation-equivalent)",
       thmref_diffs="7, all plural/format artefacts ('Sections 4 and 5' etc.), no numbering mismatch"),
    tex_en_vs_es=dict(math_segments=[2045,2045], math_substantive_diffs=0, tags=[196,196], tt_identifiers_equal=True),
    md_vs_tex_within_language=dict(word_diff_ratio={"en":0.9908,"es":0.9915}, substantive_text_diffs=0,
       notes="Diffs are markup only (title block, URLs, dashes, table rules, enumerate, C' macro, Lean code block rendering). See E6-04, E6-11."),
    key_constants_checked=["16","48","480","10^{41}","2*10^{41}(s+1)^8","40000","38000","4*10^{12}","eta_0=10^{-16}","eps_0=10^{-12}","(6.11)","(6.28)","(F.1)","(F.11)","607","615","19","224","461","421","186","75","81","piv-v12-fb459343d234","fb459343d234f968...","cb2741454380..."],
    key_constants_result="identical EN/ES and MD/TeX",
    qualifier_check=dict(method="paragraph-aligned regex counts (486/486 paragraphs) + manual side-by-side reading of Abstract, Thms A,B,C,C', 6.1, 6.1a, 6.2, 6.3, 6.3a, 6.4, 6.5, 6.6, Sec. 8.1, A.2 table/A.3, F.3a/F.3b, F.5 intro, G.1/G.2, Prop G.1",
       result="All qualifiers preserved (eventual, for each fixed s, uniform in the defect, not claimed/no priority, at most four, rational/real, explicit but impractical, sufficiently large). 71 regex flags reviewed: all translation-equivalent (Spanish 'real'='actual', 'fijar'). Nuance items in E6-06; terminology defect E6-01.")),
  pdf_checks=dict(
    pages={"en":68,"es":69}, pages_match_stated=True,
    nonembedded_fonts="none except Type3 from figures (E6-09)",
    anomalies={"??":0,"[?]":0,"U+FFFD":0,"Undefined":0},
    continuation_arrows={"en":45,"es":49}, unmarked_identifier_hyphenations={"en":5,"es":6},
    prime_C={"en_body_C\u2032":18,"es_body_C\u2032":18,"apostrophe_variants":0,"bookmarks":"ASCII apostrophe"},
    figure2_ref={"en":"cited p15, figure p16","es":"cited p15, figure p16"},
    figure_placement={"en":{"1":7,"2":16,"3":26,"4":35},"es":{"1":7,"2":16,"3":26,"4":36}},
    status_paragraph_p1="present both; identical content (freeze id, 19 targets, audits pending, no DOI)",
    sec7_counts="607/615/421/186/461/224/75/81/19 and both SHA-256 present on EN p33, ES p33"),
  visual_inspection=dict(dpi=110, en_pages_viewed=68, es_pages_viewed=69,
    note="Rendering tool hit repeated rate-limit ('media removed') responses; each page was re-requested until it displayed. Coverage below is pages actually displayed."),
  findings=findings,
  verdict="PASS WITH MINOR ISSUES: no substantive mathematical or numerical divergence EN/ES or MD/TeX; one MODERATE terminology defect in ES (E6-01), several MINOR typesetting/translation defects.")
json.dump(results, open(E + "E6_RESULTS.json", "w", encoding="utf-8"), ensure_ascii=False, indent=1)

# page log
issues = {("en",21):"MINOR: Spanish subscript N_lej in EN (E6-03)", ("en",23):"MINOR: e_int/e_cruz subscripts (E6-03)",
 ("en",31):"MINOR: 4 roman Lean identifiers hyphenated without arrow (E6-02)", ("en",38):"MINOR: Lean excerpt {{v : V}} and lost indentation (E6-04)",
 ("en",39):"MINOR: Lean excerpt indentation lost (E6-04)", ("en",47):"MINOR: x^limpio superscript (E6-03)", ("en",48):"MINOR: N_lejano (E6-03)",
 ("en",49):"MINOR: E_cub (E6-03)", ("en",63):"MINOR: 'FD-Check.ASCheck' hyphenated (E6-02)",
 ("en",7):"OK: Figure 1 correct, caption matches", ("en",16):"OK: Figure 2 correct (cited p15)", ("en",26):"OK: Figure 3, C\u2032 rendered", ("en",35):"OK: Figure 4 correct",
 ("en",33):"OK: Sec.7 counts/hashes; arrows at hash/path breaks",
 ("es",5):"MINOR: 'holgura' used for margin (E6-01)", ("es",9):"MINOR: Sec.3 title 'regimen con holgura' (E6-01)", ("es",10):"MINOR: 'holgura de la instancia' (E6-01)",
 ("es",27):"MINOR: 'NormalizedStabi-lity' hyphenated (E6-02)", ("es",28):"MINOR: 'baseline' untranslated (E6-05)",
 ("es",31):"MINOR: DefectSharp-Publication, ResearchAu-dit hyphenated (E6-02)", ("es",32):"OBS: identifier split across page p32->p33 with arrow (E6-10)",
 ("es",33):"MINOR: OptimalTemplateObs-tructionAudit hyphenated; 'import PaperIV' line split (E6-02, E6-10)",
 ("es",39):"MINOR: Lean excerpt {{v : V}}/indentation (E6-04)", ("es",40):"MINOR: Lean excerpt; 'build exitoso' (E6-04, E6-05)",
 ("es",41):"MINOR: 'packings','target','log' untranslated (E6-05)", ("es",51):"MINOR: 'gap mixto' (E6-05)", ("es",65):"MINOR: 'FD-Check.ASCheck' hyphenated; 'gap' (E6-02, E6-05)",
 ("es",7):"OK: Figura 1 correct", ("es",16):"OK: Figura 2 correct (cited p15)", ("es",26):"OK: Figura 3, C\u2032 rendered", ("es",36):"OK: Figura 4 correct",
 ("es",33):"MINOR: OptimalTemplateObs-tructionAudit hyphenated; Sec.7 counts OK (E6-02)"}
with open(E + "PAGE_INSPECTION_LOG.csv", "w", newline="", encoding="utf-8") as f:
    w = csv.writer(f); w.writerow(["lang","page","status","note"])
    for lang, n in (("en",68),("es",69)):
        for p in range(1, n+1):
            note = issues.get((lang,p), "OK: no overlap, cut-off, glyph, table or language issue seen")
            st = note.split(":")[0]
            w.writerow([lang, p, st, note.split(": ",1)[1] if ": " in note else note])

# record
L = ["# E6 — Bilingual artifacts audit record (Paper IV v1.2)", "",
     "Run: run_v1.2_r1 · Date: 2026-09-30 · Sub-auditor: E6", "",
     "## Identity", "All six bound files match the expected SHA-256 (see E6_RESULTS.json). Page counts EN 68 / ES 69 as stated.", "",
     "## Coverage",
     "- Automated EN/ES comparison of MD and TeX: math segments (1988/1988 MD, 2045/2045 TeX), tags, citations, identifiers, URLs, hashes, numbers, headings.",
     "- MD vs TeX word-level comparison per language.",
     "- Qualifier survival: 486 aligned paragraphs (regex) plus manual side-by-side reading of the key statements listed in the brief.",
     "- PDF checks: fonts, anomalies, continuation arrows, prime notation, figure references, status paragraph, Sec. 7 counts.",
     "- Visual inspection: all 68 EN and 69 ES pages rendered at 110 dpi and viewed (see PAGE_INSPECTION_LOG.csv). The image tool rate-limited many requests; pages were re-requested until displayed.",
     "- Figures: 4 EN + 4 ES referenced files exist; content and captions agree.", "",
     "## Summary of clean results",
     "- No substantive mathematical divergence: every display/inline math segment is identical EN/ES apart from translated \\text{} words (4 cases).",
     "- All key constants, tags, theorem numbering, citation keys, hashes, URLs, counts and dates agree across EN/ES and MD/TeX.",
     "- No '??', '[?]', U+FFFD or 'Undefined' in either PDF; C\u2032 renders as a prime in body text of both PDFs; Figure 2 reference resolves (p15 -> p16) in both.", "",
     "## Findings", "", "| ID | Severity | File + line / page | Evidence | Description |", "|---|---|---|---|---|"]
for x in findings:
    L.append("| {id} | {severity} | {where} | {evidence} | {description} |".format(**{k: v.replace("|", "/") for k, v in x.items()}))
L += ["", "## Verdict", results["verdict"], "",
      "## Scripts", "scripts/e6_md_compare.py, e6_md_vs_tex.py, e6_md_tex_words.py, e6_qualifiers.py, e6_qual_show.py, e6_rmwords.py, e6_pdf.py, e6_pdf_breaks.py, e6_pdf_breaks2.py, e6_write_deliverables.py; outputs in results/."]
open(E + "E6_RECORD.md", "w", encoding="utf-8").write("\n".join(L) + "\n")
print("written")
