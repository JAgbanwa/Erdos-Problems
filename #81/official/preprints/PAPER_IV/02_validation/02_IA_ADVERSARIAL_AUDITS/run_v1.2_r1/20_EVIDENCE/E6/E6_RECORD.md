# E6 — Bilingual artifacts audit record (Paper IV v1.2)

Run: run_v1.2_r1 · Date: 2026-09-30 · Sub-auditor: E6

## Identity
All six bound files match the expected SHA-256 (see E6_RESULTS.json). Page counts EN 68 / ES 69 as stated.

## Coverage
- Automated EN/ES comparison of MD and TeX: math segments (1988/1988 MD, 2045/2045 TeX), tags, citations, identifiers, URLs, hashes, numbers, headings.
- MD vs TeX word-level comparison per language.
- Qualifier survival: 486 aligned paragraphs (regex) plus manual side-by-side reading of the key statements listed in the brief.
- PDF checks: fonts, anomalies, continuation arrows, prime notation, figure references, status paragraph, Sec. 7 counts.
- Visual inspection: all 68 EN and 69 ES pages rendered at 110 dpi and viewed (see PAGE_INSPECTION_LOG.csv). The image tool rate-limited many requests; pages were re-requested until displayed.
- Figures: 4 EN + 4 ES referenced files exist; content and captions agree.

## Summary of clean results
- No substantive mathematical divergence: every display/inline math segment is identical EN/ES apart from translated \text{} words (4 cases).
- All key constants, tags, theorem numbering, citation keys, hashes, URLs, counts and dates agree across EN/ES and MD/TeX.
- No '??', '[?]', U+FFFD or 'Undefined' in either PDF; C′ renders as a prime in body text of both PDFs; Figure 2 reference resolves (p15 -> p16) in both.

## Findings

| ID | Severity | File + line / page | Evidence | Description |
|---|---|---|---|---|
| E6-01 | MODERATE | ES md 37, 150, 269 (Sec. 3 title), 303; ES pdf p5-p10; cf. EN md 37,150,269,303 and EN/ES md 159 | EN 'margin' is rendered 'holgura' (ES 150: 'una perdida menor que la holgura en el regimen lejano'; 269: 'Redondeo mixto y regimen con holgura'; 303: 'menor que la holgura de la instancia'), while ES 159 defines 'margen' = Delta(G) and 'holgura del selector' = unused auxiliary capacity and says the latter 'no debe confundirse con el margen del grafo'. EN keeps 'margin' vs 'selector slack' distinct. | Terminology conflict in the ES edition: the term the paper reserves for selector slack is used for the graph margin in four places, blurring a distinction the text itself declares essential. Substantive translation defect (meaning), not a math change. |
| E6-02 | MINOR | EN pdf p31 (Defect-SharpPublication, PublicationIncrementAu-dit, Optimal-TemplateObstructionAudit, Release-ExportCheck), p63 (FD-Check.ASCheck); ES pdf p27 (NormalizedStabi-lity), p31 (DefectSharp-Publication, ResearchAu-dit), p33 (OptimalTemplateObs-tructionAudit), p65 (FD-Check.ASCheck); TeX EN 1005/1007/1058/2160 (same in ES) | These Lean names are set in roman (not {\ttfamily}) in TeX and in plain text in MD, so TeX hyphenates them with an ordinary hyphen and no continuation arrow. | Contradicts the declared convention in Sec. 7 ('Formal identifiers are printed in monospaced type. A continuation arrow at a line break is a typesetting marker'). A reader may copy e.g. 'FD-Check.ASCheck'. All monospace breaks do carry the arrow (45 EN / 49 ES markers found). |
| E6-03 | MINOR | EN md 726-727 (N_lej), 819 (e_int, e_cruz), 1610 (x^limpio), 1661, 1685 (N_lejano), 1734 (E_cub), 2333 (mis_c); EN pdf p21, p23, p47, p48, p49, App. F.5 | Spanish-derived subscripts inside math of the EN edition, e.g. \(N_{\mathrm{lej}}\), \(e_{\rm cruz}(C)\), \(x_K^{\rm limpio}\), \(N_{\rm lejano}(\eta_0)\le T(h+7)\). | Wrong-language fragments left in the English edition (math identical to ES by construction, which is why the math-sequence comparison is clean). Notation otherwise consistent; no meaning change. |
| E6-04 | MINOR | EN pdf p38-39, ES pdf p39-40 (A.1 'Literal definitions'); TeX EN/ES 1261-1300 vs MD 1303-1345 | MD code block has '\u2200 \u2983v : V\u2984' (strict-implicit binder) and indented structure fields; TeX renders '\{\!\{v : V\}\!\}' -> PDF shows '{{v : V}}', and leading indentation is lost (fields of 'structure CliquePartition' flush-left, double-spaced). | The text calls these 'literal definitions ... omitting proofs but not hypotheses'; the PDF rendering is not literal Lean syntax. MD vs TeX/PDF mismatch in both languages (no semantic change to the statements). |
| E6-05 | MINOR | ES md 1034 ('Restar este baseline'), 1351 ('un build exitoso'), 1371 ('packings'), 1375 ('target', 'log'), 2351-2362 ('gap mixto', 'gap triangular'); ES pdf p28, p40-41, p51, p65 | Untranslated English words in ES prose, while elsewhere ES uses 'valor base', 'compilacion', 'empaquetamientos', 'brecha'. Title of App. G uses 'Brechas' but G.1 body uses 'gap'. | Translation-quality / terminology consistency defects; translation-equivalent in meaning. |
| E6-06 | OBSERVATION | ES md 45 vs 1070 vs 1257; ES md 1438; ES md 1189; ES md 837 | 'estrella con signos' (45, 1257) vs 'estrella con pesos de ambos signos' (1070); 'explicit hypothesis' -> 'hipotesis visible'; 'explicitly attributed support' -> 'soporte identificado'; Thm 6.1 'Existe gamma>0 y un umbral ... tales que' (agreement). | Minor nuance/consistency differences; qualifiers otherwise preserved. Classified translation-equivalent. |
| E6-07 | OBSERVATION | PDF outline (bookmarks) EN and ES; TeX \texorpdfstring{C\ensuremath{^{\prime}}}{C'} (13x each) | Bookmark titles read "Theorem C'. Fixed-defect ..." / "Teorema C'. ..." with ASCII apostrophe; body text renders C\u2032 correctly (18 occurrences per PDF, 0 apostrophe variants). | Prime notation is correct in body text of both PDFs and in Figure 3; only bookmarks use the ASCII fallback. |
| E6-08 | OBSERVATION | figures/ and figures_en/ file names; TeX 187, 502, 846, 1131; MD 180, 522, 940-942, 1228 | Figure numbers vs file names: EN fig1_proof_map=Fig.1, fig2_host_realization=Fig.2, fig4_same_root_stability=Fig.3, fig3_budget_comparison=Fig.4; ES fig2_prueba_y_variantes=Fig.1, fig3_anfitrion=Fig.2, fig4_same_root_stability=Fig.3, fig1_presupuesto_comparado=Fig.4. All 4+4 referenced PDFs/PNGs exist. Only Figure 3 has an explicit 'Figure 3.' label in MD; Figure 3 is never cited in running text (EN/ES). | No broken reference; file-name/number mismatch is a maintenance hazard. Captions and figure contents agree EN/ES (labels translated, numbers/refs such as (6.12)-(6.16), Prop. 6.3a, Cor. 6.3 identical). |
| E6-09 | OBSERVATION | EN/ES PDFs, fonts from figure PDFs | 17 Type3 fonts (DejaVuSans/Serif, STIXNonUnicode) reported with ext 'n/a' by pymupdf; all Type0/Type1 text fonts embedded as subsets. | Type3 fonts are embedded glyph procedures (render correctly) but some journal/arXiv pipelines flag them. |
| E6-10 | OBSERVATION | ES pdf p32->p33 ('MixedRoundin' arrow at page foot); ES pdf p33 ('import' / 'PaperIV' split at line end) | Continuation arrow at a page break inside MixedRoundingAdapter; 'import\ PaperIV' broken at the control space without marker. | Legal under the stated convention (first) / cosmetic (second). |
| E6-11 | OBSERVATION | MD EN/ES vs TeX EN/ES (identifiers) | 208 backtick identifiers in MD vs 260 monospace identifiers in TeX; 52 Lean names (e.g. E35.Fexp_le_tower, FREEZE_SCOPE.json, A.1/F.4 table entries, F.5 lemma names) are plain text in MD. | Presentation inconsistency MD vs TeX (identical in both languages); text content is identical (word-level diff shows only markup). |
| E6-12 | OBSERVATION | EN md 1899-1901 | Three consecutive blank lines after (E.2d) paragraph in EN MD (ES has one); causes the EN/ES MD 2-line offset after 1899. | Cosmetic source-only. |

## Verdict
PASS WITH MINOR ISSUES: no substantive mathematical or numerical divergence EN/ES or MD/TeX; one MODERATE terminology defect in ES (E6-01), several MINOR typesetting/translation defects.

## Scripts
scripts/e6_md_compare.py, e6_md_vs_tex.py, e6_md_tex_words.py, e6_qualifiers.py, e6_qual_show.py, e6_rmwords.py, e6_pdf.py, e6_pdf_breaks.py, e6_pdf_breaks2.py, e6_write_deliverables.py; outputs in results/.
