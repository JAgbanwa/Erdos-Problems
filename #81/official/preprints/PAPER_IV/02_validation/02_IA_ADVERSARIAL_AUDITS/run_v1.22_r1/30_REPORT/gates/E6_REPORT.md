# Gate E6 report — run_v1.22_r1 (Paper IV v1.22-r1)

Verdict: **PASS_WITH_FINDINGS**. Evidence: `20_EVIDENCE/E6/`. Auditor: Claude Opus 5.5, same session as run_v1.2_r1/run_v1.21_r1; no Lean executed.

---

# E6 — Bilingual parity, rendering and presentation (v1.22)

The inputs are the final v1.22 MD, TeX and PDF files bound by the manifest (E0). No earlier renders were used.

## Method
- **Automated parity** (`e6_parity.py` → `E6_PARITY.json`), against v1.21 and between EN and ES:
  - EN goes from 230 to 237 display formulas and ES from 230 to 237; 7 are added in each language and none removed.
  - Equation tags and Lean code blocks are identical to v1.21 in both languages. Theorem-heading lines are unchanged (33 EN, 34 ES).
  - The EN and ES display sequences are equal (237 = 237; no mismatch after normalising `\text{}`).
  - Reference titles differ only for [2]–[4], the author's own Papers, which have legitimate Spanish titles.
- **Residual-term scan** (`scripts/e6_x15_new01_scan.py` → `E6_X15_NEW01_SCAN.json`).
- **Visual inspection of every page.**
  - `scripts/make_pairs.py` renders the bound PDFs at 90 dpi as 2-up sheets (`pairs/`): EN 72 pages and ES 73 pages.
  - All 145 pages are logged in `PAGE_INSPECTION_LOG.csv` (138 VIEWED_OK, 7 VIEWED_FINDING).
  - Changed pages, identifiers, the stability figure and the bibliography were also inspected at 130 dpi (`zoom/`, `ZOOM_VIEW_LOG.csv`).
  - Coverage rule (see CORRECTIONS C2-02…C2-05): a page is logged only from a sheet that is visible to the auditor when the row is written. Discarded and unconfirmed intermediate logs are kept for transparency.
- The author's response and `VISUAL_REVIEW_v1.22.md` were contrasted after the inspection.

## Rendering
No overlaps, clipping, empty pages, overflowing formulas, missing glyphs or undefined references were seen on any page. The new C.3 text (EN pp. 48–51, ES pp. 49–52) is legible at 90 and 130 dpi, as is Table C.1. Long identifiers carry the typographic continuation arrow.

## Mandated items

| Item | Evidence | Result |
|---|---|---|
| C.3 formulas, ES/EN | Parity: the 7 added displays are identical in both languages. 130 dpi: EN p50–51 and ES p51–52 have the same chain, constants and tags (C.3), (C.4). | **OK** |
| Statements, final constants, tags | Tags equal to v1.21; heading lines unchanged; the diff shows no change to a statement. | **Unchanged** |
| X-12: `E34.lemma3`, `E34.transfer` | EN p65 "This is E34.lemma3." and Table 10 "E34.transfer" on p66, both monospaced (130 dpi). ES p67, same (130 dpi). | **RESOLVED** |
| NEW-01: Regularization/Nibble descriptive; `Model` as namespace | EN §5.1 heading (p13), A.2 row (p40) and the ES Lemma 3.2 heading (p44) are now plain text. EN §7.2 has "bounded gain function from `Model`" in code (p34). **ES §7.2 still has "función de ganancia acotada de Model" in roman type** (MD l.1203, TeX l.1084, PDF p35). In v1.2 the ES text had `` `Model` ``. | **PARTIAL** (MINOR). The ES residual was also missed by run_v1.21_r1 (CORRECTIONS C2-08). |
| X-15: emparejamientos/empaquetamiento in prose; "valor base" in the figure; cited titles untranslated | Figure 3, ES p26 at 130 dpi: "Cotas de edición y valor base (6.12)". **Fixed.** Cited titles are kept ([6], [7], [9]). **ES prose still contains 12 English terms**: "matchings" at MD l.526, 578, 746 (×2); "matching" at l.1892, 1917, 1959, 2177, 2182 (×2), 2184; "packing" at l.688 ("ni otro packing"). These fall on PDF pp. 16, 18, 20, 21, 55, 56 and 61 and are also in the TeX. This is the same set of 12 + 1 listed by run_v1.21_r1 (line numbers shifted by the C.3 insertion). | **PARTIAL** (MINOR). See the discrepancy below. |
| NEW-02: original title of [6] | EN p71 and ES p72 (130 dpi): «Integer and fractional packings in dense graphs». | **RESOLVED** |
| Preference Labs spelling | EN p71 "Jacobian at Preference Labs"; ES p72 "Jacobian de Preference Labs". | **RESOLVED** (X-10 observation closed) |
| X-27: dependency disclosure and real independence scope | EN p31 / ES p31: the E32 classification wrappers still use the historical Alon–Shapira chain, and the exclusion check is not extended to them. Table 9 keeps the E32 entry (EN p64 / ES p65). [23] keeps its use statement (EN p72). | **Preserved** |
| Bibliography result of the earlier audit | Unchanged apart from NEW-02 and the spelling fix. Not widened. | **OK** |

## Discrepancy with the author's response
`RESPONSE_TO_REVALIDATION_v1.22.md` (X-15 row) states that the matching/packing residues in Spanish prose are translated. In fact, only the figure label changed; none of the 13 prose occurrences was translated. The response's NEW-01 row ("Se restaura el formato del namespace Model donde corresponde") holds for EN only. `VISUAL_REVIEW_v1.22.md` reports "valor base" and [6], which is correct, and does not claim the prose translation. **Severity: MINOR** (presentation; no mathematical content).

## E6 verdict
**PASS_WITH_FINDINGS.** Everything renders, and parity of all formulas, tags and statements holds. X-12, NEW-02 and Preference Labs are resolved; X-27 is preserved. Two MINOR, non-blocking presentation residuals remain in the Spanish edition: X-15 (prose) and NEW-01 (ES §7.2 `Model`).
