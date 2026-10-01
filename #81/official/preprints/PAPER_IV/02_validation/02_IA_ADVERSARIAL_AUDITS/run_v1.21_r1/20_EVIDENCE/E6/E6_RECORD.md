# E6 — Bilingual artifacts revalidation (v1.21)

**Coverage.**
- Identities: all six target files (EN/ES × MD/TeX/PDF) match `E0_INITIAL.json`. Page counts are EN 71 and
  ES 72 (pymupdf).
- Automated parity: done by the delegated sub-agent (same model) before two rate-limit interruptions. Its
  outputs are in `results/`: equation/section reference parity, key-number counts across the four
  sources, a prime check, headings set as code, a "holgura" scan, line alignment, and PDF text and font
  checks.
- Page inspection: after the second interruption the lead auditor rendered both PDFs again at 90 dpi as
  2-up sheets (`scripts/make_pairs.py`, `pairs/`) and viewed every sheet itself: **143/143 pages**
  (71 EN + 72 ES), logged in `PAGE_INSPECTION_LOG.csv`. Zooms in `results/` (binder, figures) were used
  where needed. Because of the 90 dpi 2-up render, fine glyph defects on dense pages may have been missed.

**Parity.**
- Key numbers of the new passages (33δ, 138δ, 11δ, 23δ, 2208, 59485, a₀+31, 191424, 12748, 12749, 392,
  ρ/40, ρ/200, 10^10, n/9, 4n/10⁴, 2^-59485) occur the same number of times in EN.md, ES.md, EN.tex and
  ES.tex.
- No "§3.2" remains. C′ is a typographic prime in MD; the TeX uses C' in math (renders as a prime in both
  PDFs).
- The Figure 2 reference (EN p.15 → figure on p.16; ES p.16) and the new Figure 3 citation in §6.6
  (EN p.25 → p.26; ES p.26) resolve correctly.
- The page-1 status paragraph is accurate in both editions.

## Resolution of earlier findings

| ID | Status | Evidence |
|---|---|---|
| X-04 "holgura" for the margin | **RESOLVED** | ES uses "margen" for Δ(G) everywhere (incl. §3 title "régimen con margen"); "holgura" survives only as "holgura del selector" (l.159) and for the slack nibble (Lemma 3.2 title, l.1461), which is the selector-slack notion. |
| X-12 Lean identifiers in roman / unmarked breaks | **PARTIAL** | Breaks now carry the continuation arrow throughout (e.g. EN pp.17, 22, 31–33, 39, 64; ES pp.17, 31–33, 39, 41, 61). Residual: `E34.lemma3` and `E34.transfer` are still plain text in MD l.2342/2348 (EN p.64–65; ES p.66). |
| X-13 Spanish subscripts in EN math | **RESOLVED** | far, cross, clean and covered appear in both languages; mis_c is defined. |
| X-14 literal Lean excerpt | **RESOLVED** | EN p.39 and ES p.40: strict-implicit binder ⦃v : V⦄ and indentation are preserved. |
| X-15 untranslated English words in ES | **PARTIAL** | baseline/build/target/log/gap were translated. Residual: "matching(s)" ×12 in prose (e.g. l.526, 578, 746, 1845, 1870, 1912, 2130–2137), "ni otro packing" (l.688), and "Cotas de edición y baseline" inside the ES Figure 3 (rendered p.26). |
| X-16 "§3.2" | **RESOLVED** | A.2 row now reads "Lemma 3.2 and C.1–C.2" / "Lema 3.2 y C.1–C.2". |

## New findings (v1.21)

| ID | Severity | Location | Description |
|---|---|---|---|
| NEW-02 | **MINOR** (bibliographic) | ES md l.2484; ES PDF p.71 | The translation pass altered a cited title. The Haxell–Rödl reference [6] now reads «Integer and fractional **empaquetamientos** in dense graphs». v1.2 ES and v1.21 EN have the correct title «Integer and fractional packings in dense graphs». The author's response says bibliographic titles were not translated, so this is an accidental corruption of the reference list. |
| NEW-01 | MINOR | EN §5.1 heading (p.13) and A.2 row (p.40); ES Lemma 3.2 heading (p.44) | Descriptive words are typeset as code identifiers (`Regularization`, `Nibble`). The headings are inconsistent between languages: EN "5.1. `Regularization`…" vs ES "5.1. Regularización…"; ES "Lema 3.2. `Nibble`…" vs EN "Bounded-rank nibble". |
| OBS-1 | OBSERVATION | EN §7.2 | "the bounded gain function from Model" lost its code markup, although it names the Lean namespace `Model`. |
| OBS-2 | OBSERVATION | ES p.33 | `#check` is rendered with letter-spacing; the text remains legible. |
| OBS-3 | OBSERVATION | EN p.70 / ES p.71 | The reference [5] note writes "PreferenceLabs"; the README writes "Preference Labs". |

**E6 verdict: PASS with findings.** No statement, number or qualifier differs between EN and ES. One new
MINOR bibliographic error (NEW-02). Two earlier findings are only partially resolved (X-12, X-15).
