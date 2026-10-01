# E6 — bilingual artifacts (partial)

**Inputs.** EN/ES md, tex, pdf with hashes verified (E0; re-verified inside `e6_auto.py`: `sha256_ok` true for both
PDFs). PDFs were only read; nothing regenerated.

**Method (auditor-written `e6_auto.py`; output `e6_auto.json`, `pdftext_{en,es}.txt`, 101 page rasters in `pages/`).**

| Check | EN | ES | Result |
|---|---|---|---|
| Page count (expected 50 / 51) | 50 | 51 | PASS |
| Fonts | all subset-embedded (prefix `XXXXXX+`) | same | PASS. CORRECTION (auditor): the script's `non_embedded_fonts` list is a false positive — it keyed on the extension field; every listed font carries a subset prefix, i.e. is embedded. |
| U+FFFD replacement glyphs in extracted text | 0 | 0 | PASS |
| `??` / unresolved-reference markers | 0 | 0 | PASS ("Missing" hits are the identifier `ChordalCoreMissing`) |
| Near-blank pages | none | none | PASS |
| Display-math blocks EN vs ES (md, whitespace/`\text` normalised) | 158 | 158 | **identical, 0 differences** |
| Headings | 67 | 67 | PASS |
| Distinctive constants (16, 48, 117/1825, 12687/20000, 19/365, 253/500, 2920, 219, 1600, 87947/44352, 393, 65536, 16384, 57344, 4500, 2208, 105, 59516, 191432, 59517, 10⁻¹⁶, 10⁻¹²) md vs tex, EN vs ES | — | — | consistent across the four sources (only "16" differs md 35 vs tex 39 in **both** languages equally: TeX macros) |
| Numeric-token multiset EN vs ES md | — | — | differences only from a stray `\Needspace{20\baselineskip}` at EN md l.1745 (absent in ES md) and wording ("zero"); no semantic divergence |
| Status language | l.11 / PDF p.1, §7 | same | Current: external review "pending"; no stale v1.0.2/1.0.3 labels; `PASS_INTERNAL_AUTHOR_SIDE` appears only as the author-side record (§7). PASS |
| Attribution of [15] | §1 l.46, §8.1 | §1 l.46, §8.1 l.1029 | Same omission of [15, Thm 1.1] in both languages (E7-F1) |

**Visual inspection.** Only a sample was inspected by eye (EN p. 27, and [15] pages for E7). Observed: code
identifiers are set in roman and broken across lines without any marker (e.g. `PASS_INTERNAL_AU|THOR_SIDE`,
`gain_t|…`, `NearH1CalibratedRo|ot` in ES) — MINOR typographic issue (copy-paste of identifiers breaks).
**Full page-by-page visual inspection of all 101 pages was not performed**: after the E7 blocker, new expensive
work was stopped (request §4.2). Rasters are retained for a later pass.

**Other observations.** `PAPER_IV_preprint_v1.0.1_{en,es}.aux` are present in the candidate directory but not
listed in `MANIFEST.json` (E0) — OBSERVATION.

**E6 = INCONCLUSIVE** (automated checks pass; full visual QA not done; attribution defect shared by both editions).
