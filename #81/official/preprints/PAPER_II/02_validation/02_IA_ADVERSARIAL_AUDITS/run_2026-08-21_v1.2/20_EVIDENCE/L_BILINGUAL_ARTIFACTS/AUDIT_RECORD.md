# Gate L - Bilingual and artifact consistency (PAPER_II, preprint_draft_v1.2)

**Protocol:** `EXTERNAL_AI_ADVERSARIAL_AUDIT_INSTRUCTIONS_v1.1`
**Verdict:** `PASS_WITH_RESIDUALS`

## Method

`scripts/gate_L_check.py`, written for this audit. Display-math blocks are extracted and
all `\text{...}`, `\mathrm{...}` and `\operatorname{...}` prose is blanked, so that
idiomatic Spanish translation of embedded words is ignored and only mathematical
structure is compared, as a **multiset** (immune to ordering, and to a count difference
cascading into spurious mismatches). The check also compares equation tags, code and Lean
identifiers, citation keys, heading hierarchy, and duplicated non-trivial lines - the
last because Paper I v1.2 was found to carry exactly that defect, so it was screened for
here explicitly.

Rendered-page QA used Poppler at 90 dpi with per-page ink analysis.

## Protected-content results

| Item | English | Spanish | Identical |
|---|---|---|---|
| display-math blocks (prose blanked) | 96 | 96 | **yes** - 0 only-EN, 0 only-ES |
| equation tags | 7 | 7 | **yes** |
| code / Lean identifiers | 29 unique | 30 unique | one ES-only: `simp` |
| citation keys | - | - | **yes** |
| headings and level sequence | 52 | 52 | **yes** |

**Zero protected mathematical content diverges.** The single identifier asymmetry is the
Lean tactic name `simp` mentioned once in Spanish prose; it is not a declaration name and
carries no mathematical content.

## Duplicated-content screen (the Paper I defect class)

**Not present.** The duplicated-line classes are symmetric between the two languages:
- the headline `floor((2n+1)^2/24)` display appears 9 times in each language, and the
  `max` operator line 3 times in each - legitimate repetition of the main formula across
  abstract, body and appendix;
- the table header `| Node | Statement | Axiom footprint |` appears twice in each
  language because there are **two** distinct tables (Table 4, the formalization
  perimeter, and Table 5, the arithmetic surface). Verified by reading both regions.

An initial screen flagged the Spanish header as ES-only; that was an artifact of a
40-character length threshold, since the English header is 38 characters. Investigated
and dismissed rather than filed.

## Rendered-page QA

| Artifact | Pages | Producer | Min ink | Anomalies |
|---|---|---|---|---|
| `..._en.pdf` | 23 | LuaTeX-1.24.0 | 1.018% | **0** |
| `..._es.pdf` | 24 | LuaTeX-1.24.0 | 0.653% | **0** |

All 47 pages rendered and analysed. No blank page, no anomalous black area, no malformed
PDF structure. Both A4, unencrypted. The one-page difference is ordinary Spanish text
expansion, not duplicated content - the duplication screen above is what establishes
that.

## Findings

None at this gate.

## Limitations

- The PDFs were **not** independently recompiled from the delivered TeX. Producer strings
  and source-to-PDF text tracking were checked instead.
- Figure resolution and legibility were not separately assessed.
- Per-page visual inspection was performed programmatically (ink and dark-area analysis)
  plus targeted visual reading; not every one of the 47 pages was read by eye.

## Files

`scripts/gate_L_check.py`, `results/en_es_protected_content_diff.json`,
`results/pdf_page_qa_*.json`.
