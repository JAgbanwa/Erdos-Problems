# Paper IV v0.8 — English review edition

## Editorial verdict

`EDITORIAL_DRAFT_WITH_OPEN_GATES`

This is the English counterpart of the Spanish v0.8 review draft, not a new mathematical version or a public release. Both editions remain in `draft_v0.8_es`, as requested. The Spanish manuscript, PDF, figures, reports, source snapshot, and manifest were not modified.

## Authorities and scope

- Semantic source: `PAPER_IV_preprint_v0.8_es.md`, SHA-256 `83823cf8a061934ebe3c6769982d376f06aa7f91274a885eacd20598198b8457`.
- English source: `PAPER_IV_preprint_v0.8_en.md`.
- Layout: the Spanish v0.8 series template, adapted to English and compared with Paper III v1.5 English, including its first page, theorem, figure, table, and reference pages.
- Stage: author-review preprint. A permanent public source commit/link and final author review remain pending, exactly as in the Spanish version.
- No Lean files were edited. No formal build or axiom audit was newly run for this translation. The evidence reported by the manuscript is the frozen v0.8 evidence accompanying the Spanish source.

## Changes

| ID | Location | Editorial change | Mathematical scope |
|:--|:--|:--|:--|
| EN-01 | Entire manuscript | Translated 322 text blocks, including proofs, captions, tables, acknowledgments, and tool disclosure | No new assertions or proof steps |
| EN-02 | Display and inline mathematics | Translated prose inside `\text{...}` using the explicit map in `BILINGUAL_PARITY_v0.8.json` | Symbols, constants, inequalities, and equation labels unchanged |
| EN-03 | Figures 1–3 | English labels in separate `figures_en` assets | Geometry, arrows, resource structure, and numbering unchanged |
| EN-04 | Terminology | Kept graph margin distinct from selector slack; distinguished triangle and mixed gaps | Definitions and hypotheses unchanged |
| EN-05 | Bibliography | English connective prose and dates; references [2]–[4] now use the exact titles of their English editions, checked against the corresponding Paper I–III TeX sources | Same works, 20 reference numbers, URLs, identifiers, and attribution scope; all other titles unchanged |
| EN-06 | §6.1 | Completed the introductory sentence before its display rather than leaving “pieces” after it | Same piece count and argument |
| EN-07 | Figure assets | Renamed the English assets to `fig1_proof_map`, `fig2_host_realization`, and `fig3_budget_comparison`; synchronized Markdown, TeX, and build references | Same figures, numbering, captions, and geometry |
| EN-08 | This report | Translated the research-status field labels into English and corrected the former title-retention policy | No manuscript claim changed |

## Semantic integrity

`check_translation_en.py` verifies the unchanged source hash and exact ordered correspondence of 1,052 protected mathematical/code fragments, allowing only the declared prose-annotation translations. It also verifies all 118 display formulas, equation labels, five literal Lean blocks, inline code identifiers, reference URLs, citation order, heading hierarchy and numerical labels, nine table structures (eight numbered and one notation table), and the three figures in their original order.

The annotation translations do not rename symbols. Subscripts such as `lej`, `cercano`, `est`, `cruz`, and `cub` remain as in the Spanish mathematics so that formulas match literally across editions. Personal names and bibliographic titles other than [2]–[4] are retained. For those three works of this series, the English edition cites the existing English title, not a newly translated or different work.

The review correction is bounded by `EN_REVIEW_CORRECTIONS.json`. Reversing only the three authorized title substitutions and three figure-path substitutions recovers the exact preceding English manuscript hash. Thus all other manuscript prose is unchanged, including the caution that a namespace audit alone does not detect relocated and renamed code; the discharged Vizing input and unused Häggkvist–Janssen input; the stated third-party Mathlib dependency; the limits of the comparison with [15]; both gain conventions; and the triangle/mixed distinction. The user's observation about `GalvinRoute` is not promoted to a new audited claim by this editorial correction.

Editorial review retained the quantifier order, exceptional cases, negations, provenance, conditional statements, and the distinction between the near and global thresholds. It did not attempt to repair or extend the mathematics. The comparisons with other works remain those of the frozen Spanish draft; no new literature review is implied.

## Artifacts and checks

- The delivered TeX is generated from the delivered English Markdown, using `series_template_en.tex`.
- The delivered PDF was compiled from that TeX; `compiler_console_en.log` names the English output.
- English PDF: 40 pages. A different page count from the Spanish edition is expected; section, theorem, equation, table, figure, and reference numbering are unchanged.
- All 40 pages were rendered and inspected in contact sheets after the final source edit; selected pages were also examined at readable scale. See `qa_en/VISUAL_QA.md`.
- No overfull boxes, missing-character warnings, undefined control sequences, replacement glyphs, or off-page text bounds were detected. The renderer reports a local Fontconfig configuration message, but the explicitly selected fonts are present in the resulting PDF and the visual checks passed.
- `BILINGUAL_PARITY_v0.8.json` records the final source/TeX/PDF hashes and checks. `MANIFEST_SHA256_EN.md` seals the English deliverables and their supporting reports without replacing the Spanish manifest.

## Formal-status boundary

The shared `AUDIT_SUMMARY.json` reports 83 main axiom declarations, 57 cone statements, 12 supplement axiom declarations, and 632 bounded-library checks, with 479 unchanged source files. These are inherited evidence counts, not new translation results; their scopes overlap and are not summed. The local Lean snapshot retains SHA-256 `4f6ba1b40ace1d926ae5fab7490c4bc0dc3f236dea28640de4cee0166da60afa`.

## Remaining actions

No new content query was introduced by the translation. Final author review of the English wording and the existing public-release gates remain open. Suggested next steps are a bilingual author review, a referee package using the same frozen mathematical sources, and assignment of the canonical public source cut before release.

## Research status checklist

- Active plan: English counterpart of the frozen Spanish v0.8 draft.
- Result: Markdown, TeX, and rendered PDF in the same folder.
- Mathematical status: unchanged; this translation is not a new proof audit.
- Dependencies: original v0.8 source snapshot and recorded audit evidence.
- Pending: author review and public source cut/link.
- Next action: collect wording corrections on the English review draft.
