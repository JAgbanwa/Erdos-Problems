# Paper III v1.5 rendered-PDF QA report

**Verdict:** `PASS`

## Frozen rendered targets

| Language | PDF | SHA-256 | Pages |
|---|---|---|---:|
| English | `PAPER_III_preprint_v1.5_en.pdf` | `077a12da4db42ecbe6bcc25333539bf7ee3e63fa20bc7a46d8e801120ac9bb27` | 46 |
| Spanish | `PAPER_III_preprint_v1.5_es.pdf` | `5ed3f83b97f6c900d63d09dd3eb491ed903693df1b90fe0dbac5df2e1e93ec92` | 47 |

Both PDFs were compiled twice with LuaLaTeX from the delivered v1.5 TeX files. The final
logs identify the expected output jobs and contain no fatal error, undefined reference,
undefined citation, missing character, missing glyph or overfull-box diagnostic.

## Inspection performed

All 46 English pages and all 47 Spanish pages were rendered after the final compilation.
The six contact sheets cover every rendered page. Full-resolution inspection included both
title pages, the Appendix D pages changed by the v1.5 clarification, representative theorem,
figure, table and bibliography pages, and the pages adjacent to each changed passage.

The inspection found:

- one centered author block on each title page, with no duplicated lower-left author block;
- correct author metadata rather than the literal generator placeholder;
- no clipped text, overlapping text, missing figure, displaced caption or table overflow;
- no missing glyph or corrupted mathematical escape;
- matching figure order and geometry across the English and Spanish versions;
- clean rendering of the Theorem 2.2 and Appendix D clarifications in both languages.

The English and Spanish page counts differ by one because of normal translation expansion;
the 61-check manuscript-consistency result records no structural or protected-content loss.

