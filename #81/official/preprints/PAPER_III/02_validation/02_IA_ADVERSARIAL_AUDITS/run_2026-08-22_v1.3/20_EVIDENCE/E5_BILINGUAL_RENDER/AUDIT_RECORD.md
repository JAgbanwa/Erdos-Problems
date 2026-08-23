# E5 -- bilingual, format and render consistency

**Verdict: `FAIL`**, on one divergence. Everything else passes.

## Renders

Every page of both PDFs rendered at 60 dpi and measured.

| | EN | ES |
|---|---|---|
| pages | 45 | 46 |
| blank or near-blank | **none** | **none** |
| right-margin overflow | **none** | **none** |
| bottom-margin overflow | **none** | **none** |
| ink range | 1.22%-9.20% | 1.43%-8.58% |
| producer | LuaTeX-1.24.0 | LuaTeX-1.24.0 |

MD -> TeX -> PDF fidelity, both languages: **66/66** equation tags, **20/20** theorem numbers,
**17/17** references, **42/42** formal identifiers present in the generated TeX and in the
extracted PDF text.

Structural EN/ES agreement: 144 headings with identical level sequence, 66 identical equation
tags, 17 identical references, identical theorem numbering, identical formal identifiers.

## Named regressions, closed

`A_{2J}`: **zero** occurrences of the variant `A_{2,J}` anywhere, Markdown or TeX, either
language. `[3,8]`: 2 EN / 2 ES. `[11,17]`: 2 EN / 2 ES. The corrected split-case scope is
present and symmetric. No stale version label in any publication artifact.

## The divergence

**Proposition 7.4.** English gives full hypotheses including `h_i >= max{rho, q_J - r_b}` plus
the explicit inequality with `A_J`, `A_{2J}`, `B_J`. Spanish replaces the hypothesis with a
reference to Section 7 and **the entire conclusion** with "vale la cota exacta
`reserved_gain_packing_bound_subset` mostrada allí" -- and Section 7 in Spanish contains no such
formula; it is in Appendix E.1.3, which *is* identical in both languages. The divergence
propagates to the TeX, so it is EN/ES rather than MD/TeX. See `EXT-V13-002`.

## Auditor artifacts recorded

1. A naive extraction reported 16,368 replacement characters in the English PDF text. The
   bytes are **CESU-8** -- poppler's non-standard encoding for astral-plane characters -- and
   are not valid strict UTF-8. Decoded correctly, **zero** replacements remain and the
   recovered characters are exactly the intended mathematical italics (`U+1D43A` `G`,
   `U+1D45D` `p`, `U+1D708` `nu`, ...). The PDF text layer is correct.
2. 17 formal identifiers appeared absent from the TeX; all 17 are present with escaped
   underscores. MD -> TeX is 42/42.

Evidence: `scripts/v13_E5_pdf_qa.py`, `results/E5_pdf_qa.json`, per-page renders retained.
