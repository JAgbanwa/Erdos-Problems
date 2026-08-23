# EXT-V14-M01 correction evidence

## Correction

The Spanish Section 2.4 sentence now states that Sections 5--7 and Proposition 10.5
use no asymptotic input, while still using standard facts such as complete-graph edge
coloring. This restores the scope of the English source and removes the non-self-contained
reference to earlier versions.

## Derived-artifact chain

- Spanish Markdown SHA-256: `83e3844e5b62ddeb8cebed46d1557e692f94b5ed25bb683f6b6e173f8ebfe15c`.
- Spanish LaTeX SHA-256: `fbf30d758c849fb062f1619f18e2c2ca68b0e6ddaf69f8741b9fde8eee756910`.
- Spanish PDF SHA-256: `5804253aabc815bc0092048c47289f2956273a0a477b4e1b5a7c8906987ee8d4`.
- The consistency suite passes 51/51 with 144 headings in each language.
- Both Markdown sources contain zero duplicated long paragraphs.
- The final Spanish TeX log contains no fatal error, undefined citation/reference,
  missing character, or overfull box.
- All 47 Spanish PDF pages were rerendered at 150 dpi. Page 8, containing the
  correction, was inspected at full rendered resolution and has no clipping,
  collision, missing glyph, or broken hierarchy.

## Regression boundary

The English Markdown, LaTeX, and PDF remain byte-identical at their externally audited
hashes. The Lean v1.4 freeze archive remains byte-identical. No Lean build was run.

**Verdict:** `PASS_INTERNAL`.
