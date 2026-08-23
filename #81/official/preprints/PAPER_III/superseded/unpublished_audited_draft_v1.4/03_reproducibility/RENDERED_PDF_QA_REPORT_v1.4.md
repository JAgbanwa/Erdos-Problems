# Paper III v1.4 rendered-PDF QA

**Verdict:** `PASS`  
**Date:** 2026-08-22  
**Method:** both final PDFs were rendered at 150 dpi to page PNGs and inspected page by page through complete contact sheets; critical pages were then inspected at original rendered resolution.

## Frozen PDF targets

| Artifact | SHA-256 | Pages |
|---|---|---:|
| English PDF | `afd00647f22b97fd2f761ed052857e4273bc88cb265b9d1af8dad347ba943702` | 46 |
| Spanish PDF | `5804253aabc815bc0092048c47289f2956273a0a477b4e1b5a7c8906987ee8d4` | 47 |

## Inspection coverage

- All 46 English pages and all 47 Spanish pages occur exactly once in the render sets.
- Full-resolution inspection covered both title pages, the complete-split figure, dense formalization tables, the Proposition 7.4 correction, the `q=0` benchmark clause, and the final reference pages.
- After the external M01 correction, all 47 Spanish pages were rendered again at 150 dpi; page 8, containing Section 2.4, was inspected at original rendered resolution.
- Figures render identically in role and placement across languages.
- Tables remain inside the text block; long Lean identifiers break without clipping.
- No missing glyph, overlapping object, cropped formula, broken image, blank content page, duplicated page, or TeX residue was observed.
- Final TeX logs contain no fatal error, undefined reference/citation, missing-character warning, or overfull box. The inherited Cascadia Mono font-shape substitution warning does not indicate a missing font or glyph.

## Result

`PASS`. The two PDFs are visually suitable for the corrected v1.4 internal-audit target. The English PDF is byte-identical to the externally audited target. This is layout QA, not mathematical or external publication approval.
