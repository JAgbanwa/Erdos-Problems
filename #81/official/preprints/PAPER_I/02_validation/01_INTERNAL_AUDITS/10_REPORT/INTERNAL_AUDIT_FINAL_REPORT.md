# Paper I v1.3 internal audit final report

> **Overall verdict:** `PASS`  
> **Audit class:** internal / author-side / not external  
> **Protocol:** `INTERNAL_AUDIT_STANDARD_v1.3`  
> **Date:** 2026-08-21  
> **Lean execution:** recorded full build and external clean-room result reviewed; Lean not rerun

## Frozen target

| Item | Value |
|---|---|
| English manuscript SHA-256 | `f3094b670c93ff622c3f573cdab61bdd0f5d84007f04b1888b364e0183565bea` |
| Spanish manuscript SHA-256 | `57ba967fc2de805b7bbb4cf5f937727bde43c2ada80fa794bcbb5a727db05b8b` |
| English PDF SHA-256 | `7d04c47692b613c8d6e2cc4471f0205128b4ae06ca11d581a08d020eb2236db0` |
| Spanish PDF SHA-256 | `3ad16ae86e8fcad358bf964a6ae98ae053b0bde2fdf3140e008cedab78b90c2a` |
| Formal archive | `PAPER_I_lean_v1.2_freeze.zip` |
| Formal archive SHA-256 | `0181506408644fc1f8872d711de5a98a500f4052aa295bcd6f8c82776694fd3a` |
| Lean / Mathlib | Lean 4.28.0 / Mathlib `8f9d9cff6bd728b17a24e163c9402775d9e6a365` |
| Recorded full build | exit 0; 8,034 jobs |
| Recorded axiom footprint | `propext`, `Classical.choice`, `Quot.sound` |

## Gate results

| Gate | Verdict | Principal evidence |
|---|---|---|
| G0 Target | `PASS` | 95 static/integrity/residual controls; six LF-sealed artifacts; manifests verified |
| G1 Claims | `PASS_AFTER_CORRECTION` | Eight external findings resolved; one residual citation reference found internally, corrected and rerun |
| G2 Mathematics | `PASS` | 5 identities; 561 boundary; 480 orbit; 99,671 assembly; 1,179 split-LP; 9 sharpness checks |
| G3 Formal conformance | `PASS` | Headline, assembly and residual-duality surfaces match the unchanged archive |
| G4 Recorded build | `PASS_RECORDED_BUILD` | 8,034-job record and 15-surface axiom report reviewed; no Lean rerun |
| G5 Bilingual | `PASS` | EN/ES aligned; known-block controls and general exact/near-duplicate scan pass |
| G6 TeX/PDF | `PASS` | EN 19 / ES 20 pages; clean logs, embedded fonts and 39 pages visually inspected |
| G7 Prior art | `PASS_INTERNAL` | Primary CEO scan added; novelty wording remains scoped; specialist gate open |
| G8 Package | `PASS` | Self-contained v1.3 target, correction matrix and evidence perimeter |

## Correction disposition

The v1.3 manuscript resolves all eight findings in the external v1.2 report:
Spanish duplication, stale integrity baseline, exposition of (4.7), the domain
of Appendix A.2, the scope of “sharp,” CEO primary-source access, the
Schrijver pinpoint, and the unused repository reference. During the internal
rerun, `P1-IA-V13-001` found one remaining textual occurrence of the unverified
Schrijver pinpoint. It was corrected in both languages and formats; the PDFs,
hashes and all downstream gates were regenerated and rerun.

These corrections do not alter a theorem, hypothesis, numerical constant,
proof step or Lean source. The formal archive is byte-identical to the archive
already rebuilt independently by the external auditor.

## Overall verdict

`PASS`. All nine blocking internal gates pass. There are no unresolved internal
blockers or major findings. Residual external adversarial validation,
independent specialist prior-art review, human peer review, tagging and
publication approval remain open external gates.
