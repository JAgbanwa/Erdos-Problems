# Paper I v1.2 internal audit final report

> **Overall verdict:** `PASS`  
> **Audit class:** internal / author-side / not external  
> **Protocol:** `INTERNAL_AUDIT_STANDARD_v1.3`  
> **Date:** 2026-08-21  
> **Lean execution:** recorded full build reviewed; full build not rerun

## Frozen target

| Item | Value |
|---|---|
| English manuscript SHA-256 | `da7e48196a03a8698a9c5a503976b43780cb9e5309558f1b7d3e06b4af35ee9e` |
| Spanish manuscript SHA-256 | `a6b14c85abdb872c21187d13889038f5aa2a16fae5caf8d6781ff998a20ed847` |
| Formal archive | `PAPER_I_lean_v1.2_freeze.zip` |
| Formal archive SHA-256 | `0181506408644fc1f8872d711de5a98a500f4052aa295bcd6f8c82776694fd3a` |
| Lean / Mathlib | Lean 4.28.0 / Mathlib `8f9d9cff6bd728b17a24e163c9402775d9e6a365` |
| Recorded full build | exit 0; 8,034 jobs |
| Recorded axiom footprint | `propext`, `Classical.choice`, `Quot.sound` |

## Gate results

| Gate | Verdict | Principal evidence |
|---|---|---|
| G0 Target | `PASS` | 59 static/integrity checks; six LF-sealed artifacts; archive, source and package manifests verified |
| G1 Claims | `PASS_AFTER_CORRECTION` | Exact freeze provenance, sharp assembly, duality namespaces and tightness qualification matched |
| G2 Mathematics | `PASS` | 5 identities; 561 boundary regressions; 480 orbit LPs; 99,671 assembly cases; 1,179 split LPs; 9 sharpness cases |
| G3 Formal conformance | `PASS` | `paperI_main_sharp`, `assembly_sharp` and `residual_duality` matched to manuscript roles |
| G4 Recorded build | `PASS_RECORDED_BUILD` | 8,034-job log plus corrective 15-surface axiom report reviewed; no full rebuild |
| G5 Bilingual | `PASS` | 33/33 headings, two figures and 15 protected identifiers aligned |
| G6 TeX/PDF | `PASS` | EN 19 / ES 20 pages, embedded fonts and all pages visually inspected |
| G7 Prior art | `PASS_INTERNAL` | Scoped negative literature result; specialist external review remains open |
| G8 Package | `PASS` | Self-contained manuscript and exact v1.2 evidence perimeter |

## Corrective batch admitted before the rerun

- Replaced the nonexistent archive name/hash in all manuscript formats with the delivered v1.2 archive and hash.
- Regenerated the six-artifact sidecar with LF-only line endings.
- Added exact axiom queries for `PaperI.assembly_sharp` and `PaperI.Split.residual_duality`.
- Qualified the (s=2) tightness statement by (o\ge1), retaining ((2,4,2)) as the zero-slack equality case.
- Removed prior-version narrative from the manuscript; release history remains package metadata only.

The corrections do not change a theorem, hypothesis, constant or proof step.

## Overall verdict

`PASS`. All nine blocking internal gates pass. There are no unresolved internal blocker or major findings. Independent reconstruction, external adversarial audit, specialist prior-art review, peer review, tagging and publication approval remain open external gates.
