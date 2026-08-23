# Paper III v1.5 internal residual audit protocol

## Scope

This is an internal, author-side, non-independent residual audit of the v1.5 release
candidate against the preserved, externally audited v1.4 baseline. It reviews the protected
editorial delta and the complete publication-artifact chain. It does not rerun Lean.

## Regression boundary

The v1.5 change set is limited to the explicit `EXT-V14C-N02` and `EXT-V14C-N03`
clarifications, release-status wording, filenames, author-block generation, PDF metadata,
README/HTML/citation metadata and their regenerated artifacts. The formal freeze remains
`PAPER_III_lean_v1.4_freeze.zip`, SHA-256
`79ee24c38fd776bc2585a0c3c996e30817f0829fc5064463bdbde0fa2d3d7104`.

## Gates

| Gate | Requirement |
|---|---|
| G0 | exact v1.5 target, LF-only six-artifact sidecar and no active draft-named manuscript |
| G1 | protected semantic delta, unchanged displayed mathematics/tags/order/citations, N02/N03 in both languages |
| G2 | preservation of v1.4 internal/external PASS and the prior independent mathematical review |
| G3 | Lean archive, manifests, CRC and all 707 manifested sources byte-identical to v1.4 |
| G4 | recorded independent build/axiom evidence reviewed without rebuilding Lean |
| G5 | bilingual parity, 61-check conversion suite, duplicate-text and scope controls |
| G6 | final TeX/PDF/log/page-render/font/metadata QA |
| G7 | E2/E6 carry-forward, corpus-bounded novelty and review limitations |
| G8 | active package hygiene, citation metadata, README/HTML links and absence of stale generic evidence shadowing current versioned evidence |

Every gate must be `PASS`. A failed check is corrected only within its authorized layer and
the complete residual suite is rerun. No earlier sealed audit report may be rewritten.
