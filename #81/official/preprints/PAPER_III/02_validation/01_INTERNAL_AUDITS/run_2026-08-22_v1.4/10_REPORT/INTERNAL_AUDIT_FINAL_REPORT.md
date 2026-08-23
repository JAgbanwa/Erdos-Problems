# Paper III v1.4 internal audit final report

> **Overall verdict:** `PASS`  
> **Audit class:** internal / author-side / not independent  
> **Date:** 2026-08-22  
> **Lean execution during audit:** recorded evidence inspected; full Lean build not rerun

## Frozen target

| Item | Value |
|---|---|
| English MD / TeX / PDF | `eea753a4…` / `5e3cf6da…` / `afd00647…` |
| Spanish MD / TeX / PDF | `748a8330…` / `62acd23f…` / `0f93b4b5…` |
| Formal archive | `PAPER_III_lean_v1.4_freeze.zip` |
| Formal archive SHA-256 | `79ee24c38fd776bc2585a0c3c996e30817f0829fc5064463bdbde0fa2d3d7104` |
| Toolchain | Lean 4.28.0; Mathlib commit `8f9d9cff6bd728b17a24e163c9402775d9e6a365` |
| Recorded build | `PASS_CLEAN_ORIGIN_RESUMED`; public root 8,455 jobs; query roots 8,444 jobs |
| Axiom gate | 8 files; 42 queries; 35 distinct surfaces; no `sorryAx`; foundational-only union |

## Gate results

| Gate | Verdict | Principal evidence |
|---|---|---|
| G0 Target | `PASS` | six portable hashes; 707-source and 751-package manifests; archive CRC/hash |
| G1 Claims | `PASS` | exact split scope, sharp quadratic role, necessary linear term and open chordal scope aligned |
| G2 Mathematics | `PASS` | fresh bounded suites plus the E2 universal ledger and 315,183 exact residual checks |
| G3 Formal conformance | `PASS` | final/API root closure and all canonical/load-bearing axiom surfaces recorded |
| G4 Recorded build | `PASS_RECORDED_BUILD` | clean-origin resumed evidence verified; limitation disclosed; no rebuild performed internally |
| G5 Bilingual | `PASS` | 51/51 consistency checks; 144 headings each; 205 display-math blocks; no duplicated long text |
| G6 TeX/PDF | `PASS` | EN 46 / ES 47 pages; final logs clean; fonts embedded; all 93 pages inspected |
| G7 Prior art | `PASS_INTERNAL_EXTERNAL_GATE_OPEN` | bounded internal claim and preserved E6 addendum; fresh independent confirmation required |
| G8 Package | `PASS` | v1.4 target unambiguous; no duplicated v1.3 artifacts, Lean objects, TeX residue or stray directories |

The executable suite reports **144/144 checks passed**. During test-harness calibration,
six false failures were identified: three literal phrase probes, a query/distinct-surface
count distinction, and two probes that read preliminary instead of final TeX logs. The
controls were corrected without changing any manuscript, TeX, PDF or Lean source, and the
entire suite was rerun.

## External-audit regression closure

Version 1.4 corrects the public-root imports, stale root description, Spanish Proposition
7.4, formal metadata and reproduction sequence. The recorded build verifies the corrected
root and all directed axiom surfaces. It began from a source-only clean project but resumed
after an application restart; therefore uninterrupted clean-room reproduction remains the
principal external formal gate.

The E2 and E6 material is ready as an explicit auditor hint. For E2, the external auditor
must independently rederive the analytic obligations using the ledger as a map and confirm
the hypergraph/graph and quantitative bridges. For E6, the auditor must confirm the prior
search addendum and the precise novelty scope: the split coefficient improves from `3/16`
to the sharp `1/6`, while the general chordal problem remains open.

## Verdict and boundary

`PASS`. No internal blocker, major or minor finding remains. This does not constitute
external reproduction, peer review, public-release approval or an independent novelty
certificate. The package is ready for residual external adversarial audit.
