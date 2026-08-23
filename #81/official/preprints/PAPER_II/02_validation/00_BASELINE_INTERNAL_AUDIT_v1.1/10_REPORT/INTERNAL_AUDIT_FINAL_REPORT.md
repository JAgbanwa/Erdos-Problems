# Paper II v1.1 internal audit final report

> **Overall verdict:** `PASS`  
> **Audit class:** internal / not external  
> **Protocol:** `INTERNAL_AUDIT_STANDARD_v1.2`  
> **Date:** 2026-08-21

The audit covered claims, exact and bounded mathematical checks, static
manuscript-to-Lean correspondence, recorded build evidence, bilingual and
publication artifacts, prior art and package integrity. Lean was not rerun.

| Gate | Verdict | Evidence |
|---|---|---|
| G0 Target | `PASS` | 6 artifact, 45 source and 62 package hashes; archive sidecar |
| G1 Claims | `PASS` | Exact theorem, branches, degeneracies, scope and quantifiers |
| G2 Mathematics | `PASS_AFTER_HARNESS_CORRECTION` | 195 cover LPs; n=1..5000; 139 chordal graphs; 931 copy pairs |
| G3 Formal conformance | `PASS` | Unconditional `PaperII.theorem_1_2`; auxiliary surfaces matched |
| G4 Recorded build | `PASS` | 8,061 main + 8,032 supplement; 16 axiom outputs; no Lean rerun |
| G5 Bilingual | `PASS` | Headings, formulas, 3 figures, tables and 23 identifiers aligned |
| G6 TeX/PDF | `PASS` | 24/24 pages, embedded fonts, all pages visually inspected |
| G7 Prior art | `PASS_INTERNAL` | No earlier same exact finite functional/extremizer result identified |
| G8 Package | `PASS` | Active/superseded and evidence structure consistent |

The first G2 attempt over-scoped a saturated-branch argmax statement to include
the degenerate tie at `n=2`. The harness domain was corrected and the failed
attempt retained. This was a test-specification correction, not a manuscript
or mathematical correction. No manuscript artifact required modification.

The English target SHA-256 is
`361802b5398eb9e3cc03b4ca5e591ce71987979b02142826054eb5f6a315ded6`;
the Spanish target SHA-256 is
`26ddd0d08b08e54bfe57e43a9733f456f94f617e8cfc98e3604b34a3dc10273e`.
The freeze records Lean 4.28.0, Mathlib
`8f9d9cff6bd728b17a24e163c9402775d9e6a365`, successful main and supplement
builds, and foundational-only axiom footprints.

The internal novelty assessment remains carefully scoped: no earlier exact
maximum of the fractional functional over chordal graphs was identified, while
the integral Erdős #81 problem remains open. Specialist prior-art review,
independent archive rebuild, external adversarial audit, peer review, tag and
release approval remain open external gates.

## Overall verdict

`PASS`. All nine blocking internal gates pass. There are zero unresolved
blocker or major findings.

