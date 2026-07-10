# Release notes -- Paper II, preprint v1.0

**Date:** 2026-07-10

## Summary
First official preprint release of Paper II: the exact finite extremum of the
fractional triangle-cover functional over chordal graphs,
`max = floor((2n+1)^2/24)`, attained by a complete-split graph.

## Highlights
- Self-contained analytic proof (calculation ledger v1.1).
- **Formally verified in Lean 4 / Mathlib v4.28.0** (`PaperII.theorem_1_2`,
  commit `5f2d448`): `sorry`-free, unconditional on the standard `IsChordal`
  definition, axiom report `[propext, Classical.choice, Quot.sound]`.
- Bilingual manuscript (English + Spanish), identical mathematics.
- Per-section internal computational audits (A-F).

## Boundary
Not externally peer-reviewed; novelty/priority review incomplete; independent
third-party reproduction of the Lean build recommended and pending; external
adversarial audit of Paper II pending. Does not settle 