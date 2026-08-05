# Validation status -- Paper II, preprint v1.0

**Result.** For chordal `G` on `n` vertices,
`max(|E(G)| - 2*tau3*(G)) = floor((2n+1)^2/24)` (upper bound and attainment).

## What has been done

- **Analytic proof.** Complete and self-contained (calculation ledger v1.1).
- **Formal verification (Lean 4 / Mathlib v4.28.0).** `PaperII.theorem_1_2`
  (commit `5f2d448`): `sorry`-free; unconditional on the standard `IsChordal`
  predicate; `#print axioms` = `[propext, Classical.choice, Quot.sound]`
  (no `sorryAx`, no project-specific axiom). See `../05_formalization/`.
- **Internal AI adversarial audits (A-F).** Each manuscript section re-verified by
  an independent, self-contained program (`PAPER_II_AUDIT/`): the vertex-copy
  inequality, clone-class convexity, terminal characterization, complete-split
  cover program, integer maximization, and the global theorem. All passed with no
  violation in the tested ranges.
- **Editor and researcher approval** for preprint release.

## What has NOT been done (honest boundary)

- **No external peer review / journal refereeing.**
- **No specialist novelty/priority review** of the functional.
- **No independent third-party reproduction** of the Lean build yet: the
  `lake build` + `#print axioms` certificate has been produced in the development
  environment; reproduction in a clean, independent environment is recommended
  (see `../03_reproducibility/`).
- **Independent AI adversarial audit** (tier `02_IA_ADVERSARIAL_AUDITS/`, mirroring
  Paper I): **PASS** (`PAPER-II-EXT-AUDIT-001`, 2026-07-10); report deposited under
  `02_IA_ADVERSARIAL_AUDITS/20_EVIDENCE/ERDOZ81-P2-FRAC-THM-01/`. This is an
  intermediate level (independent AI reviewer), **not** human peer review.
  (The unrelated `EXT-AUDIT-001` concerns the *separate* asymptotic clique-partition
  route, not this theorem.)

## Scope

Paper II is the exact fractional-cover theorem only. It does not prove a
clique-partition bound and