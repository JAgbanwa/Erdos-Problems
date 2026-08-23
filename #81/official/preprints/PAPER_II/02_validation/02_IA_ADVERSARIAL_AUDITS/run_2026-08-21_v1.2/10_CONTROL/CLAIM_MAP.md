# Claim map - PAPER_II, preprint_draft_v1.2

**Protocol:** `EXTERNAL_AI_ADVERSARIAL_AUDIT_INSTRUCTIONS_v1.1`

Built independently from the manuscript before consulting any author-side record.

## `P2-MAIN-V1_2` - the exact chordal maximum

- **Manuscript:** abstract and Theorem 1.1. For every integer `n >= 1`,
  `max { Phi_tau(G) : G chordal, |V(G)| = n } = floor((2n+1)^2/24)`, with
  `Phi_tau(G) = |E(G)| - 2 tau_3^*(G)`, together with attainment by a complete-split graph.
- **Hypotheses:** `G` chordal, `|V(G)| = n`, `n >= 1`. The left endpoint `n = 1` is included
  and was tested.
- **Formal:** `PaperII.theorem_1_2`.
- **Role:** final theorem.
- **Falsification strategy:** exhaustive enumeration of all chordal graphs on up to 6
  vertices with `nu_3^*` and `tau_3^*` each computed by exact rational simplex; two failure
  routes sought - a graph exceeding the formula, and the formula being unattainable.
- **Outcome:** **survived.** 19,048 chordal graphs, exact at every `n`, always attained by a
  complete-split graph.

## `P2-EXTREMIZER` - maximizers, level sets, copy defects

- **Manuscript:** the copy inequality, its clone-class lift, the terminal characterization.
- **Formal:** `Fsat_argmax_unique`, `Fsat_argmax_tie`, `level_set_iff`,
  `copyDefect_nonneg`, `copyGamma_ge_half_copyDefect`.
- **Role:** structural bridges.
- **Falsification strategy:** the single-step copy inequality tested exhaustively over all
  labeled graphs on 2..6 vertices and all nonadjacent pairs.
- **Outcome:** **survived.** 251,085 instances, zero violations, minimum defect 0.
  Ties observed exactly where the manuscript's scoping predicts them.
- **Not verified:** termination of the repeated-copy process, and the discrete-convexity
  lift to clone classes.

## `P2-ASYM-COR` - asymptotic, modular and Paper I comparison corollaries

- **Formal:** `phiTau_max_sandwich`, `odd_sq_emod_24`, `phiTau_max_closed`,
  `phiTau_max_le_paperI_bound`.
- **Role:** byproducts of the closed value.
- **Outcome:** **survived.** All four confirmed in exact arithmetic over `n` in
  `[-20000, 20000]`, including the negative range the sandwich is stated for. The `n >= 1`
  hypothesis on the Paper I comparison was shown to be **necessary**: the inequality fails
  for `n <= 0`.
- **Cross-paper:** the comparison uses Paper I's corrected `+n/2` surface, as protocol
  Section 10 requires.

## `P2-FORMAL-CONFORMANCE` - the v1.2 surface and reusable components

- **Formal:** `PaperII`, `Contrib.Submission.Chordal`,
  `Contrib.Submission.GeodesicChordless`.
- **Role:** byproduct / reusable lane.
- **Outcome:** built as explicit targets; footprints as expected. Two declarations carry a
  strictly smaller footprint (`[propext, Quot.sound]`), and the manuscript's Table 5 records
  that reduced footprint accurately.

## The identity `nu_3^* = tau_3^*`

Asserted in the abstract. **Not assumed by this audit.** Both optima were computed by
separate linear programs on every graph tested - 270,133 in total across Gates C and G -
with **zero** mismatches.

## Protocol Section 5.2 distinctions, recorded separately

| Distinction | Status |
|---|---|
| source present | yes, 42 project `.lean` files |
| target compiled | yes, the seven protocol targets, explicitly enumerated |
| aggregate root imports target | **not relied upon.** `Extremizer` and `CopyDefect` are explicit build targets and are imported directly by the frozen axiom file |
| public API re-exports declaration | not applicable |
| headline theorem has the claimed axiom footprint | **yes**, `PaperII.theorem_1_2` reports the expected triple |
