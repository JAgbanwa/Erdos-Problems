# Formalization -- Lean 4

`lean/` is the exact source of repository commit `5f2d448` (verified per file by
SHA-256).

- Main theorem: `PaperII.theorem_1_2` in `lean/PaperII/Unconditional.lean`
  (= Theorem 1.1 of the manuscript): both the upper bound over all chordal graphs
  of order `n` and attainment by a complete-split graph.
- Chordality hypothesis: the standard `IsChordal` predicate
  (`lean/PaperII/Chordal.lean`) -- every cycle of length >= 4 has a chord. The
  structural chordal facts (induced-subgraph heredity, clique-neighborhood
  extension, simplicial-vertex existence via Dirac's minimal-separator theorem)
  are **derived** from `IsChordal`; no clique-tree/running-intersection axiom is
  used (the terminal characterization is proved clique-tree-free).
- Certificate: `sorry`-free; `#print axioms PaperII.theorem_1_2` =
  `[propext, Classical.choice, Quot.sound]`.

See `../03_reproducibility/BUILD_VERIFICATION.md` and `l