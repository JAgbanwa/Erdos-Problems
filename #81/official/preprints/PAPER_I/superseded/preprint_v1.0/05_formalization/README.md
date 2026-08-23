# Formalization

This directory contains the Lean 4 formalization accompanying the preprint
*Affine Profile Reduction for Fractional Triangle Packings in Split Graphs.*

Theorem 1.1 is fully machine-checked in Lean 4 (Mathlib v4.28.0): the proof is
sorry-free, and the recorded axiom report for both `paperI_main` (Theorem 1.1)
and `residual_duality` (Proposition B.1) reduces to Lean's three standard
foundational axioms (`propext`, `Classical.choice`, `Quot.sound`), with no
project-specific axiom. Those three axioms are the ordinary logical foundation
used throughout Mathlib, not additional assumptions of this work.

## Contents

The formalization lives in the `lean/` subdirectory:

- `lean/PaperI/PaperI_Statement.lean` — full split-graph model, the main theorem
  `paperI_main` (Theorem 1.1), and `residual_duality` (Proposition B.1).
- `lean/PaperI/PaperI_Arith.lean` — arithmetic backbone (`Rq`, final bound).
- `lean/FiniteLPDuality.lean` — finite LP strong duality
  (`covering_packing_duality`), proved from a finite Farkas lemma and the
  closedness of a finitely generated convex cone plus hyperplane separation for
  closed convex cones.
- `lean/lean-toolchain`, `lean/lakefile.toml`, `lean/lake-manifest.json` — build
  configuration (Lean and Mathlib pinned to v4.28.0).
- `lean/gate_logs/` — recorded build log (`lake_build_PaperI_full.log`) and axiom
  report (`print_axioms_residual_and_main.log`).
- `lean/README.md`, `lean/README_EVIDENCE.md` — build instructions and the
  statement-to-preprint map.

The verified core is `PaperI_Statement.lean` and `FiniteLPDuality.lean`. The files
`DeltaNu.lean` and `WCDH_check.lean` are auxiliary results and are not part of the
Theorem 1.1 verification.

## Build and verify

See `lean/README.md`. In brief:

```bash
cd lean
lake exe cache get   # fetch the prebuilt Mathlib cache
lake build           # a successful (exit 0) build type-checks every theorem with no sorry
```

To reproduce the axiom certification:

```
#print axioms PaperI.paperI_main
-- 'PaperI.paperI_main' depends on axioms: [propext, Classical.choice, Quot.sound]
```
