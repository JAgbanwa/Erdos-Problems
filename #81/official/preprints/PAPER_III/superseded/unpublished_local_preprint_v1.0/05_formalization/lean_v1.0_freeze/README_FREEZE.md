# Paper III Lean v1.0 freeze

Frozen Lean package equivalent to the latest Paper III working version available at `C:\lean\paper3`.

## Source

- Source copied from: `C:\lean\paper3`
- Destination: `C:\ERDOS\erdos81\github-sync\#81\official\preprints\PAPER_III\05_formalization\lean_v1.0_freeze`
- Lean toolchain: `leanprover/lean4:v4.28.0`
- Mathlib revision: `v4.28.0` (`8f9d9cff6bd728b17a24e163c9402775d9e6a365`)
- Previous released Lean folder left untouched: `preprints\PAPER_III\05_formalization\lean`

## Verification

```text
lake build PaperIII
Build completed successfully (8060 jobs).
```

Log: `gate_logs/lake_build_full.log`

Warning count in full PaperIII build log: `64`
Error count in full PaperIII build log: `0`

The warnings are Lean linter warnings in internal `PaperIII.*` modules, mostly unused variables,
unused simp arguments, and one unused tactic. They do not affect elaboration success.

## Axiom Scope

The only project-level external axioms declared in `PaperIII/AX.lean` are:

```lean
axiom AX1 : ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ...
axiom AX2 : ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ...
```

These correspond to the recognized external results AX1 (Haxell-Rödl / Yuster) and AX2 (Dross +
Barber-Kühn-Lo-Osthus), as documented in `PaperIII/AX.lean`.

## Contents

- `PaperIII/`: paper formalization modules.
- `PaperIII/Contrib/`: Mathlib contribution candidates copied with the freeze.
- `gate_logs/`: build/cache logs for this frozen copy.
- `FREEZE_MANIFEST_SHA256.txt`: SHA256 manifest of source and metadata files.

## Scope

This freeze is a new incremental snapshot. It does not modify the previous released Lean package under
`05_formalization/lean`.
