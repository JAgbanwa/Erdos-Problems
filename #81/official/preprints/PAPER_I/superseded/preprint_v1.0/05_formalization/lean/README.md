# Paper I — Machine-Verified Lean 4 Proof

A self-contained Lean 4 / Mathlib formalization of the main theorem of **Paper I**,
*"Affine Profile Reduction for Fractional Triangle Packings in Split Graphs."*

```
paperI_main : Φ = |E| − 2·ν₃* ≤ n²/6 + n
```

**Verified: sorry-free, axiom-clean, no external dependencies.**

## Axiom certification

Both critical declarations depend **only** on the three standard Lean/Mathlib
foundational axioms — no `sorryAx`, no `native_decide`, no `admit`, no added `axiom`:

```
PaperI.Split.residual_duality → [propext, Classical.choice, Quot.sound]
PaperI.paperI_main            → [propext, Classical.choice, Quot.sound]
```

## Requirements

- [`elan`](https://github.com/leanprover/elan) (the Lean toolchain manager).
  The pinned toolchain (`lean-toolchain`) is Lean **v4.28.0**; elan installs it
  automatically on first build.
- Mathlib is pinned in `lake-manifest.json` to the `v4.28.0` release.

## Build & verify

```bash
# 1. fetch the prebuilt Mathlib cache (avoids recompiling Mathlib)
lake exe cache get

# 2. build everything (Paper I + the finite-LP-duality backbone + auxiliary results)
lake build
```

A successful `lake build` (exit 0) is itself the proof that every theorem type-checks
with no `sorry`. To re-print the axiom certification explicitly, the end of
`PaperI/PaperI_Statement.lean` contains:

```lean
#print axioms PaperI.Split.residual_duality
#print axioms PaperI.paperI_main
```

These lines are emitted during `lake build PaperI.PaperI_Statement`; the expected
output is shown above and recorded in `gate_logs/`.

## Contents

| Path | Role |
|---|---|
| `PaperI/PaperI_Statement.lean` | Full split-graph model, `ν₃*`, `Φ`, and the proven `paperI_main`. |
| `PaperI/PaperI_Arith.lean` | Arithmetic backbone (`Rq`, the final numeric bound). |
| `FiniteLPDuality.lean` | **Finite LP strong duality, proved from scratch** — closes the last obligation `residual_duality`. |
| `DeltaNu.lean` | Bipartite bound `\|E\| − ν ≤ \|P_A\| + \|P_B\|` (independent, axiom-clean). |
| `WCDH_check.lean` | Paper 1 conditional bound via a perfect elimination ordering (verified, conditional on the wCDH hypothesis). |
| `gate_logs/` | Recorded build + `#print axioms` outputs. |
| `README_EVIDENCE.md` | Detailed evidence notes and the strong-duality proof tree. |

## How the strong-duality wall was closed (no external citation)

Mathlib does not provide finite LP strong duality packaged. It is developed here from
scratch in `FiniteLPDuality.lean`, built on Mathlib's proper-cone hyperplane separation:

```
conic_caratheodory → fg_cone_isClosed → farkas_ge → covering_packing_duality → residual_duality
```

`FiniteLP.covering_packing_duality` is a reusable finite LP strong-duality theorem.
