# Paper I — Lean 4 Proof Evidence

**Date:** 2026-07-07
**Repo of record:** `C:\Users\jtrav\aristotle_lean` (git, branch `main`)
**Toolchain:** Lean 4 `v4.28.0` + Mathlib `v4.28.0`

## Result

The main theorem of Paper I ("Affine Profile Reduction for Fractional Triangle
Packings in Split Graphs") is **fully formalized and machine-verified**:

```
paperI_main : Φ = |E| − 2·ν₃* ≤ n²/6 + n
```

**Status: sorry-free · axiom-clean · no external dependencies.**

## Axiom certification

Verified via `lake build PaperI.PaperI_Statement` (8027 jobs, exit 0) and
`#print axioms`. Both critical declarations depend **only** on the three standard
Lean/Mathlib axioms — no `sorryAx`, no `native_decide`, no `admit`, no added `axiom`:

```
PaperI.Split.residual_duality → [propext, Classical.choice, Quot.sound]
PaperI.paperI_main            → [propext, Classical.choice, Quot.sound]
```

(`propext`, `Classical.choice`, `Quot.sound` are the foundational axioms every
ordinary Mathlib theorem uses; their presence is the expected clean baseline.)

## The strong-duality wall — proved the hard, self-contained way

The last obligation, `residual_duality` (finite LP **strong** duality, which
Mathlib does not provide packaged), was proved **from scratch, with no external
citation**, in `FiniteLPDuality.lean` (314 lines, 0 sorries):

    conic_caratheodory        (conic Carathéodory)
      → fg_cone_isClosed      (finitely generated cone is closed)
        → farkas_ge           (finite Farkas, via Mathlib ProperCone hyperplane separation)
          → covering_packing_duality   (finite LP strong duality, attained)
            → residual_duality (specialized to the clique-edge / clique-triangle system)

`FiniteLP.covering_packing_duality` is reusable — it is the same duality wall as
M2-DUAL of Erdős #81.

## File inventory

### Lean source files (in this directory)
| File | Role |
|---|---|
| `PaperI_Statement.lean` | The full Paper I model + `paperI_main` (proven). |
| `PaperI_Arith.lean` | A-ARITH arithmetic backbone (`Rq`, final bound). |
| `FiniteLPDuality.lean` | Finite LP strong duality from scratch (closes `residual_duality`). |
| `DeltaNu.lean` | Bipartite bound `|E| − ν ≤ |P_A| + |P_B|` (proven, axiom-clean). |
| `WCDH_check.lean` | Paper 1 conditional bound via PEO (verified, conditional on wCDH). |
| `lakefile.toml`, `lean-toolchain` | Build configuration. |

### `gate_logs/`
| File | Content |
|---|---|
| `lake_build_PaperI_full.log` | `lake build` output: 8027 jobs, exit 0, per-declaration axioms. |
| `print_axioms_residual_and_main.log` | Literal `#print axioms` for `residual_duality` and `paperI_main`. |
| `FiniteLPDuality_compile.log` | Compilation of the strong-duality file (exit 0). |

## Reproduce

From a checkout of `aristotle_lean` (with the pinned toolchain and Mathlib cache):

```
lake build PaperI.PaperI_Statement
```

Expect exit 0. To re-print the axiom certification, the file ends with:

```
#print axioms PaperI.Split.residual_duality
#print axioms PaperI.paperI_main
```
