# `Contrib/Submission/` — Mathlib contribution candidates (PR-track)

This folder holds the **submission (PR-ready) versions** of the Lean results extracted from
the Erdős-#81 Paper I formalization that appear to fill genuine gaps in Mathlib. They are
kept **separate from the working versions** (in `Contrib/`) so the polished, send-quality
code is not mixed with exploratory work. Nothing here is imported by the Paper I
formalization (`PaperI/`), so it cannot affect that proof.

All results below compile `sorry`-free and are **axiom-clean**
(`[propext, Classical.choice, Quot.sound]` only — no `sorryAx`, no project axioms), with
**no `grind`, no `simp +decide`, and at the default heartbeat budget** unless noted.

## Files

| File | Contents |
|---|---|
| `FgConeClosed.lean` | Closedness of a finitely generated cone (Weyl) + conic Carathéodory + the `PointedCone` API theorems. |
| `FarkasLP.lean` | Finite Farkas lemma (algebraic inequality form) + finite LP strong duality (covering/packing). |
| `INTEGRATION_PLAN.md` | The plan/status for turning these into Mathlib PR(s): what Mathlib already has, the reduction to the engine, remaining items. |
| `ZULIP_TOPIC_DRAFT.md` | Draft message for the Mathlib Zulip (`#mathlib4`) to coordinate naming/placement before opening PR(s). |
| `README.md` | This file. |

## Results

### `FgConeClosed.lean` (over an arbitrary real normed space `E`)
- `simplicial_cone_isClosed` — a cone spanned by a linearly independent finite family is
  closed (image of the closed nonnegative orthant under an injective linear map).
- `conic_caratheodory` — conic Carathéodory: every nonnegative combination equals a
  nonnegative combination over a linearly independent subfamily. *(fully idiomatic; default
  heartbeats)*
- `fg_cone_isClosed` — **a finitely generated cone is closed** (Weyl); the headline result.
- `span_isClosed_of_finite` — Mathlib-API form: `IsClosed (PointedCone.span ℝ s)` for finite `s`.
- `isSimplicial_isClosed` — Mathlib-API form: a `PointedCone.IsSimplicial` cone is closed.

### `FarkasLP.lean` (over `EuclideanSpace ℝ ι`)
- `farkas_ge` — finite Farkas lemma (inequality form): if `x ≥ 0, N x ≥ c` is infeasible,
  there is a certificate `y ≥ 0` with `Nᵀ y ≤ 0` and `⟨c,y⟩ > 0`.
- `covering_packing_duality` — finite LP strong duality: the maximum packing value equals
  the covering optimum and is attained. (Built on `fg_cone_isClosed`.)
- Helpers: `toE`, `toE_apply`, `inner_toE`.

## Status vs. Mathlib

Mathlib (v4.28.0) has `ProperCone`, `ProperCone.hyperplane_separation` (geometric Farkas),
and `PointedCone.IsSimplicial`/`span`, but **not** the closedness of a finitely generated /
simplicial cone, nor an algebraic Farkas lemma or finite LP strong duality. These files
supply those. See `INTEGRATION_PLAN.md`.

**Remaining before an actual PR** (deliberately not done here): Mathlib Zulip coordination
on naming/placement; optionally generalizing the scalar field beyond `ℝ`. The code itself
is compile-clean and idiomatic.

## Build / verify

From the repo root (`aristotle_lean/`):

```bash
lake build Contrib.Submission.FgConeClosed
lake build Contrib.Submission.FarkasLP
```

To re-check axioms, append `#print axioms <name>` to a scratch file importing the module and
run `lake env lean` on it (expect `[propext, Classical.choice, Quot.sound]`).

## Provenance

The proofs were developed with AI-assisted tooling (an automated prover) as part of the
Paper I formalization, then extracted, generalized to Mathlib's natural generality, and
cleaned to idiomatic style (removing `grind`/`simp +decide`/`simp_all` and raised heartbeat
budgets). They are the author's contribution; no AI system is an author.

---
*Maintenance note: keep this README in sync when files/results in this folder change.*
