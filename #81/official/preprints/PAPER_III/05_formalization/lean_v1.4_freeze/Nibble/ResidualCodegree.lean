/-
# Nibble — codegree is monotone under taking residuals

Standalone, Mathlib-only. A small structural fact for the step-2 invariant: since the residual
hypergraph is a subfamily of `H`, every pair's codegree can only drop. This is the codegree side of
the round invariant (the degree side is `RoundInvariant`): the residual keeps `codegree ≤ μd`
because it started `≤ μd` and only shrinks.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.Basic
import Nibble.Round
import Mathlib.Tactic.Monotonicity

open Finset

namespace Hypergraph

variable {V : Type*} [DecidableEq V]

/-- **Codegree monotonicity under residuals.** `codegree (residual H R) x y ≤ codegree H x y`. -/
theorem codegree_residual_le (H R : Finset (Finset V)) (x y : V) :
    codegree (residual H R) x y ≤ codegree H x y :=
  Finset.card_le_card (Finset.filter_subset_filter _ (residual_subset H R))

end Hypergraph
