import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Data.Rat.Star
import Mathlib.Tactic.Positivity

/-!
# Arithmetic assembly of the far and near regimes

The graph-theoretic mechanisms are intentionally left as separate witnesses.
This module verifies the common numerical interface: the far rounding loss is
absorbed by half of the quadratic slack, while the near terminal supplies a
direct target bound in the original graph.
-/

namespace PaperIV.TwoRegimeAssembly

/-- A far-regime certificate: `F` is below the target by quadratic slack and
the physical construction loses at most half that slack. -/
structure FarCertificate (Q F C η n : ℚ) : Prop where
  nonneg_slack : 0 ≤ η * n ^ 2
  far : F < Q - η * n ^ 2
  rounding : C ≤ F + η * n ^ 2 / 2

theorem FarCertificate.closes {Q F C η n : ℚ}
    (h : FarCertificate Q F C η n) : C < Q := by
  rcases h with ⟨hslack, hfar, hround⟩
  nlinarith

/-- A near-regime certificate has a direct physical partition in the original
graph.  It is deliberately not transported backwards along a copy path. -/
structure NearCertificate (Q C : ℚ) : Prop where
  direct_bound : C ≤ Q

theorem NearCertificate.closes {Q C : ℚ}
    (h : NearCertificate Q C) : C ≤ Q := h.direct_bound

/-- The only top-level case split used by the two-regime architecture. -/
theorem closes_of_far_or_near {Q F C η n : ℚ}
    (h : FarCertificate Q F C η n ∨ NearCertificate Q C) : C ≤ Q := by
  rcases h with hfar | hnear
  · exact hfar.closes.le
  · exact hnear.closes

end PaperIV.TwoRegimeAssembly
