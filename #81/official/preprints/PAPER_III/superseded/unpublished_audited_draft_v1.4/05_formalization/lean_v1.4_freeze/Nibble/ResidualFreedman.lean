/-
# Freedman concentration wiring for residual degree

This file connects the one-bit Bernoulli variance calculation to the Doob
martingale on the concrete Bernoulli configuration space.  The first theorem is
the reusable per-coordinate conditional-variance estimate; its specialization
to the residual-degree observable uses the sharp count bounded difference.
-/
import Nibble.ResidualBernstein
import Nibble.ResidualBoundedDiffSharp
import Nibble.McDiarmidMarginal
import Nibble.BernoulliConfig
import Nibble.VarianceEstimate
import Nibble.Prelude

open MeasureTheory ProbabilityTheory Finset Hypergraph
open scoped NNReal ENNReal

namespace Nibble

/-- Integration against the concrete Bernoulli configuration measure is the
usual weighted two-point average. -/
theorem integral_bernoulliConfigMeasure (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (g : Bool → ℝ) :
    ∫ b, g b ∂bernoulliConfigMeasure p hp0 hp1 =
      p * g true + (1 - p) * g false := by
  unfold bernoulliConfigMeasure
  rw [PMF.integral_eq_sum, Fintype.sum_bool]
  change (⟨p, hp0⟩ : NNReal) • g true + (1 - ⟨p, hp0⟩ : NNReal) • g false = _
  simp only [NNReal.smul_def, smul_eq_mul]
  rw [NNReal.coe_sub (show (⟨p, hp0⟩ : NNReal) ≤ 1 by exact_mod_cast hp1)]
  norm_num

/-- The second moment of a centered Bernoulli two-point variable is bounded by
`p C²` when its two possible uncentered values have gap at most `C`. -/
theorem bernoulli_centered_two_point_secondMoment_le
    {p a b C : ℝ} (hp0 : 0 ≤ p) (hgap : |a - b| ≤ C) :
    p * (a - (p * a + (1 - p) * b)) ^ 2 +
        (1 - p) * (b - (p * a + (1 - p) * b)) ^ 2 ≤ p * C ^ 2 := by
  rw [bernoulli_two_point_variance_identity]
  exact bernoulli_two_point_variance_le hp0 hgap

/-- Residual degree, with the finite edge-configuration index reindexed by
`Fin (Fintype.card (Finset V))` so that it is directly compatible with the
exposure filtration. -/
def residualDegReindexed {V : Type*} [Fintype V] [DecidableEq V]
    (H : Finset (Finset V)) (v : V)
    (e : Fin (Fintype.card (Finset V)) ≃ Finset V)
    (ω : Fin (Fintype.card (Finset V)) → Bool) : ℝ :=
  degree (residual H (H.filter (fun g => ω (e.symm g) = true))) v

/-- The reindexed residual-degree observable has the sharp coordinate
oscillation `neighborCoef H v (e j)`. -/
theorem residualDegReindexed_boundedDiff
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : Finset (Finset V)) (v : V)
    (e : Fin (Fintype.card (Finset V)) ≃ Finset V)
    (j : Fin (Fintype.card (Finset V)))
    (ω ω' : Fin (Fintype.card (Finset V)) → Bool)
    (hagree : ∀ i, i ≠ j → ω i = ω' i) :
    |residualDegReindexed H v e ω - residualDegReindexed H v e ω'| ≤
      (neighborCoef H v (e j) : ℝ) := by
  apply residualDegConfig_boundedDiff_sharp H v (e j)
  intro g hg
  exact hagree (e.symm g) (fun h => hg (by simpa using congrArg e h))


end Nibble
