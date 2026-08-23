/-
# Nibble — M8 with the sharp COUNT coefficient

Standalone, Mathlib-only. Re-instantiates the residual-degree McDiarmid concentration with the sharp
per-edge COUNT coefficient `neighborCoef H v e` (the number of `v`-edges meeting the toggled edge's
neighbourhood, `≤ deg(v)`) in place of the loose sum-of-degrees coefficient. The denominator becomes
`∑_{e∈H} neighborCoef(v,e)²`, which the sum-estimate chain
(`sumSq_neighborCoef_le` + `neighborCoef_le_sum_codegree` + `sum_neighborCoef_le_degree_mul`) bounds by
`M·S ≲ deg(v)·poly(r,Δ)` — the tail total that makes the nibble window `c ≈ √(d log n) ≪ d` feasible.

Off-`H` toggles are inert (`residualDegConfig_eq_of_notMem`), so the coefficient `if e∈H then
neighborCoef else 0` collapses the coordinate sum to `H`.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.McDiarmidFull
import Nibble.ResidualBoundedDiffSharp
import Nibble.McDiarmidResidualSharp
import Nibble.SumEstimate
import Nibble.Prelude

open MeasureTheory ProbabilityTheory Finset Hypergraph

namespace Nibble

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **M8 (count) — residual-degree concentration with the sharp count coefficient.** The residual
degree at `v` deviates from its mean by `≥ ε` with probability
`≤ 2·exp(−ε²/(2 ∑_{e∈H} neighborCoef(v,e)²))`. The count coefficient (`≤ deg(v)`) replaces the loose
sum-of-degrees, so the denominator is bounded by the sum-estimate chain — the exponential tail that
makes the nibble parameter window feasible. -/
theorem residualDeg_config_concentration_count (H : Finset (Finset V)) (v : V)
    (ν : Measure Bool) [IsProbabilityMeasure ν] {ε : ℝ} (hε : 0 ≤ ε) :
    (Measure.pi (fun _ : Finset V => ν)).real
        {ω | ε ≤ |(degree (residual H (H.filter (fun g => ω g = true))) v : ℝ)
              - ∫ x, (degree (residual H (H.filter (fun g => x g = true))) v : ℝ)
                  ∂(Measure.pi (fun _ : Finset V => ν))|}
      ≤ 2 * Real.exp (-ε ^ 2 / (2 * ∑ e ∈ H, (neighborCoef H v e : ℝ) ^ 2)) := by
  classical
  set c : Finset V → ℝ := fun e => if e ∈ H then (neighborCoef H v e : ℝ) else 0 with hc
  have hfmeas : Measurable
      (fun ω : Finset V → Bool => (degree (residual H (H.filter (fun g => ω g = true))) v : ℝ)) :=
    measurable_of_finite _
  have hbd : ∀ (j : Finset V) (ω ω' : Finset V → Bool), (∀ i, i ≠ j → ω i = ω' i) →
      |(degree (residual H (H.filter (fun g => ω g = true))) v : ℝ)
        - (degree (residual H (H.filter (fun g => ω' g = true))) v : ℝ)| ≤ c j := by
    intro j ω ω' h
    by_cases hjH : j ∈ H
    · rw [hc]; simp only [if_pos hjH]
      exact residualDegConfig_boundedDiff_neighborCoef H v j ω ω' (fun g hg => h g hg)
    · rw [hc]; simp only [if_neg hjH]
      rw [residualDegConfig_eq_of_notMem H v j ω ω' hjH (fun g hg => h g hg)]
      simp
  have hkey := mcdiarmid_two_sided_const ν
    (fun ω => (degree (residual H (H.filter (fun g => ω g = true))) v : ℝ))
    hfmeas.stronglyMeasurable Integrable.of_finite hbd hε
  have hsum : (∑ j : Finset V, (c j) ^ 2) = ∑ e ∈ H, (neighborCoef H v e : ℝ) ^ 2 := by
    have : ∀ j : Finset V, (c j) ^ 2 = if j ∈ H then (neighborCoef H v j : ℝ) ^ 2 else 0 := by
      intro j; rw [hc]; by_cases hjH : j ∈ H <;> simp [hjH]
    simp_rw [this]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  rw [hsum] at hkey
  exact hkey

end Nibble
