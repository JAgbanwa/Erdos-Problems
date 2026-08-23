/-
# Nibble — sub-gamma MGF and the Bernstein tail (variance-based concentration)

Standalone, Mathlib-only. The McDiarmid (bounded-difference) tail is too weak for the nibble: the
coordinate sum `∑ c_e²` is `≈ d²`, giving deviation `d√(log n) ≫ d`. The correct concentration is
VARIANCE-based (Bernstein/Freedman): with conditional variance `V ≈ d ≪ d²`, the tail
`exp(−c²/(2V))` gives deviation `√(d log n) ≪ d`, which the near-regularity window requires. Mathlib has
only the sub-Gaussian MGF (`HasSubgaussianMGF`), the base of Azuma — not the sub-gamma / Bernstein one.

This file introduces `HasSubgammaMGF X V c` (the sub-gamma MGF bound `mgf ≤ exp(V t²/(2(1−ct)))`) and
derives the Bernstein tail `P(X ≥ ε) ≤ exp(−ε²/(2(V+cε)))` from it, via Mathlib's Chernoff bound
(`measure_ge_le_exp_mul_mgf`) at the optimal `t* = ε/(V+cε)`. The HARD analytic core — that a bounded
mean-zero variable HAS a sub-gamma MGF (Bennett's inequality), and the martingale summation — is
dispatched separately.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.Prelude

open MeasureTheory ProbabilityTheory Real

namespace Nibble

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- **Sub-gamma MGF bound.** `X` has a sub-gamma MGF with variance factor `V` and scale `c` if
`mgf X μ t ≤ exp(V t²/(2(1−ct)))` for `0 ≤ t < 1/c`. This is the variance-based (Bernstein) analogue of
`HasSubgaussianMGF` (`c = 0`), and the martingale-summable object underlying Freedman's inequality. -/
def HasSubgammaMGF (X : Ω → ℝ) (V c : ℝ) (μ : Measure Ω) : Prop :=
  ∀ t : ℝ, 0 ≤ t → t < 1 / c → mgf X μ t ≤ Real.exp (V * t ^ 2 / (2 * (1 - c * t)))

/-- **Bernstein tail from the sub-gamma MGF.** If `X` has a sub-gamma MGF with `V > 0`, `c > 0`, then
`P(X ≥ ε) ≤ exp(−ε²/(2(V + cε)))`. The optimal Chernoff parameter is `t* = ε/(V+cε)`, at which the
exponent is exactly `−ε²/(2(V+cε))`. -/
theorem subgamma_tail [IsFiniteMeasure μ] {X : Ω → ℝ} {V c ε : ℝ}
    (h : HasSubgammaMGF X V c μ) (hV : 0 < V) (hc : 0 < c) (hε : 0 ≤ ε)
    (hint : Integrable (fun ω => Real.exp ((ε / (V + c * ε)) * X ω)) μ) :
    μ.real {ω | ε ≤ X ω} ≤ Real.exp (-ε ^ 2 / (2 * (V + c * ε))) := by
  have hVce : 0 < V + c * ε := by positivity
  set t : ℝ := ε / (V + c * ε) with ht
  have ht0 : 0 ≤ t := by rw [ht]; positivity
  have htc : t * c < 1 := by
    rw [ht, div_mul_eq_mul_div, div_lt_one hVce]
    linarith only [hV, mul_nonneg hc.le hε]
  have ht1 : t < 1 / c := by rw [lt_div_iff₀ hc]; exact htc
  -- 1 - c*t = V/(V+cε) > 0
  have hden : (1 : ℝ) - c * t = V / (V + c * ε) := by
    rw [ht]; field_simp [hVce.ne']; ring
  have hden_pos : 0 < 1 - c * t := by rw [hden]; positivity
  -- Chernoff + sub-gamma MGF
  have hcher := measure_ge_le_exp_mul_mgf (μ := μ) (X := X) (t := t) ε ht0 hint
  have hmgf := h t ht0 ht1
  have hstep : μ.real {ω | ε ≤ X ω}
      ≤ Real.exp (-t * ε) * Real.exp (V * t ^ 2 / (2 * (1 - c * t))) :=
    le_trans hcher (mul_le_mul_of_nonneg_left hmgf (Real.exp_nonneg _))
  rw [← Real.exp_add] at hstep
  refine le_trans hstep (le_of_eq ?_)
  congr 1
  -- exponent: -t*ε + V t²/(2(1-ct)) = -ε²/(2(V+cε))
  rw [ht, hden]
  field_simp
  ring
end Nibble
