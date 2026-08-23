/-
# Conditional Bennett bridge for residual-degree Freedman concentration

This file supplies the measure-theoretic bridge from fiberwise conditional centering,
boundedness, and conditional second-moment control to the conditional sub-gamma MGF
used by `Nibble.Freedman`.
-/
import Nibble.Freedman
import Nibble.Prelude

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

namespace Nibble

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
  {μ : Measure Ω} [IsFiniteMeasure μ] {X : Ω → ℝ}

/-- The exact variance identity for a two-point (Bernoulli) distribution.  This is
 the scalar Efron--Stein calculation underlying the one-coordinate conditional
 variance estimate. -/
theorem bernoulli_two_point_variance_identity (p a b : ℝ) :
    p * (a - (p * a + (1 - p) * b)) ^ 2
      + (1 - p) * (b - (p * a + (1 - p) * b)) ^ 2
      = p * (1 - p) * (a - b) ^ 2 := by
  ring

/-- **One-bit Efron--Stein bound.**  If changing a Bernoulli coordinate changes
 a quantity by at most `C`, then its two-point variance is at most `p C²`.
 The sharper intermediate value is `p(1-p)(a-b)²`. -/
theorem bernoulli_two_point_variance_le {p a b C : ℝ}
    (hp0 : 0 ≤ p) (hC : |a - b| ≤ C) :
    p * (1 - p) * (a - b) ^ 2 ≤ p * C ^ 2 := by
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) hC
  have hsquare : (a - b) ^ 2 ≤ C ^ 2 := by
    rw [← sq_abs]
    exact (sq_le_sq₀ (abs_nonneg _) hC0).2 hC
  calc
    p * (1 - p) * (a - b) ^ 2 ≤ p * 1 * (a - b) ^ 2 := by
      gcongr
      linarith only [hp0]
    _ ≤ p * 1 * C ^ 2 := by gcongr
    _ = p * C ^ 2 := by ring

/-- **Conditional Bennett bridge.**  If, on almost every conditional-expectation
fiber, `X` is centered, bounded above by `b`, and has second moment at most `V`,
then `X` has conditional sub-gamma parameters `(V,b/3)`.

The hypotheses are stated fiberwise because this is exactly the interface needed by
the conditional-expectation kernel.  In applications, the first and third hypotheses
are obtained from the martingale-difference identity and a conditional variance
estimate, respectively. -/
theorem hasCondSubgammaMGF_of_bounded_above
    (hm : m ≤ mΩ) {V b : ℝ} (hV : 0 ≤ V) (hbpos : 0 < b)
    (hcenter : ∀ᵐ ω ∂μ.trim hm, ∫ x, X x ∂condExpKernel μ m ω = 0)
    (hbound : ∀ᵐ ω ∂μ.trim hm, ∀ᵐ x ∂condExpKernel μ m ω, X x ≤ b)
    (hsecond : ∀ᵐ ω ∂μ.trim hm,
      ∫ x, (X x) ^ 2 ∂condExpKernel μ m ω ≤ V)
    (hXint : Integrable X μ)
    (hXsqint : Integrable (fun x => (X x) ^ 2) μ)
    (hexpint : ∀ t : ℝ, Integrable (fun x => Real.exp (t * X x)) μ) :
    HasCondSubgammaMGF m hm X ⟨V, hV⟩ ⟨b / 3, by positivity⟩ μ := by
  let κ := condExpKernel μ m
  have hcomp : κ ∘ₘ μ.trim hm = μ := condExpKernel_comp_trim hm
  have hXfiber : ∀ᵐ ω ∂μ.trim hm, Integrable X (κ ω) := by
    apply Measure.ae_integrable_of_integrable_comp
    simpa only [hcomp] using hXint
  have hXsqfiber : ∀ᵐ ω ∂μ.trim hm, Integrable (fun x => (X x) ^ 2) (κ ω) := by
    apply Measure.ae_integrable_of_integrable_comp
    simpa only [hcomp] using hXsqint
  have hexpfiber : ∀ t : ℝ, ∀ᵐ ω ∂μ.trim hm,
      Integrable (fun x => Real.exp (t * X x)) (κ ω) := by
    intro t
    apply Measure.ae_integrable_of_integrable_comp
    simpa only [hcomp] using hexpint t
  refine ⟨?_, ?_⟩
  · intro t
    rw [hcomp]
    exact hexpint t
  · have hexpall : ∀ᵐ ω ∂μ.trim hm, ∀ t : ℝ,
        Integrable (fun x => Real.exp (t * X x)) (κ ω) := by
      have h (q : ℚ) := hexpfiber q
      rw [← ae_all_iff] at h
      filter_upwards [h] with ω hω t
      exact integrable_exp_mul_of_le_of_le (hω ⌊t⌋) (hω ⌈t⌉)
        (Int.floor_le t) (Int.le_ceil t)
    filter_upwards [hcenter, hbound, hsecond, hXfiber, hXsqfiber, hexpall]
      with ω hcenterω hboundω hsecondω hXω hXsqω hexpω
    intro t ht htc
    exact hasSubgammaMGF_of_bounded_above hbpos hcenterω hboundω hsecondω
      hXω hXsqω (fun s _ _ => hexpω s) t ht htc

end Nibble

