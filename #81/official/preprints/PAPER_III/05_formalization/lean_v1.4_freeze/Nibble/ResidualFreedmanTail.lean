/-
# Bernoulli conditional second-moment core

This file packages the concrete two-point integral calculation in the exact form
needed after identifying an exposure-filtration conditional kernel with the next
Bernoulli coordinate.
-/
import Nibble.ResidualFreedman
import Nibble.McDiarmidStep
import Nibble.Prelude

open MeasureTheory ProbabilityTheory Finset Hypergraph
open scoped NNReal ENNReal

namespace Nibble

/-- Variance bound for an arbitrary real observable of the concrete Bool-valued
Bernoulli coordinate.  This is the terminal analytic step after conditional-kernel
identification: the conditional mean is the Bernoulli integral itself. -/
theorem integral_sq_sub_integral_bernoulliConfigMeasure_le
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (g : Bool → ℝ) {C : ℝ}
    (hgap : |g true - g false| ≤ C) :
    ∫ b, (g b - ∫ z, g z ∂bernoulliConfigMeasure p hp0 hp1) ^ 2
        ∂bernoulliConfigMeasure p hp0 hp1 ≤ p * C ^ 2 := by
  rw [integral_bernoulliConfigMeasure p hp0 hp1 g]
  rw [integral_bernoulliConfigMeasure p hp0 hp1]
  exact bernoulli_centered_two_point_secondMoment_le hp0 hgap

/-- Sub-gamma assembly for a Doob increment once its conditional second
moment has been identified.  Thus the residual-specific remaining obligation is
isolated entirely in `hsecond`. -/
theorem doob_increment_hasCondSubgammaMGF_of_secondMoment
    {n : ℕ} {α : Fin n → Type*} [∀ i, MeasurableSpace (α i)]
    [∀ i, StandardBorelSpace (α i)]
    (μ : Measure (∀ i, α i)) [IsProbabilityMeasure μ]
    (f : (∀ i, α i) → ℝ) {c V : ℝ}
    (hV : 0 ≤ V) (hc : 0 < c)
    (k : ℕ)
    (hbd : ∀ᵐ ω ∂μ,
      |doob μ f (k + 1) ω - doob μ f k ω| ≤ c)
    (hsecond : ∀ᵐ ω ∂μ.trim (exposureσ_le k),
      ∫ x, (doob μ f (k + 1) x - doob μ f k x) ^ 2
        ∂condExpKernel μ (exposureσ k) ω ≤ V) :
    HasCondSubgammaMGF (exposureσ k) (exposureσ_le k)
      (fun ω => doob μ f (k + 1) ω - doob μ f k ω)
      ⟨V, hV⟩ ⟨c / 3, by positivity⟩ μ := by
  let X := fun ω => doob μ f (k + 1) ω - doob μ f k ω
  have hmk : exposureσ (α := α) k ≤ MeasurableSpace.pi := exposureσ_le (α := α) k
  have hcomp : condExpKernel μ (exposureσ (α := α) k) ∘ₘ μ.trim hmk = μ :=
    condExpKernel_comp_trim (hm := hmk)
  -- Measurability of the increment
  have hdiff_mble : Measurable (fun ω => doob μ f (k + 1) ω - doob μ f k ω) := by
    have h1 := (doob_stronglyMeasurable μ f (k + 1)).measurable
    have h2 := (doob_stronglyMeasurable μ f k).measurable.mono (exposureσ_mono (Nat.le_succ k)) le_rfl
    exact (h1.sub h2).mono (exposureσ_le _) le_rfl
  -- Use hasCondSubgammaMGF_of_bounded_above
  refine hasCondSubgammaMGF_of_bounded_above hmk hV hc ?_ ?_ ?_ ?_ ?_ ?_
  · -- hcenter: martingale property
    -- Integrability of the increment follows from boundedness
    have hint_diff : Integrable (fun ω => doob μ f (k + 1) ω - doob μ f k ω) μ := by
      exact Integrable.mono' (integrable_const c) hdiff_mble.aestronglyMeasurable hbd
    -- Integrability of doob μ f k
    have hint_k : Integrable (fun ω => doob μ f k ω) μ := by
      simp only [doob]
      exact integrable_condExp (μ := μ) (m := exposureσ k)
    -- Integrability of doob μ f (k+1)
    have hint_k1 : Integrable (fun ω => doob μ f (k + 1) ω) μ := by
      have heq : (fun ω => doob μ f (k + 1) ω) =
          (fun ω => doob μ f (k + 1) ω - doob μ f k ω) + (fun ω => doob μ f k ω) := by
        ext ω; simp
      rw [heq]
      exact hint_diff.add hint_k
    -- Tower property: μ[doob μ f (k+1) | exposureσ k] =ᵐ[μ] doob μ f k
    have htower : (μ[doob μ f (k + 1) | exposureσ k] : _) =ᵐ[μ] doob μ f k :=
      condExp_condExp_of_le (exposureσ_mono (Nat.le_succ k)) (exposureσ_le _)
    -- doob μ f k is strongly measurable w.r.t. exposureσ k
    have hsm_k : StronglyMeasurable[exposureσ k] (fun ω => doob μ f k ω) :=
      doob_stronglyMeasurable μ f k
    -- self-tower: μ[doob μ f k | exposureσ k] =ᵐ[μ] doob μ f k
    have hself : (μ[doob μ f k | exposureσ k] : _) =ᵐ[μ] doob μ f k := by
      exact Filter.EventuallyEq.symm (Filter.Eventually.of_forall
        (fun x => (condExp_of_stronglyMeasurable (exposureσ_le k) hsm_k hint_k).symm ▸ rfl))
    -- The increment conditional expectation
    have hsub : μ[fun ω => doob μ f (k + 1) ω - doob μ f k ω | exposureσ k] =ᵐ[μ]
        (μ[doob μ f (k + 1) | exposureσ k] - μ[doob μ f k | exposureσ k]) :=
      condExp_sub (m := exposureσ k) hint_k1 hint_k
    have heq0 : (μ[fun ω => doob μ f (k + 1) ω - doob μ f k ω | exposureσ k] : _) =ᵐ[μ] 0 := by
      refine hsub.trans ?_
      refine Filter.EventuallyEq.trans (Filter.EventuallyEq.sub htower hself) ?_
      exact Filter.Eventually.of_forall (fun x => sub_self _)
    -- Convert from μ-ae to μ.trim hmk-ae
    have heq0_trim : (μ[fun ω => doob μ f (k + 1) ω - doob μ f k ω | exposureσ k] : _) =ᵐ[μ.trim hmk] 0 :=
      StronglyMeasurable.ae_eq_trim_of_stronglyMeasurable hmk stronglyMeasurable_condExp
        stronglyMeasurable_zero heq0
    have heq2 := condExp_ae_eq_trim_integral_condExpKernel hmk hint_diff
    filter_upwards [heq2, heq0_trim] with ω h2 h0
    exact h2.symm ▸ h0
  · -- hbound: convert hbd to conditional form
    have hbd' : ∀ᵐ ω ∂(condExpKernel μ (exposureσ (α := α) k) ∘ₘ μ.trim hmk),
        |doob μ f (k + 1) ω - doob μ f k ω| ≤ c := by rw [hcomp]; exact hbd
    have hbd_ae_ae := Measure.ae_ae_of_ae_comp hbd'
    filter_upwards [hbd_ae_ae] with ω hω
    filter_upwards [hω] with x hx
    exact le_of_abs_le hx
  · exact hsecond -- hsecond
  · -- hXint: integrability from boundedness
    exact Integrable.mono' (integrable_const c) hdiff_mble.aestronglyMeasurable hbd
  · -- hXsqint: integrability of X² from boundedness
    have hXsq_bound : ∀ᵐ ω ∂μ, ‖(doob μ f (k + 1) ω - doob μ f k ω) ^ 2‖ ≤ c ^ 2 := by
      filter_upwards [hbd] with ω hω
      simp only [Real.norm_eq_abs, abs_pow]
      gcongr
    have hXsq_mble : Measurable (fun x => (doob μ f (k + 1) x - doob μ f k x) ^ 2) :=
      Measurable.pow_const hdiff_mble 2
    exact Integrable.mono' (integrable_const (c ^ 2)) hXsq_mble.aestronglyMeasurable hXsq_bound
  · -- hexpint: exp(t*X) is integrable since |X| ≤ c implies exp(t*X) ≤ exp(|t|*c)
    intro t
    have hexp_bound : ∀ᵐ ω ∂μ, ‖Real.exp (t * (doob μ f (k + 1) ω - doob μ f k ω))‖ ≤ Real.exp (|t| * c) := by
      filter_upwards [hbd] with ω hω
      simp only [Real.norm_eq_abs, Real.abs_exp]
      have habs : t * (doob μ f (k + 1) ω - doob μ f k ω) ≤ |t| * c := by
        calc t * (doob μ f (k + 1) ω - doob μ f k ω)
            ≤ |t * (doob μ f (k + 1) ω - doob μ f k ω)| := le_abs_self _
          _ = |t| * |doob μ f (k + 1) ω - doob μ f k ω| := by rw [abs_mul]
          _ ≤ |t| * c := by gcongr
      exact Real.exp_le_exp.mpr habs
    have hexp_mble : Measurable (fun x => Real.exp (t * (doob μ f (k + 1) x - doob μ f k x))) := by
      fun_prop
    exact Integrable.mono' (integrable_const (Real.exp (|t| * c)))
      hexp_mble.aestronglyMeasurable hexp_bound

end Nibble
