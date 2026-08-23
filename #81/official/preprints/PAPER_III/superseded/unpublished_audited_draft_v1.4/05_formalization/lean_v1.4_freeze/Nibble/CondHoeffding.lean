/-
# Nibble — Module M3 : conditional Hoeffding lemma

Standalone, Mathlib-only. Foundation for the McDiarmid bridge (Layer M) of the Rödl-nibble project.

Conditional analogue of `ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero`:
a random variable that is a.s. bounded in `[a,b]` and has conditional expectation `0` given a
sub-σ-algebra `m` is conditionally sub-Gaussian with parameter `(b-a)²/4`. This is the martingale
increment bound feeding Azuma (`measure_sum_ge_le_of_hasCondSubgaussianMGF`) to obtain McDiarmid.

NOTE TO PROVER: adapt the exact phrasing of the conditional-mean-zero hypothesis and the
sub-Gaussian parameter to Mathlib v4.28's `HasCondSubgaussianMGF` / `condExpKernel` API — but it
MUST be a genuine conditional Hoeffding bound (bounded range ⇒ conditionally sub-Gaussian with
parameter of order `(b-a)²`), fully proved, with no proof placeholders or new assumptions. Mirror
the unconditional proof `hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero` (in Mathlib's
SubGaussian.lean), lifting it through the conditional expectation kernel `condExpKernel μ m`.
-/
import Nibble.Prelude

open MeasureTheory ProbabilityTheory

namespace Nibble

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} {hm : m ≤ mΩ} {μ : Measure Ω}

/-- **M3 — conditional Hoeffding.** A variable a.s. in `[a,b]` with conditional expectation `0`
given `m` is conditionally sub-Gaussian with parameter `(b-a)²/4`. -/
theorem hasCondSubgaussianMGF_of_mem_Icc [StandardBorelSpace Ω] [IsProbabilityMeasure μ]
    {a b : ℝ} {X : Ω → ℝ} (hXm : Measurable X)
    (hb : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b)
    (hmean : μ[X | m] =ᵐ[μ] 0) :
    HasCondSubgaussianMGF m hm X ⟨(b - a) ^ 2 / 4, by positivity⟩ μ := by
  let c : NNReal := ⟨(b - a) ^ 2 / 4, by positivity⟩
  have hXint : Integrable X μ := Integrable.of_mem_Icc a b hXm.aemeasurable hb
  have hb_kernel : ∀ᵐ ω ∂(μ.trim hm), ∀ᵐ y ∂condExpKernel μ m ω, X y ∈ Set.Icc a b := by
    apply Measure.ae_ae_of_ae_comp
    rwa [condExpKernel_comp_trim]
  have hmean_trim : μ[X | m] =ᵐ[μ.trim hm] 0 :=
    StronglyMeasurable.ae_eq_trim_of_stronglyMeasurable hm stronglyMeasurable_condExp
      stronglyMeasurable_zero hmean
  have hint := condExp_ae_eq_trim_integral_condExpKernel hm hXint
  change Kernel.HasSubgaussianMGF X c (condExpKernel μ m) (μ.trim hm)
  refine ⟨?_, ?_⟩
  · intro t
    rw [condExpKernel_comp_trim]
    exact integrable_exp_mul_of_mem_Icc hXm.aemeasurable hb
  · filter_upwards [hb_kernel, hmean_trim, hint] with ω hbound hzero hintegral
    have hmgf := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
      hXm.aemeasurable hbound (hintegral ▸ hzero)
    intro t
    convert hmgf.mgf_le t using 1
    apply congrArg (fun z : ℝ => Real.exp (z * t ^ 2 / 2))
    norm_cast
    apply NNReal.eq
    simp [c]
    nlinarith only [sq_abs (b - a)]

end Nibble
