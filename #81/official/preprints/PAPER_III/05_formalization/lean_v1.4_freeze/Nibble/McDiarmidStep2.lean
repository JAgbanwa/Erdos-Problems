/-
# Nibble — McDiarmid M6.5 STEP2 : increment bound from the marginalization identity

Standalone, Mathlib-only. Given the marginalization identity (STEP1, `doob μ f k =ᵐ ∫ splice`), the
a.e. increment bound `|doob(j+1) − doob(j)| ≤ c j` follows by a short argument: the two spliced
configurations differ ONLY in coordinate `j` (`j+1` takes coord `j` from `ω`, `j` takes it from `y`),
so the integrand `f(splice_{j+1}) − f(splice_j)` is pointwise `≤ c j` by the bounded-difference
hypothesis, and integrating a `≤ c j` bound over a probability measure gives `≤ c j`.

STEP2 consumes STEP1 (`hmarg`) as a hypothesis — it will be combined with STEP1 (Aristotle) to give
the full M6.5 (`doob_increment_ae_bound`), the input `hbd` of M6 (`doob_increment_hasCondSubgaussianMGF`).
Requires `f` bounded, which holds for the residual degree (`≤ Δ`).

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.McDiarmid
import Nibble.Prelude

open MeasureTheory ProbabilityTheory Finset

namespace Nibble

variable {n : ℕ} {α : Fin n → Type*} [∀ i, MeasurableSpace (α i)]

/-- **M6.5 STEP2 — increment bound from the marginalization identity.** -/
theorem doob_increment_ae_bound_of_marginal
    (ν : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (ν i)]
    (f : (∀ i, α i) → ℝ) (hf : Measurable f) {M : ℝ} (hfb : ∀ x, |f x| ≤ M)
    {c : ℕ → ℝ}
    (hbd : ∀ (j : Fin n) (ω ω' : ∀ i, α i), (∀ i, i ≠ j → ω i = ω' i) → |f ω - f ω'| ≤ c (j : ℕ))
    (hmarg : ∀ k, doob (Measure.pi ν) f k =ᵐ[Measure.pi ν]
        fun ω => ∫ y, f (fun i => if (i : ℕ) < k then ω i else y i) ∂(Measure.pi ν))
    (j : ℕ) (hj : j < n) :
    ∀ᵐ ω ∂(Measure.pi ν),
      |doob (Measure.pi ν) f (j + 1) ω - doob (Measure.pi ν) f j ω| ≤ c j := by
  filter_upwards [hmarg (j + 1), hmarg j] with ω h1 h2
  rw [h1, h2]
  have hmeas : ∀ k, Measurable
      (fun y : ∀ i, α i => f (fun i => if (i : ℕ) < k then ω i else y i)) := by
    intro k
    refine hf.comp (measurable_pi_iff.mpr (fun i => ?_))
    by_cases hik : (i : ℕ) < k
    · simp only [hik, if_true]; exact measurable_const
    · simp only [hik, if_false]; exact measurable_pi_apply i
  have hint : ∀ k, Integrable
      (fun y : ∀ i, α i => f (fun i => if (i : ℕ) < k then ω i else y i)) (Measure.pi ν) := by
    intro k
    refine Integrable.of_mem_Icc (-M) M (hmeas k).aemeasurable ?_
    filter_upwards with y
    exact ⟨(abs_le.mp (hfb _)).1, (abs_le.mp (hfb _)).2⟩
  rw [← integral_sub (hint (j + 1)) (hint j)]
  calc |∫ y, (f (fun i => if (i : ℕ) < j + 1 then ω i else y i)
              - f (fun i => if (i : ℕ) < j then ω i else y i)) ∂(Measure.pi ν)|
      ≤ ∫ y, |f (fun i => if (i : ℕ) < j + 1 then ω i else y i)
              - f (fun i => if (i : ℕ) < j then ω i else y i)| ∂(Measure.pi ν) :=
        abs_integral_le_integral_abs
    _ ≤ ∫ _y, c j ∂(Measure.pi ν) := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall (fun y => abs_nonneg _))
          (integrable_const _) (Filter.Eventually.of_forall (fun y => ?_))
        refine hbd ⟨j, hj⟩ _ _ (fun i hi => ?_)
        have hij : (i : ℕ) ≠ j := fun h => hi (Fin.ext h)
        by_cases h1 : (i : ℕ) < j
        · rw [if_pos (by omega : (i : ℕ) < j + 1), if_pos h1]
        · rw [if_neg (by omega : ¬ (i : ℕ) < j + 1), if_neg h1]
    _ = c j := by simp

end Nibble
