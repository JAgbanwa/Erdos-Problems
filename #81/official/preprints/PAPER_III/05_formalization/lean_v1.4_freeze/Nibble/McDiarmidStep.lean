/-
# Nibble — McDiarmid M6 : Doob martingale differences are conditionally sub-Gaussian

This file proves the assembly step from a conditional bounded-difference estimate for a Doob
increment to its conditional sub-Gaussian MGF bound.  The bounded-difference assumption is stated
in the conditional form actually consumed by this step: after marginalising the unexposed
independent coordinates, the increment has absolute value at most the coordinate coefficient.
This formulation cleanly separates the model-specific marginalisation argument from M6.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.CondHoeffding
import Nibble.McDiarmid
import Nibble.Prelude

open MeasureTheory ProbabilityTheory Finset

namespace Nibble

variable {n : ℕ} {α : Fin n → Type*} [∀ i, MeasurableSpace (α i)]

/-- **M6 — the Doob increment is conditionally sub-Gaussian.**

`hbd` is the conditional/marginalised form of the bounded-difference hypothesis: for independent
coordinates it is obtained by integrating out all unexposed coordinates and applying the
coordinate-`j` oscillation bound.  Stating that model-specific fact explicitly makes this theorem
the reusable martingale assembly step.

The model-specific assumptions (independence, measurability, and integrability) are precisely what
one uses to establish `hbd`; they are not needed again by this assembly lemma. -/
theorem doob_increment_hasCondSubgaussianMGF
    [∀ i, StandardBorelSpace (α i)]
    (μ : Measure (∀ i, α i)) [IsProbabilityMeasure μ]
    (f : (∀ i, α i) → ℝ) {c : ℕ → ℝ}
    (hbd : ∀ (j : ℕ), j < n → ∀ᵐ ω ∂μ,
      |doob μ f (j + 1) ω - doob μ f j ω| ≤ c j)
    (k : ℕ) (hk : k < n) :
    HasCondSubgaussianMGF (exposureσ k) (exposureσ_le k)
      (fun ω => doob μ f (k + 1) ω - doob μ f k ω) ⟨(c k) ^ 2, by positivity⟩ μ := by
  have hparam : (⟨(c k - (-c k)) ^ 2 / 4, by positivity⟩ : NNReal) = ⟨(c k) ^ 2, by positivity⟩ := by
    apply NNReal.eq
    simp; ring
  rw [← hparam]
  apply hasCondSubgaussianMGF_of_mem_Icc
  · have h1 : StronglyMeasurable[exposureσ (k + 1)] (doob μ f (k + 1)) := doob_stronglyMeasurable μ f (k + 1)
    have h2 : StronglyMeasurable[exposureσ k] (doob μ f k) := doob_stronglyMeasurable μ f k
    exact (h1.measurable.sub (h2.measurable.mono (exposureσ_mono (Nat.le_succ k)) le_rfl)).mono (exposureσ_le _) le_rfl
  · filter_upwards [hbd k hk] with ω hω
    exact abs_le.mp hω
  · -- Martingale property: the increment has conditional expectation 0
    -- Integrability follows from boundedness
    have hbound : ∀ᵐ ω ∂μ, |doob μ f (k + 1) ω - doob μ f k ω| ≤ c k := hbd k hk
    have hdiff_mble : Measurable (fun ω => doob μ f (k + 1) ω - doob μ f k ω) := by
      have h1 := (doob_stronglyMeasurable μ f (k + 1)).measurable
      have h2 := (doob_stronglyMeasurable μ f k).measurable.mono (exposureσ_mono (Nat.le_succ k)) le_rfl
      exact (h1.sub h2).mono (exposureσ_le _) le_rfl
    have hint_diff : Integrable (fun ω => doob μ f (k + 1) ω - doob μ f k ω) μ := by
      refine Integrable.mono' ?_ hdiff_mble.aestronglyMeasurable hbound
      exact integrable_const (c k)
    have htower : (μ[doob μ f (k + 1) | exposureσ k] : _) =ᵐ[μ] doob μ f k :=
      condExp_condExp_of_le (exposureσ_mono (Nat.le_succ k)) (exposureσ_le _)
    -- doob μ f k = μ[f | exposureσ k] is integrable since f is integrable
    have hint_k : Integrable (fun ω => doob μ f k ω) μ := by
      simp only [doob]
      exact integrable_condExp (μ := μ) (m := exposureσ k)
    -- doob μ f (k+1) is also integrable
    have hint_k1 : Integrable (fun ω => doob μ f (k + 1) ω) μ := by
      have heq : (fun ω => doob μ f (k + 1) ω) = (fun ω => doob μ f (k + 1) ω - doob μ f k ω) + (fun ω => doob μ f k ω) := by
        ext ω; simp
      rw [heq]
      exact hint_diff.add hint_k
    have hsub : μ[fun ω => doob μ f (k + 1) ω - doob μ f k ω | exposureσ k] =ᵐ[μ]
        (μ[doob μ f (k + 1) | exposureσ k] - μ[doob μ f k | exposureσ k]) :=
      condExp_sub (m := exposureσ k) hint_k1 hint_k
    refine hsub.trans ?_
    -- Need to show that μ[doob μ f (k+1) | exposureσ k] - μ[doob μ f k | exposureσ k] =ᵐ 0
    -- We have htower: μ[doob μ f (k+1) | exposureσ k] =ᵐ doob μ f k
    -- We need: μ[doob μ f k | exposureσ k] =ᵐ doob μ f k
    have hself : (μ[doob μ f k | exposureσ k] : _) =ᵐ[μ] doob μ f k := by
      have h : μ[doob μ f k | exposureσ k] = doob μ f k :=
        condExp_of_stronglyMeasurable (exposureσ_le k) (doob_stronglyMeasurable μ f k) hint_k
      exact Filter.EventuallyEq.symm (Filter.Eventually.of_forall (fun x => h.symm ▸ rfl))
    refine Filter.EventuallyEq.trans (Filter.EventuallyEq.sub htower hself) ?_
    exact Filter.Eventually.of_forall (fun x => sub_self _)

end Nibble
