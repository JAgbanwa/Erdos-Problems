/-
# Nibble — abstract good-event selection lemma (measure-theoretic glue)

Pure Mathlib. The crux glue for the Rödl-nibble iteration: on a probability space, a nonnegative
bounded integrable random variable `f` with mean `≥ m` and a "bad" event `Bad` of small probability
admits an outcome OUTSIDE `Bad` where `f` is still at least `m − M·P(Bad)`.

This is the probabilistic-method step that lets one round simultaneously (i) cover many vertices
(large `f = matching size`) and (ii) avoid the regularity-failure event `Bad`. Splitting
`∫ f = ∫_Bad f + ∫_Badᶜ f` with `∫_Bad f ≤ M·P(Bad)` gives `∫_Badᶜ f ≥ m − M·P(Bad)`, and a point of
`Badᶜ` attains at least the average there.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.Prelude

open MeasureTheory
open scoped ProbabilityTheory

namespace Nibble

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- **Good-event selection.** For a nonnegative, `M`-bounded, integrable `f` with `m ≤ E[f]` and a
measurable bad event `Bad`, there is an outcome `ω ∉ Bad` with `m − M·P(Bad) ≤ f ω`. -/
theorem exists_notin_bad_ge {f : Ω → ℝ} {Bad : Set Ω} {m M : ℝ}
    (hf : Integrable f (ℙ : Measure Ω)) (hf0 : ∀ ω, 0 ≤ f ω) (hfM : ∀ ω, f ω ≤ M)
    (hBad : MeasurableSet Bad) (hBad1 : (ℙ Bad).toReal < 1)
    (hm : m ≤ ∫ ω, f ω ∂(ℙ : Measure Ω)) :
    ∃ ω, ω ∉ Bad ∧ m - M * (ℙ Bad).toReal ≤ f ω := by
  have hM0 : 0 ≤ M := by
    let ω : Ω := Classical.choice (MeasureTheory.nonempty_of_isProbabilityMeasure ℙ)
    exact (hf0 ω).trans (hfM ω)
  have hIntBad : ∫ ω in Bad, f ω ∂ℙ ≤ M * (ℙ Bad).toReal := by
    calc
      ∫ ω in Bad, f ω ∂ℙ ≤ ∫ _ω in Bad, M ∂ℙ :=
        setIntegral_mono_on hf.integrableOn (integrableOn_const (measure_ne_top ℙ Bad))
          hBad (fun ω _ ↦ hfM ω)
      _ = M * (ℙ Bad).toReal := by simp [measureReal_def, mul_comm]
  have hIntCompl : m - M * (ℙ Bad).toReal ≤ ∫ ω in Badᶜ, f ω ∂ℙ := by
    rw [setIntegral_compl hBad hf]
    linarith
  have hμComplReal_pos : 0 < (ℙ Badᶜ).toReal := by
    rw [← measureReal_def, measureReal_compl hBad, probReal_univ]
    exact sub_pos.mpr hBad1
  have hμCompl_ne : ℙ Badᶜ ≠ 0 := by
    intro h
    simp [h] at hμComplReal_pos
  have hμCompl_top : ℙ Badᶜ ≠ ⊤ := measure_ne_top ℙ _
  obtain ⟨ω, hω, havg⟩ :=
    exists_setAverage_le hμCompl_ne hμCompl_top hf.integrableOn
  refine ⟨ω, hω, ?_⟩
  have hμComplReal_le : (ℙ Badᶜ).toReal ≤ 1 := by
    rw [← measureReal_def]
    simpa using measureReal_mono (μ := ℙ) (show Badᶜ ⊆ Set.univ from Set.subset_univ _)
  rw [setAverage_eq, smul_eq_mul, inv_mul_eq_div] at havg
  simp only [measureReal_def] at havg
  have hIntCompl0 : 0 ≤ ∫ ω in Badᶜ, f ω ∂ℙ :=
    integral_nonneg_of_ae
      (ae_restrict_iff' hBad.compl |>.2 (ae_of_all _ fun _ _ ↦ hf0 _))
  have ht :
      m - M * (ℙ Bad).toReal ≤ (∫ ω in Badᶜ, f ω ∂ℙ) / (ℙ Badᶜ).toReal := by
    by_cases ht0 : m - M * (ℙ Bad).toReal ≤ 0
    · exact ht0.trans (div_nonneg hIntCompl0 hμComplReal_pos.le)
    · apply (le_div_iff₀ hμComplReal_pos).2
      nlinarith
  exact ht.trans havg

end Nibble
