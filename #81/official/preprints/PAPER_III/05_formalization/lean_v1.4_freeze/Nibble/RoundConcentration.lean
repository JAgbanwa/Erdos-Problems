/-
# Nibble — Module C3 : concentration of the retained degree

Standalone, Mathlib-only. Foundation for the Rödl-nibble project.

Combines C2 (expected retained degree = `p · deg v`) with B1 (Hoeffding upper tail) to show the
number of retained edges through a vertex concentrates around its mean.

* `hoeffding_upper_finset` — a `Finset`-indexed version of `Nibble.hoeffding_upper`.
* `retained_degree_upper_tail` — `P(#retained edges through v ≥ p·deg v + t) ≤ exp(-2t²/deg v)`.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.Basic
import Nibble.Concentration
import Nibble.Expectation
import Nibble.Prelude

open MeasureTheory ProbabilityTheory Finset Hypergraph

namespace Nibble

variable {V : Type*} [DecidableEq V] {Ω : Type*} [MeasureSpace Ω]
  [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- **B1' — Hoeffding upper tail, `Finset`-indexed.** -/
theorem hoeffding_upper_finset {ι : Type*} {X : ι → Ω → ℝ} (s : Finset ι)
    (hmeas : ∀ i ∈ s, Measurable (X i))
    (hindep : iIndepFun X (ℙ : Measure Ω))
    (h01 : ∀ i ∈ s, ∀ᵐ ω ∂(ℙ : Measure Ω), X i ω ∈ Set.Icc (0 : ℝ) 1)
    (t : ℝ) (ht : 0 ≤ t) :
    (ℙ {ω | (∑ i ∈ s, X i ω) ≥ (∑ i ∈ s, ∫ ω, X i ω ∂ℙ) + t})
      ≤ ENNReal.ofReal (Real.exp (-2 * t ^ 2 / (s.card : ℝ))) := by
  let Y : ι → Ω → ℝ := fun i ω ↦ X i ω - ∫ ω, X i ω ∂ℙ
  have hY_indep : iIndepFun Y ℙ := by
    have h := hindep.comp (fun i x ↦ x - ∫ ω, X i ω ∂ℙ)
      (fun _ ↦ measurable_id.sub measurable_const)
    simpa [Y, Function.comp_def] using h
  have hY_subG : ∀ i ∈ s,
      HasSubgaussianMGF (Y i) (((2 : NNReal) ^ 2)⁻¹) ℙ := by
    intro i hi
    simpa [Y] using
      (hasSubgaussianMGF_of_mem_Icc (X := X i) (a := (0 : ℝ)) (b := 1)
        (hmeas i hi).aemeasurable (h01 i hi))
  have hbound := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hY_indep
    (s := s) (fun i hi ↦ hY_subG i hi) ht
  have hreal :
      (ℙ : Measure Ω).real {ω | (∑ i ∈ s, X i ω) ≥ (∑ i ∈ s, ∫ ω, X i ω ∂ℙ) + t}
        ≤ Real.exp (-2 * t ^ 2 / (s.card : ℝ)) := by
    calc
      (ℙ : Measure Ω).real {ω | (∑ i ∈ s, X i ω) ≥ (∑ i ∈ s, ∫ ω, X i ω ∂ℙ) + t}
          = (ℙ : Measure Ω).real {ω | t ≤ ∑ i ∈ s, Y i ω} := by
              congr 1
              ext ω
              simp only [Set.mem_setOf_eq, Y]
              rw [Finset.sum_sub_distrib]
              constructor <;> intro h <;> linarith
      _ ≤ Real.exp (-t ^ 2 / (2 * ∑ i ∈ s, (((2 : NNReal) ^ 2)⁻¹))) := hbound
      _ = Real.exp (-2 * t ^ 2 / (s.card : ℝ)) := by
        congr 1
        simp
        by_cases hs : s.card = 0
        · simp [hs]
        · field_simp
  rw [← ENNReal.ofReal_toReal (measure_ne_top ℙ _)]
  exact ENNReal.ofReal_le_ofReal hreal

/-- **C3 — retained-degree upper tail.** -/
theorem retained_degree_upper_tail {H : Finset (Finset V)} {p : ℝ}
    (ρ : Retention (Ω := Ω) H p)
    (v : V) (t : ℝ) (ht : 0 ≤ t) :
    (ℙ {ω | (∑ e ∈ H.filter (fun e => v ∈ e), ρ.I e ω) ≥ p * (degree H v : ℝ) + t})
      ≤ ENNReal.ofReal (Real.exp (-2 * t ^ 2 / (degree H v : ℝ))) := by
  have hmean : (∑ e ∈ H.filter (fun e => v ∈ e), ∫ ω, ρ.I e ω ∂(ℙ : Measure Ω))
      = p * (degree H v : ℝ) := by
    rw [Finset.sum_congr rfl (fun e he => ρ.expect e (Finset.mem_of_mem_filter e he))]
    rw [Finset.sum_const, nsmul_eq_mul, degree, mul_comm]
  have hcard : ((H.filter (fun e => v ∈ e)).card : ℝ) = (degree H v : ℝ) := by
    rw [degree]
  have h := hoeffding_upper_finset (Ω := Ω) (X := ρ.I) (H.filter (fun e => v ∈ e))
    (fun e _ => ρ.meas e) ρ.indep (fun e _ => ρ.zeroone e) t ht
  rw [hmean, hcard] at h
  exact h

end Nibble
