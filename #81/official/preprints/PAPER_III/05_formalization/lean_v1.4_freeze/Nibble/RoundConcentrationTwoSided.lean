/-
# Nibble — Module C4a : two-sided concentration of the retained degree

Standalone, Mathlib-only. Foundation for the Rödl-nibble project.

Complements C3's upper tail with the lower tail and the combined two-sided bound: the number of
retained edges through a vertex `v` stays within `t` of its mean `p · deg v`, except with
probability `≤ 2 · exp(-2 t² / deg v)`. This is the per-vertex concentration the round invariant
(C4) unions over all vertices.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.Basic
import Nibble.Concentration
import Nibble.Expectation
import Nibble.RoundConcentration
import Nibble.Prelude

open MeasureTheory ProbabilityTheory Finset Hypergraph

namespace Nibble

variable {V : Type*} [DecidableEq V] {Ω : Type*} [MeasureSpace Ω]
  [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- **C4a-lower — retained-degree lower tail.** `P(retained deg through v ≤ p·deg v − t)
≤ exp(-2 t² / deg v)`. Prove by mirroring `retained_degree_upper_tail` with the lower-tail
sub-Gaussian bound (`HasSubgaussianMGF.measure_sum_le_le_of_iIndepFun`, or apply the upper tail to
the negated indicators `-ρ.I`). -/
theorem retained_degree_lower_tail {H : Finset (Finset V)} {p : ℝ}
    (ρ : Retention (Ω := Ω) H p) (v : V) (t : ℝ) (ht : 0 ≤ t) :
    (ℙ {ω | (∑ e ∈ H.filter (fun e => v ∈ e), ρ.I e ω) ≤ p * (degree H v : ℝ) - t})
      ≤ ENNReal.ofReal (Real.exp (-2 * t ^ 2 / (degree H v : ℝ))) := by
  -- Define the complementary retention process with parameter 1 - p
  let ρ' : Retention H (1 - p) := {
    I := fun e ω => 1 - ρ.I e ω
    meas := fun e => measurable_const.sub (ρ.meas e)
    indep := ρ.indep.comp (fun _ x => 1 - x) (fun _ => measurable_const.sub measurable_id)
    integrable := fun e => (integrable_const (1 : ℝ)).sub (ρ.integrable e)
    expect := fun e he => by
      rw [integral_sub (integrable_const 1) (ρ.integrable e)]
      simp [ρ.expect e he]
    zeroone := fun e => (ρ.zeroone e).mono fun ω h => by constructor <;> linarith only [h.1, h.2]
  }
  -- Apply the upper tail to the complementary process
  have h := retained_degree_upper_tail ρ' v t ht
  -- The sets are equal: ∑(1 - ρ.I) ≥ (1-p)*deg + t ⟺ ∑ρ.I ≤ p*deg - t
  have hset : {ω | ∑ e ∈ H.filter (fun e => v ∈ e), ρ'.I e ω ≥ (1 - p) * (degree H v : ℝ) + t} =
              {ω | ∑ e ∈ H.filter (fun e => v ∈ e), ρ.I e ω ≤ p * (degree H v : ℝ) - t} := by
    ext ω
    simp only [Set.mem_setOf_eq, ρ']
    have hcard : ((H.filter (fun e => v ∈ e)).card : ℝ) = (degree H v : ℝ) := by rw [degree]
    constructor
    · intro hsum
      have : ∑ e ∈ H.filter (fun e => v ∈ e), (1 - ρ.I e ω) =
             (degree H v : ℝ) - ∑ e ∈ H.filter (fun e => v ∈ e), ρ.I e ω := by
        rw [← hcard]
        simp [Finset.sum_sub_distrib]
      linarith only [hsum, this]
    · intro hsum
      have : ∑ e ∈ H.filter (fun e => v ∈ e), (1 - ρ.I e ω) =
             (degree H v : ℝ) - ∑ e ∈ H.filter (fun e => v ∈ e), ρ.I e ω := by
        rw [← hcard]
        simp [Finset.sum_sub_distrib]
      linarith only [hsum, this]
  rw [← hset]
  exact h

/-- **C4a — two-sided retained-degree concentration.** The retained degree through `v` deviates
from its mean `p·deg v` by more than `t` with probability at most `2·exp(-2 t² / deg v)`. -/
theorem retained_degree_concentration {H : Finset (Finset V)} {p : ℝ}
    (ρ : Retention (Ω := Ω) H p) (v : V) (t : ℝ) (ht : 0 ≤ t) :
    (ℙ {ω | t < |(∑ e ∈ H.filter (fun e => v ∈ e), ρ.I e ω) - p * (degree H v : ℝ)|})
      ≤ 2 * ENNReal.ofReal (Real.exp (-2 * t ^ 2 / (degree H v : ℝ))) := by
  have hupper := retained_degree_upper_tail ρ v t ht
  have hlower := retained_degree_lower_tail ρ v t ht
  have hdecomp : {ω | t < |(∑ e ∈ (H.filter (fun e => v ∈ e)), ρ.I e ω) - p * (degree H v : ℝ)|} ⊆
      {ω | p * (degree H v : ℝ) + t < ∑ e ∈ H.filter (fun e => v ∈ e), ρ.I e ω} ∪
      {ω | ∑ e ∈ H.filter (fun e => v ∈ e), ρ.I e ω < p * (degree H v : ℝ) - t} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω
    simp only [Set.mem_union, Set.mem_setOf_eq]
    rw [abs_eq_max_neg, lt_max_iff] at hω
    rcases hω with h | h <;> [left; right] <;> linarith only [h]
  have hsub1 : {ω | p * (degree H v : ℝ) + t < ∑ e ∈ H.filter (fun e => v ∈ e), ρ.I e ω} ⊆
      {ω | (∑ e ∈ H.filter (fun e => v ∈ e), ρ.I e ω) ≥ p * (degree H v : ℝ) + t} := by
    intro ω hω
    simp only [Set.mem_setOf_eq, ge_iff_le] at hω ⊢
    linarith only [hω]
  have hsub2 : {ω | ∑ e ∈ H.filter (fun e => v ∈ e), ρ.I e ω < p * (degree H v : ℝ) - t} ⊆
      {ω | (∑ e ∈ H.filter (fun e => v ∈ e), ρ.I e ω) ≤ p * (degree H v : ℝ) - t} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    linarith only [hω]
  calc (ℙ : Measure Ω) {ω | t < |(∑ e ∈ (H.filter (fun e => v ∈ e)), ρ.I e ω) - p * (degree H v : ℝ)|}
      ≤ (ℙ : Measure Ω) ({ω | p * (degree H v : ℝ) + t < ∑ e ∈ H.filter (fun e => v ∈ e), ρ.I e ω} ∪
        {ω | ∑ e ∈ H.filter (fun e => v ∈ e), ρ.I e ω < p * (degree H v : ℝ) - t}) :=
          measure_mono hdecomp
    _ ≤ (ℙ : Measure Ω) {ω | p * (degree H v : ℝ) + t < ∑ e ∈ H.filter (fun e => v ∈ e), ρ.I e ω} +
        (ℙ : Measure Ω) {ω | ∑ e ∈ H.filter (fun e => v ∈ e), ρ.I e ω < p * (degree H v : ℝ) - t} :=
          measure_union_le _ _
    _ ≤ (ℙ : Measure Ω) {ω | (∑ e ∈ H.filter (fun e => v ∈ e), ρ.I e ω) ≥ p * (degree H v : ℝ) + t} +
        (ℙ : Measure Ω) {ω | (∑ e ∈ H.filter (fun e => v ∈ e), ρ.I e ω) ≤ p * (degree H v : ℝ) - t} := by
          exact add_le_add (measure_mono hsub1) (measure_mono hsub2)
    _ ≤ ENNReal.ofReal (Real.exp (-2 * t ^ 2 / (degree H v : ℝ))) +
        ENNReal.ofReal (Real.exp (-2 * t ^ 2 / (degree H v : ℝ))) :=
          add_le_add hupper hlower
    _ = 2 * ENNReal.ofReal (Real.exp (-2 * t ^ 2 / (degree H v : ℝ))) := by ring

end Nibble
