/-
# Nibble — expected residual degree UPPER bound

Standalone, Mathlib-only. The companion of `residual_degree_expectation_lower`: an upper bound on the
expected residual degree,

  `E[deg_residual(v)] ≤ deg(v) · (1 − p·(1−p)^{rΔ})`.

Key idea: if edge `e` enters the round matching then `e ⊆ covered`, so `e ∉ residual`; hence the
events `{e ∈ residual}` and `{e matched}` are DISJOINT. Therefore
`P(e ∈ residual) ≤ 1 − P(e matched) = 1 − p·(1−p)^{c(e)} ≤ 1 − p·(1−p)^{rΔ}`. Summing over the
`deg(v)` edges through `v` gives the bound. Together with the lower bound and the two-sided
concentration (`RegularityBadTwoSided`), this pins the residual degree near `deg(v)·(1−rΔp … )` on
both sides — the near-regularity mean input for the step-2 invariant.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.Basic
import Nibble.Round
import Nibble.Conflict
import Nibble.Survival
import Nibble.Covered
import Nibble.CoveredExpectation
import Nibble.Assembly
import Nibble.RegularityBad
import Nibble.Prelude

open MeasureTheory ProbabilityTheory Finset Hypergraph
open scoped Classical

namespace Nibble

variable {V : Type*} [DecidableEq V] [Fintype V] {Ω : Type*} [MeasureSpace Ω]
  [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- **Expected residual degree upper bound.** `E[deg_residual(v)] ≤ deg(v)·(1 − p·(1−p)^{rΔ})`. -/
theorem residual_degree_expectation_upper {H : Finset (Finset V)} {p : ℝ} {r Δ : ℕ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hr1 : 1 ≤ r)
    (hr : IsUniform H r) (hΔ : ∀ x, degree H x ≤ Δ) (v : V) :
    ∫ ω, (degree (Hypergraph.residual H (retainedSet H ρ ω)) v : ℝ) ∂(ℙ : Measure Ω)
      ≤ (degree H v : ℝ) * (1 - p * (1 - p) ^ (r * Δ)) := by
  have hmeas : ∀ e : Finset V, MeasurableSet {ω | e ∈ Hypergraph.residual H (retainedSet H ρ ω)} :=
    fun e => measurableSet_residual_mem ρ e
  have hdeg_eq : (fun ω => (degree (Hypergraph.residual H (retainedSet H ρ ω)) v : ℝ))
      = fun ω => ∑ e ∈ H.filter (fun e => v ∈ e),
          (if e ∈ Hypergraph.residual H (retainedSet H ρ ω) then (1 : ℝ) else 0) := by
    funext ω
    simp only [degree, Hypergraph.residual, card_eq_sum_ones, sum_filter]
    norm_cast
    apply Finset.sum_congr rfl
    intro e _
    by_cases hev : v ∈ e <;> by_cases hdisj : Disjoint e (covered (retainedSet H ρ ω)) <;>
      simp [hev, hdisj]
    all_goals (simp at *; assumption)
  simp_rw [hdeg_eq]
  have hintegrable : ∀ i ∈ H.filter (fun e => v ∈ e),
      Integrable (fun ω => if i ∈ Hypergraph.residual H (retainedSet H ρ ω) then (1 : ℝ) else 0) ℙ := by
    intro e _
    apply Integrable.mono' (integrable_const 1)
    · exact Measurable.aestronglyMeasurable
        (Measurable.ite (hmeas e) measurable_const measurable_const)
    · filter_upwards with ω
      by_cases h : e ∈ Hypergraph.residual H (retainedSet H ρ ω) <;> simp [h]
  rw [integral_finset_sum _ hintegrable]
  have h2 : ∀ e ∈ H.filter (fun e => v ∈ e),
      ∫ ω, (if e ∈ Hypergraph.residual H (retainedSet H ρ ω) then (1 : ℝ) else 0) ∂ℙ
      = (ℙ {ω | e ∈ Hypergraph.residual H (retainedSet H ρ ω)}).toReal := by
    intro e _
    have hind : (fun ω => if e ∈ Hypergraph.residual H (retainedSet H ρ ω) then (1 : ℝ) else 0)
        = Set.indicator {ω | e ∈ Hypergraph.residual H (retainedSet H ρ ω)} (fun _ => (1 : ℝ)) := by
      ext ω; simp [Set.indicator]
    rw [hind, MeasureTheory.integral_indicator (hmeas e)]
    simp [MeasureTheory.Measure.real]
  rw [Finset.sum_congr rfl h2]
  -- Each residual probability is ≤ 1 - p(1-p)^{rΔ}
  have h3 : ∀ e ∈ H.filter (fun e => v ∈ e),
      (ℙ {ω | e ∈ Hypergraph.residual H (retainedSet H ρ ω)}).toReal
        ≤ 1 - p * (1 - p) ^ (r * Δ) := by
    intro e he
    have heH : e ∈ H := (Finset.mem_filter.mp he).1
    have hne : e.Nonempty := by
      rw [← Finset.card_pos, hr e heH]; omega
    -- {e ∈ residual} and {e ∈ roundMatching} are disjoint
    have hdisjEv : Disjoint {ω | e ∈ Hypergraph.residual H (retainedSet H ρ ω)}
        {ω | e ∈ roundMatching (retainedSet H ρ ω)} := by
      rw [Set.disjoint_left]
      intro ω hres hmatch
      have hsub : e ⊆ covered (retainedSet H ρ ω) := by
        rw [covered]; exact subset_support hmatch
      have hd : Disjoint e (covered (retainedSet H ρ ω)) := residual_disjoint_covered hres
      obtain ⟨x, hx⟩ := hne
      exact (Finset.disjoint_left.mp hd hx) (hsub hx)
    have hPmatch : (ℙ : Measure Ω) {ω | e ∈ roundMatching (retainedSet H ρ ω)}
        = ENNReal.ofReal (p * (1 - p) ^ (conflicts H e).card) := by
      rw [matchingEvent_eq ρ heH]; exact edge_survives_prob ρ hp0 hp1 heH
    have hfin1 : (ℙ : Measure Ω) {ω | e ∈ Hypergraph.residual H (retainedSet H ρ ω)} ≠ ⊤ :=
      measure_ne_top _ _
    have hfin2 : (ℙ : Measure Ω) {ω | e ∈ roundMatching (retainedSet H ρ ω)} ≠ ⊤ :=
      measure_ne_top _ _
    have hsum1 : (ℙ : Measure Ω) {ω | e ∈ Hypergraph.residual H (retainedSet H ρ ω)}
        + (ℙ : Measure Ω) {ω | e ∈ roundMatching (retainedSet H ρ ω)} ≤ 1 := by
      rw [← measure_union hdisjEv (measurableSet_matchingEvent ρ heH)]
      exact (measure_mono (Set.subset_univ _)).trans_eq measure_univ
    have htoReal : (ℙ {ω | e ∈ Hypergraph.residual H (retainedSet H ρ ω)}).toReal
        + (ℙ {ω | e ∈ roundMatching (retainedSet H ρ ω)}).toReal ≤ 1 := by
      rw [← ENNReal.toReal_add hfin1 hfin2]
      calc _ ≤ (1 : ENNReal).toReal := ENNReal.toReal_mono (by simp) hsum1
        _ = 1 := by simp
    have hPm : (ℙ {ω | e ∈ roundMatching (retainedSet H ρ ω)}).toReal
        = p * (1 - p) ^ (conflicts H e).card := by
      rw [hPmatch, ENNReal.toReal_ofReal (mul_nonneg hp0 (pow_nonneg (by linarith) _))]
    have hpow : p * (1 - p) ^ (r * Δ) ≤ p * (1 - p) ^ (conflicts H e).card := by
      apply mul_le_mul_of_nonneg_left _ hp0
      exact pow_le_pow_of_le_one (by linarith) (by linarith)
        (conflicts_card_le_of_uniform hr hΔ heH)
    linarith only [htoReal, hPm, hpow]
  have hcard : # {e ∈ H | v ∈ e} = degree H v := rfl
  calc ∑ e ∈ H.filter (fun e => v ∈ e),
        (ℙ {ω | e ∈ Hypergraph.residual H (retainedSet H ρ ω)}).toReal
      ≤ ∑ _e ∈ H.filter (fun e => v ∈ e), (1 - p * (1 - p) ^ (r * Δ)) := Finset.sum_le_sum h3
    _ = (degree H v : ℝ) * (1 - p * (1 - p) ^ (r * Δ)) := by
        rw [Finset.sum_const, nsmul_eq_mul, hcard]

end Nibble
