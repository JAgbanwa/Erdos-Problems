/-
# Nibble — the regularity-failure event : measurability and `P < 1`

Standalone, Mathlib-only. Turns `round_regularity_failure` (C4) into the two facts the one-round
selector (`exists_covering_avoiding_bad`) needs about the concrete "bad" event

  `Bad = {ω | ∃ v, deg(residual) v ≤ deg(H) v · (1 − rΔp) − c}` :

* `measurableSet_regularityBad` — `Bad` is measurable (finite union over `v` of sublevel sets of the
  measurable residual-degree functions).
* `regularityBad_prob_lt_one` — if the variance bound `∑Var/c²` is `< 1` (a parameter condition on
  `c`), then `P(Bad) < 1`, so a good outcome outside `Bad` exists.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.Basic
import Nibble.Round
import Nibble.Covered
import Nibble.Measurable
import Nibble.RoundInvariant
import Nibble.Prelude

open MeasureTheory ProbabilityTheory Finset Hypergraph
open scoped Classical

namespace Nibble

variable {V : Type*} [DecidableEq V] [Fintype V] {Ω : Type*} [MeasureSpace Ω]
  [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- Residual membership is a measurable event (copied pattern from `ResidualDegree`). -/
theorem measurableSet_residual_mem {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (e : Finset V) :
    MeasurableSet {ω | e ∈ Hypergraph.residual H (retainedSet H ρ ω)} := by
  simp only [Hypergraph.residual, Finset.mem_filter]
  have h1 : {ω | e ∈ H ∧ Disjoint e (covered (retainedSet H ρ ω))} =
      {ω | e ∈ H} ∩ {ω | Disjoint e (covered (retainedSet H ρ ω))} := rfl
  rw [h1]
  apply MeasurableSet.inter
  · by_cases he : e ∈ H <;> simp [he]
  · have heq : {ω | Disjoint e (covered (retainedSet H ρ ω))} =
        ⋂ v ∈ e, {ω | v ∉ covered (retainedSet H ρ ω)} := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_setOf_eq]
      rw [Finset.disjoint_iff_inter_eq_empty]
      refine ⟨?_, ?_⟩
      · intro h x hx hxc
        exact absurd (h ▸ Finset.mem_inter.mpr ⟨hx, hxc⟩) (by simp)
      · intro h
        apply Finset.ext
        intro x
        simp [Finset.mem_inter]
        exact h x
    rw [heq]
    apply Finset.measurableSet_biInter
    intro v _
    exact MeasurableSet.compl (measurableSet_vertex_covered ρ v)

/-- The residual degree at `v` is a measurable function of the outcome. -/
theorem measurable_residual_degree {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (v : V) :
    Measurable (fun ω => (degree (Hypergraph.residual H (retainedSet H ρ ω)) v : ℝ)) := by
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
  rw [hdeg_eq]
  apply Finset.measurable_sum
  intro e _
  exact Measurable.ite (measurableSet_residual_mem ρ e) measurable_const measurable_const

/-- **Step 1a — the regularity-failure event is measurable.** -/
theorem measurableSet_regularityBad {H : Finset (Finset V)} {p : ℝ} {r Δ : ℕ} {c : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) :
    MeasurableSet {ω | ∃ v : V,
      (degree (Hypergraph.residual H (retainedSet H ρ ω)) v : ℝ)
        ≤ (degree H v : ℝ) * (1 - r * Δ * p) - c} := by
  rw [Set.setOf_exists]
  refine MeasurableSet.iUnion (fun v => ?_)
  exact measurableSet_le (measurable_residual_degree ρ v) measurable_const

/-- **Step 1b — the regularity-failure probability is `< 1`.** If the Chebyshev variance bound
`∑Var/c²` is `< 1`, then `P(Bad) < 1` (in `ℝ` after `toReal`), so an outcome avoiding `Bad` exists. -/
theorem regularityBad_prob_lt_one {H : Finset (Finset V)} {p : ℝ} {r Δ : ℕ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : IsUniform H r) (hΔ : ∀ x, degree H x ≤ Δ) {c : ℝ} (hc : 0 < c)
    (hsmall : (∑ v : V, ENNReal.ofReal
        (Var[fun ω => (degree (Hypergraph.residual H (retainedSet H ρ ω)) v : ℝ);
          (ℙ : Measure Ω)] / c ^ 2)) < 1) :
    ((ℙ : Measure Ω) {ω | ∃ v : V,
        (degree (Hypergraph.residual H (retainedSet H ρ ω)) v : ℝ)
          ≤ (degree H v : ℝ) * (1 - r * Δ * p) - c}).toReal < 1 := by
  have hle := round_regularity_failure ρ hp0 hp1 hr hΔ hc
  have hlt : (ℙ : Measure Ω) {ω | ∃ v : V,
      (degree (Hypergraph.residual H (retainedSet H ρ ω)) v : ℝ)
        ≤ (degree H v : ℝ) * (1 - r * Δ * p) - c} < 1 := lt_of_le_of_lt hle hsmall
  have hne : (ℙ : Measure Ω) {ω | ∃ v : V,
      (degree (Hypergraph.residual H (retainedSet H ρ ω)) v : ℝ)
        ≤ (degree H v : ℝ) * (1 - r * Δ * p) - c} ≠ ⊤ := (hlt.trans_le le_top).ne
  calc _ < (1 : ENNReal).toReal := (ENNReal.toReal_lt_toReal hne (by simp)).mpr hlt
    _ = 1 := by simp

end Nibble
