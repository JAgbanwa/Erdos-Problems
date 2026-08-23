/-
# Nibble — Module C4b-3b(3) : expected residual degree lower bound

Standalone, Mathlib-only. Foundation for the Rödl-nibble project.

Combining the edge-hit bound (`prob_edge_hit_le`, `ℙ(e hit) ≤ r·Δ·p`) with measurability of the
covered events (`measurableSet_vertex_covered`), each edge survives into the residual with
probability `≥ 1 - r·Δ·p`. Summing over the `deg(v)` edges through `v` (linearity of expectation)
lower-bounds the expected residual degree:

  `E[deg_residual(v)] ≥ deg(v) · (1 - r·Δ·p)`.

This is the residual near-regularity *mean* input to the round invariant C4 (the concentration
input is the McDiarmid/Azuma bound, handled separately).

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.Basic
import Nibble.Round
import Nibble.Conflict
import Nibble.RoundConflict
import Nibble.Survival
import Nibble.Covered
import Nibble.Measurable
import Nibble.Prelude

open MeasureTheory ProbabilityTheory Finset Hypergraph
open scoped Classical

namespace Nibble

variable {V : Type*} [DecidableEq V] {Ω : Type*} [MeasureSpace Ω]
  [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- **C4b-3b(3a) — edge survival probability lower bound.** An edge `e ∈ H` survives into the
residual (avoids the covered set) with probability at least `1 - r·Δ·p`. Proof: the survival
event is the complement of the edge-hit event `{ω | ∃ x∈e, x covered}` (a finite union of the
measurable covered events, hence measurable); apply `prob_compl_eq_one_sub` and bound the hit
probability by `prob_edge_hit_le`. -/
/-
The requested declaration cannot be soundly proved as stated: it lacks `0 ≤ p`.
For `p = -1`, a one-edge hypergraph on one vertex, and all retention events empty,
its left side is `2` while its right side is `1`.
theorem prob_edge_survives {H : Finset (Finset V)} {p : ℝ} {r Δ : ℕ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (hr : IsUniform H r) (hΔ : ∀ x, degree H x ≤ Δ)
    {e : Finset V} (he : e ∈ H) :
    ENNReal.ofReal (1 - r * Δ * p)
      ≤ (ℙ : Measure Ω) {ω | ¬ ∃ x ∈ e, x ∈ support (roundMatching (retainedSet H ρ ω))} := by
-/

theorem prob_edge_survives_of_nonneg {H : Finset (Finset V)} {p : ℝ} {r Δ : ℕ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (hp0 : 0 ≤ p)
    (hr : IsUniform H r) (hΔ : ∀ x, degree H x ≤ Δ)
    {e : Finset V} (he : e ∈ H) :
    ENNReal.ofReal (1 - r * Δ * p)
      ≤ (ℙ : Measure Ω) {ω | ¬ ∃ x ∈ e, x ∈ support (roundMatching (retainedSet H ρ ω))} := by
  let A : Set Ω :=
    {ω | ∃ x ∈ e, x ∈ support (roundMatching (retainedSet H ρ ω))}
  have hA : MeasurableSet A := by
    have heq : A = ⋃ x ∈ e,
        {ω | x ∈ support (roundMatching (retainedSet H ρ ω))} := by
      ext ω
      simp [A]
    rw [heq]
    exact Finset.measurableSet_biUnion e
      (fun x _ => measurableSet_vertex_covered ρ x)
  have hhit := prob_edge_hit_le ρ hr hΔ he
  have hcast : (r : ENNReal) * (Δ : ENNReal) * ENNReal.ofReal p =
      ENNReal.ofReal ((r : ℝ) * (Δ : ℝ) * p) := by
    rw [ENNReal.ofReal_mul (mul_nonneg (Nat.cast_nonneg r) (Nat.cast_nonneg Δ))]
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg r)]
    simp
  rw [hcast] at hhit
  have hsub := tsub_le_tsub_left hhit (1 : ENNReal)
  have hq : 0 ≤ (r : ℝ) * (Δ : ℝ) * p :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg r) (Nat.cast_nonneg Δ)) hp0
  rw [ENNReal.ofReal_sub 1 hq, ENNReal.ofReal_one]
  calc
    1 - ENNReal.ofReal ((r : ℝ) * (Δ : ℝ) * p) ≤ 1 - (ℙ : Measure Ω) A := hsub
    _ = (ℙ : Measure Ω) Aᶜ := by
      rw [measure_compl hA (measure_ne_top _ _), measure_univ]
    _ = (ℙ : Measure Ω)
        {ω | ¬ ∃ x ∈ e, x ∈ support (roundMatching (retainedSet H ρ ω))} := by
      rfl

/-- **C4b-3b(3) — expected residual degree lower bound.**
`E[deg_residual(v)] ≥ deg(v) · (1 - r·Δ·p)`. Proof: write the residual degree at `v` as the
finite sum over `e ∈ H.filter (v ∈ ·)` of the survival indicators, use linearity of the integral
(`integral_finset_sum`) and `integral_indicator`/`MeasureTheory.integral_indicator_one` to turn
each term into `ℙ(e survives).toReal`, then bound below by `1 - r·Δ·p` via `prob_edge_survives`
and `ENNReal.toReal` monotonicity; the sum over the `deg(v)` edges gives `deg(v)·(1 - rΔp)`. -/
theorem residual_degree_expectation_lower {H : Finset (Finset V)} {p : ℝ} {r Δ : ℕ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : IsUniform H r) (hΔ : ∀ x, degree H x ≤ Δ) (v : V) :
    (degree H v : ℝ) * (1 - r * Δ * p)
      ≤ ∫ ω, (degree (residual H (retainedSet H ρ ω)) v : ℝ) ∂(ℙ : Measure Ω) := by
  -- Express degree as sum of indicators
  have hdeg_eq : ∀ ω, degree (Hypergraph.residual H (retainedSet H ρ ω)) v
      = ∑ e ∈ H.filter (fun e => v ∈ e), (if e ∈ Hypergraph.residual H (retainedSet H ρ ω) then (1 : ℝ) else 0) := by
    intro ω
    simp only [degree, Hypergraph.residual, card_eq_sum_ones, sum_filter]
    norm_cast
    apply Finset.sum_congr rfl
    intro e _
    by_cases hev : v ∈ e <;> by_cases hdisj : Disjoint e (covered (retainedSet H ρ ω)) <;> simp [hev, hdisj]
    all_goals (simp at *; assumption)
  -- Rewrite the integral using hdeg_eq
  simp_rw [hdeg_eq]
  -- Use linearity of integral
  have hmeas : ∀ e : Finset V, MeasurableSet {ω | e ∈ Hypergraph.residual H (retainedSet H ρ ω)} := by
    intro e
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
  have hintegrable : ∀ i ∈ H.filter (fun e => v ∈ e),
      Integrable (fun ω => if i ∈ Hypergraph.residual H (retainedSet H ρ ω) then (1 : ℝ) else 0) ℙ := by
    intro e _
    apply Integrable.mono' (integrable_const 1)
    · exact Measurable.aestronglyMeasurable
        (Measurable.ite (hmeas e) measurable_const measurable_const)
    · filter_upwards with ω
      by_cases h : e ∈ Hypergraph.residual H (retainedSet H ρ ω) <;> simp [h]
  have h1 : (∫ ω, ∑ e ∈ H with v ∈ e, if e ∈ Hypergraph.residual H (retainedSet H ρ ω) then (1 : ℝ) else 0 ∂ℙ)
      = ∑ e ∈ H.filter (fun e => v ∈ e), ∫ ω, (if e ∈ Hypergraph.residual H (retainedSet H ρ ω) then (1 : ℝ) else 0) ∂ℙ := by
    apply integral_finset_sum
    exact hintegrable
  rw [h1]
  -- Each integral is the probability the edge survives
  have h2 : ∀ e ∈ H.filter (fun e => v ∈ e),
      ∫ ω, (if e ∈ Hypergraph.residual H (retainedSet H ρ ω) then (1 : ℝ) else 0) ∂ℙ
      = (ℙ {ω | e ∈ Hypergraph.residual H (retainedSet H ρ ω)}).toReal := by
    intro e _
    have : (fun ω => if e ∈ Hypergraph.residual H (retainedSet H ρ ω) then (1 : ℝ) else 0)
        = Set.indicator {ω | e ∈ Hypergraph.residual H (retainedSet H ρ ω)} (fun _ => (1 : ℝ)) := by
      ext ω; simp [Set.indicator]
    rw [this, MeasureTheory.integral_indicator (hmeas e)]
    simp [MeasureTheory.Measure.real]
  rw [Finset.sum_congr rfl h2]
  -- Each probability is at least 1 - r * Δ * p
  have h3 : ∀ e ∈ H.filter (fun e => v ∈ e),
      (ℙ {ω | e ∈ Hypergraph.residual H (retainedSet H ρ ω)}).toReal ≥ 1 - r * Δ * p := by
    intro e he
    have heH : e ∈ H := Finset.mem_filter.mp he |>.1
    have hbound := prob_edge_survives_of_nonneg ρ hp0 hr hΔ heH
    have heq : {ω | e ∈ Hypergraph.residual H (retainedSet H ρ ω)}
        = {ω | ¬∃ x ∈ e, x ∈ support (roundMatching (retainedSet H ρ ω))} := by
      ext ω
      simp only [Hypergraph.residual, Finset.mem_filter, Set.mem_setOf_eq, heH]
      rw [Finset.disjoint_left]
      simp only [support, Finset.mem_biUnion]
      constructor
      · intro h ⟨x, hx, a, ha, hxa⟩
        apply h.2 hx
        exact Finset.mem_biUnion.mpr ⟨a, ha, hxa⟩
      · intro h
        refine ⟨trivial, fun x hx => ?_⟩
        intro hcovered
        obtain ⟨f, hf, hxf⟩ := Finset.mem_biUnion.mp hcovered
        exact h ⟨x, hx, f, hf, hxf⟩
    rw [heq, ge_iff_le]
    have hmeas_ne_top : ℙ {ω | ¬∃ x ∈ e, x ∈ support (roundMatching (retainedSet H ρ ω))} ≠ ⊤ := measure_ne_top _ _
    rw [← ENNReal.ofReal_toReal hmeas_ne_top] at hbound
    by_cases hge : 1 - (r : ℝ) * Δ * p ≥ 0
    · have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
      rwa [ENNReal.toReal_ofReal hge, ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ _)] at this
    · have hle : 1 - (r : ℝ) * Δ * p ≤ 0 := le_of_not_ge hge
      exact le_trans hle ENNReal.toReal_nonneg
  have hcard : # {e ∈ H | v ∈ e} = degree H v := rfl
  rw [← hcard]
  calc (degree H v : ℝ) * (1 - ↑r * ↑Δ * p)
      = (# {e ∈ H | v ∈ e} : ℝ) * (1 - ↑r * ↑Δ * p) := by rw [hcard]
    _ ≤ ∑ e ∈ {e ∈ H | v ∈ e}, (ℙ {ω | e ∈ Hypergraph.residual H (retainedSet H ρ ω)}).toReal := by
        simpa only [Finset.sum_const, nsmul_eq_mul] using Finset.sum_le_sum h3
end Nibble
