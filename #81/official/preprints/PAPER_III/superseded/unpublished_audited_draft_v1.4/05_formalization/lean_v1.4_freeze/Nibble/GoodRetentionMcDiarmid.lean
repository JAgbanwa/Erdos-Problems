/-
# Nibble — Finset-level McDiarmid good retention (N5b)

Standalone, Mathlib-only. The `Finset`-abstraction companion of `exists_good_round_mcdiarmid` (N5a):
packages the good retained configuration `ω` as a retained SUBSET `R' ⊆ H` (hiding the measure space),
with the bad-probability replaced by the explicit McDiarmid tail total
`δ = (∑_v 2·exp(…)).toReal` (bounded via the N4 union bound `≥ P(Bad)`). This is the exact shape the
retention strategy / discharge chain consumes — the McDiarmid analogue of `exists_good_retention'`
(which used the Chebyshev variance sum).

Coefficient-agnostic: works with whatever `mcdiarmidCoeffSum H` denotes; re-instantiating with the
sharp count coefficient only changes that sum.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.GoodRoundMcDiarmid
import Nibble.RegularityBadMcDiarmid
import Nibble.BernoulliConfig
import Nibble.Prelude

open MeasureTheory ProbabilityTheory Finset Hypergraph
open scoped ENNReal Classical

namespace Nibble

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **N5b — Finset-level McDiarmid good retention.** If the McDiarmid tail sum is `< 1`, there is a
retained subset `R' ⊆ H` that is near-regular below and covers
`≥ H.card·p(1-p)^{rΔ} − |V|·δ`, where `δ = (∑_v 2·exp(…)).toReal` is the explicit tail total. Extracts
the good config from `exists_good_round_mcdiarmid` and bounds `P(Bad) ≤ ∑_v 2·exp(…)` via the union
bound. The McDiarmid replacement for `exists_good_retention'`. -/
theorem exists_good_retention_mcd' (H : Finset (Finset V)) {p : ℝ} {r Δ : ℕ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hr1 : 1 ≤ r) (hr : IsUniform H r) (hΔ : ∀ x, degree H x ≤ Δ)
    {c : ℝ} (hc0 : 0 ≤ c)
    (hsmall : (∑ _v : V, ENNReal.ofReal (2 * Real.exp (-c ^ 2 / (2 * mcdiarmidCoeffSum H)))) < 1) :
    ∃ R' : Finset (Finset V), R' ⊆ H
      ∧ (∀ v : V, (degree H v : ℝ) * (1 - r * Δ * p) - c
          < (degree (residual H R') v : ℝ))
      ∧ (H.card : ℝ) * (p * (1 - p) ^ (r * Δ))
          - (Fintype.card V : ℝ) *
              ((∑ _v : V, ENNReal.ofReal (2 * Real.exp (-c ^ 2 / (2 * mcdiarmidCoeffSum H)))).toReal)
        ≤ ((roundMatching R').card : ℝ) := by
  letI : MeasureSpace (Finset V → Bool) := bernoulliConfigSpace p hp0 hp1
  haveI : IsProbabilityMeasure (ℙ : Measure (Finset V → Bool)) := by
    show IsProbabilityMeasure (Measure.pi (fun _ : Finset V => bernoulliConfigMeasure p hp0 hp1))
    infer_instance
  obtain ⟨ω, hreg, hcov⟩ :=
    exists_good_round_mcdiarmid H hp0 hp1 hr1 hr hΔ hc0 hsmall
  refine ⟨retainedSet H (bernoulliConfigRetention H hp0 hp1) ω, Finset.filter_subset _ _, hreg, ?_⟩
  -- bound P(Bad).toReal by the tail total δ
  set δE : ℝ≥0∞ := ∑ _v : V, ENNReal.ofReal (2 * Real.exp (-c ^ 2 / (2 * mcdiarmidCoeffSum H)))
    with hδE
  set Bad : Set (Finset V → Bool) := {ω | ∃ v : V,
      c ≤ |(degree (residual H (retainedSet H (bernoulliConfigRetention H hp0 hp1) ω)) v : ℝ)
        - (ℙ : Measure (Finset V → Bool))[fun ω =>
            (degree (residual H (retainedSet H (bernoulliConfigRetention H hp0 hp1) ω)) v : ℝ)]|}
    with hBad
  have hBadsub : Bad ⊆ ⋃ v ∈ (Finset.univ : Finset V),
      {ω | c ≤ |(degree (residual H (retainedSet H (bernoulliConfigRetention H hp0 hp1) ω)) v : ℝ)
        - (ℙ : Measure (Finset V → Bool))[fun ω =>
            (degree (residual H (retainedSet H (bernoulliConfigRetention H hp0 hp1) ω)) v : ℝ)]|} := by
    intro ω hω
    obtain ⟨v, hv⟩ := hω
    exact Set.mem_biUnion (Finset.mem_univ v) hv
  have hPle : (ℙ : Measure (Finset V → Bool)) Bad ≤ δE :=
    (measure_mono hBadsub).trans (all_vertices_residualDeg_concentration_mcdiarmid H hp0 hp1 hc0)
  have hδ : ((ℙ : Measure (Finset V → Bool)) Bad).toReal ≤ δE.toReal :=
    ENNReal.toReal_mono (hsmall.trans ENNReal.one_lt_top).ne hPle
  have hcardpos : (0 : ℝ) ≤ (Fintype.card V : ℝ) := Nat.cast_nonneg _
  calc (H.card : ℝ) * (p * (1 - p) ^ (r * Δ)) - (Fintype.card V : ℝ) * δE.toReal
      ≤ (H.card : ℝ) * (p * (1 - p) ^ (r * Δ))
          - (Fintype.card V : ℝ) * ((ℙ : Measure (Finset V → Bool)) Bad).toReal := by
        have := mul_le_mul_of_nonneg_left hδ hcardpos; linarith
    _ ≤ ((roundMatching (retainedSet H (bernoulliConfigRetention H hp0 hp1) ω)).card : ℝ) := hcov

/-- Count-sharp Finset-level McDiarmid good retention, with loss controlled by
`∑_v exp(-c²/(2 ∑_e neighborCoef²))`. -/
theorem exists_good_retention_mcd_neighborCoef' (H : Finset (Finset V)) {p : ℝ} {r Δ : ℕ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hr1 : 1 ≤ r) (hr : IsUniform H r) (hΔ : ∀ x, degree H x ≤ Δ)
    {c : ℝ} (hc0 : 0 ≤ c)
    (hsmall : (∑ v : V, ENNReal.ofReal
      (2 * Real.exp (-c ^ 2 / (2 * mcdiarmidNeighborCoeffSum H v)))) < 1) :
    ∃ R' : Finset (Finset V), R' ⊆ H
      ∧ (∀ v : V, (degree H v : ℝ) * (1 - r * Δ * p) - c
          < (degree (residual H R') v : ℝ))
      ∧ (H.card : ℝ) * (p * (1 - p) ^ (r * Δ))
          - (Fintype.card V : ℝ) *
              ((∑ v : V, ENNReal.ofReal
                (2 * Real.exp (-c ^ 2 / (2 * mcdiarmidNeighborCoeffSum H v)))).toReal)
        ≤ ((roundMatching R').card : ℝ) := by
  letI : MeasureSpace (Finset V → Bool) := bernoulliConfigSpace p hp0 hp1
  haveI : IsProbabilityMeasure (ℙ : Measure (Finset V → Bool)) := by
    show IsProbabilityMeasure (Measure.pi (fun _ : Finset V => bernoulliConfigMeasure p hp0 hp1))
    infer_instance
  obtain ⟨ω, hreg, hcov⟩ :=
    exists_good_round_mcdiarmid_neighborCoef H hp0 hp1 hr1 hr hΔ hc0 hsmall
  refine ⟨retainedSet H (bernoulliConfigRetention H hp0 hp1) ω, Finset.filter_subset _ _, hreg, ?_⟩
  set δE : ℝ≥0∞ := ∑ v : V, ENNReal.ofReal
    (2 * Real.exp (-c ^ 2 / (2 * mcdiarmidNeighborCoeffSum H v))) with hδE
  set Bad : Set (Finset V → Bool) := {ω | ∃ v : V,
      c ≤ |(degree (residual H (retainedSet H (bernoulliConfigRetention H hp0 hp1) ω)) v : ℝ)
        - (ℙ : Measure (Finset V → Bool))[fun ω =>
            (degree (residual H (retainedSet H (bernoulliConfigRetention H hp0 hp1) ω)) v : ℝ)]|}
    with hBad
  have hBadsub : Bad ⊆ ⋃ v ∈ (Finset.univ : Finset V),
      {ω | c ≤ |(degree (residual H (retainedSet H (bernoulliConfigRetention H hp0 hp1) ω)) v : ℝ)
        - (ℙ : Measure (Finset V → Bool))[fun ω =>
            (degree (residual H (retainedSet H (bernoulliConfigRetention H hp0 hp1) ω)) v : ℝ)]|} := by
    intro ω hω
    obtain ⟨v, hv⟩ := hω
    exact Set.mem_biUnion (Finset.mem_univ v) hv
  have hPle : (ℙ : Measure (Finset V → Bool)) Bad ≤ δE := by
    simpa [δE] using
      (measure_mono hBadsub).trans
        (all_vertices_residualDeg_concentration_mcdiarmid_neighborCoef H hp0 hp1 hc0)
  have hδ : ((ℙ : Measure (Finset V → Bool)) Bad).toReal ≤ δE.toReal :=
    ENNReal.toReal_mono (hsmall.trans ENNReal.one_lt_top).ne hPle
  have hcardpos : (0 : ℝ) ≤ (Fintype.card V : ℝ) := Nat.cast_nonneg _
  calc (H.card : ℝ) * (p * (1 - p) ^ (r * Δ)) - (Fintype.card V : ℝ) * δE.toReal
      ≤ (H.card : ℝ) * (p * (1 - p) ^ (r * Δ))
          - (Fintype.card V : ℝ) * ((ℙ : Measure (Finset V → Bool)) Bad).toReal := by
        have := mul_le_mul_of_nonneg_left hδ hcardpos; linarith
    _ ≤ ((roundMatching (retainedSet H (bernoulliConfigRetention H hp0 hp1) ω)).card : ℝ) := hcov

end Nibble
