/-
# Nibble — good round from the McDiarmid concentration (N5a)

Standalone, Mathlib-only. The McDiarmid analogue of `GoodRound.exists_good_round`: at the concrete
config retention `bernoulliConfigRetention`, if the McDiarmid tail sum `∑_v 2·exp(…) < 1`, then there
is a retained configuration `ω` that is simultaneously

* **near-regular below**: every residual degree stays above `deg(v)·(1−rΔp) − c`, and
* **covering**: its round matching covers `≥ H.card·p(1−p)^{rΔ} − |V|·P(Bad₂)` vertices' worth of
  edges.

The point: `exists_covering_avoiding_bad` is already generic over the bad set, so we feed it the
McDiarmid two-sided `Bad₂` (measurable by `measurableSet_regularityBadTwoSided`, probability `< 1` by
`regularityBadMcDiarmid_prob_lt_one`). The near-regularity threshold is recovered from `ω ∉ Bad₂`
(`|deg − 𝔼| < c`) together with the mean lower bound `residual_degree_expectation_lower`
(`𝔼 ≥ deg(v)·(1−rΔp)`). This is the per-round input the nibble oracle consumes — now on an
**exponential** tail, valid in the window `c ≈ √(d log n) ≪ d`.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.OneRoundGood
import Nibble.RegularityBadMcDiarmid
import Nibble.RegularityBadTwoSided
import Nibble.ResidualDegree
import Nibble.BernoulliConfig
import Nibble.Prelude

open MeasureTheory ProbabilityTheory Finset Hypergraph

namespace Nibble

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **N5a — good round from the McDiarmid tail.** At `ρ = bernoulliConfigRetention`, if the McDiarmid
sum is `< 1`, some configuration is near-regular below and covering. Exponential-tail replacement for
`exists_good_round` (which relied on the Chebyshev variance sum). -/
theorem exists_good_round_mcdiarmid (H : Finset (Finset V)) {p : ℝ} {r Δ : ℕ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hr1 : 1 ≤ r) (hr : IsUniform H r) (hΔ : ∀ x, degree H x ≤ Δ)
    {c : ℝ} (hc0 : 0 ≤ c)
    (hsmall : (∑ _v : V, ENNReal.ofReal (2 * Real.exp (-c ^ 2 / (2 * mcdiarmidCoeffSum H)))) < 1) :
    letI : MeasureSpace (Finset V → Bool) := bernoulliConfigSpace p hp0 hp1
    ∃ ω : Finset V → Bool,
      (∀ v : V, (degree H v : ℝ) * (1 - r * Δ * p) - c
          < (degree (residual H (retainedSet H (bernoulliConfigRetention H hp0 hp1) ω)) v : ℝ))
      ∧ (H.card : ℝ) * (p * (1 - p) ^ (r * Δ))
          - (Fintype.card V : ℝ) * ((ℙ : Measure (Finset V → Bool)) {ω | ∃ v : V,
              c ≤ |(degree (residual H (retainedSet H (bernoulliConfigRetention H hp0 hp1) ω)) v : ℝ)
                - (ℙ : Measure (Finset V → Bool))[fun ω =>
                    (degree (residual H (retainedSet H (bernoulliConfigRetention H hp0 hp1) ω)) v : ℝ)]|}).toReal
        ≤ ((roundMatching (retainedSet H (bernoulliConfigRetention H hp0 hp1) ω)).card : ℝ) := by
  letI : MeasureSpace (Finset V → Bool) := bernoulliConfigSpace p hp0 hp1
  haveI : IsProbabilityMeasure (ℙ : Measure (Finset V → Bool)) := by
    show IsProbabilityMeasure (Measure.pi (fun _ : Finset V => bernoulliConfigMeasure p hp0 hp1))
    infer_instance
  set ρ := bernoulliConfigRetention H hp0 hp1 with hρ
  set Bad : Set (Finset V → Bool) := {ω | ∃ v : V,
      c ≤ |(degree (residual H (retainedSet H ρ ω)) v : ℝ)
        - (ℙ : Measure (Finset V → Bool))[fun ω =>
            (degree (residual H (retainedSet H ρ ω)) v : ℝ)]|} with hBad
  have hBadMeas : MeasurableSet Bad := measurableSet_regularityBadTwoSided ρ
  have hBad1 : ((ℙ : Measure (Finset V → Bool)) Bad).toReal < 1 :=
    regularityBadMcDiarmid_prob_lt_one H hp0 hp1 hc0 hsmall
  obtain ⟨ω, hω_notin, hcov⟩ :=
    exists_covering_avoiding_bad ρ hp0 hp1 hr1 hr hΔ hBadMeas hBad1
  refine ⟨ω, fun v => ?_, hcov⟩
  have hmean := residual_degree_expectation_lower ρ hp0 hp1 hr hΔ v
  have hnotv : ¬ (c ≤ |(degree (residual H (retainedSet H ρ ω)) v : ℝ)
      - (ℙ : Measure (Finset V → Bool))[fun ω =>
          (degree (residual H (retainedSet H ρ ω)) v : ℝ)]|) := fun h => hω_notin ⟨v, h⟩
  push_neg at hnotv
  have habs := (abs_lt.mp hnotv).1
  linarith only [habs, hmean]

/-- Count-sharp version of `exists_good_round_mcdiarmid`, using the true `neighborCoef` tail sum. -/
theorem exists_good_round_mcdiarmid_neighborCoef (H : Finset (Finset V)) {p : ℝ} {r Δ : ℕ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hr1 : 1 ≤ r) (hr : IsUniform H r) (hΔ : ∀ x, degree H x ≤ Δ)
    {c : ℝ} (hc0 : 0 ≤ c)
    (hsmall : (∑ v : V, ENNReal.ofReal
      (2 * Real.exp (-c ^ 2 / (2 * mcdiarmidNeighborCoeffSum H v)))) < 1) :
    letI : MeasureSpace (Finset V → Bool) := bernoulliConfigSpace p hp0 hp1
    ∃ ω : Finset V → Bool,
      (∀ v : V, (degree H v : ℝ) * (1 - r * Δ * p) - c
          < (degree (residual H (retainedSet H (bernoulliConfigRetention H hp0 hp1) ω)) v : ℝ))
      ∧ (H.card : ℝ) * (p * (1 - p) ^ (r * Δ))
          - (Fintype.card V : ℝ) * ((ℙ : Measure (Finset V → Bool)) {ω | ∃ v : V,
              c ≤ |(degree (residual H (retainedSet H (bernoulliConfigRetention H hp0 hp1) ω)) v : ℝ)
                - (ℙ : Measure (Finset V → Bool))[fun ω =>
                    (degree (residual H (retainedSet H (bernoulliConfigRetention H hp0 hp1) ω)) v : ℝ)]|}).toReal
        ≤ ((roundMatching (retainedSet H (bernoulliConfigRetention H hp0 hp1) ω)).card : ℝ) := by
  letI : MeasureSpace (Finset V → Bool) := bernoulliConfigSpace p hp0 hp1
  haveI : IsProbabilityMeasure (ℙ : Measure (Finset V → Bool)) := by
    show IsProbabilityMeasure (Measure.pi (fun _ : Finset V => bernoulliConfigMeasure p hp0 hp1))
    infer_instance
  set ρ := bernoulliConfigRetention H hp0 hp1 with hρ
  set Bad : Set (Finset V → Bool) := {ω | ∃ v : V,
      c ≤ |(degree (residual H (retainedSet H ρ ω)) v : ℝ)
        - (ℙ : Measure (Finset V → Bool))[fun ω =>
            (degree (residual H (retainedSet H ρ ω)) v : ℝ)]|} with hBad
  have hBadMeas : MeasurableSet Bad := measurableSet_regularityBadTwoSided ρ
  have hBad1 : ((ℙ : Measure (Finset V → Bool)) Bad).toReal < 1 :=
    regularityBadMcDiarmid_neighborCoef_prob_lt_one H hp0 hp1 hc0 hsmall
  obtain ⟨ω, hω_notin, hcov⟩ :=
    exists_covering_avoiding_bad ρ hp0 hp1 hr1 hr hΔ hBadMeas hBad1
  refine ⟨ω, fun v => ?_, hcov⟩
  have hmean := residual_degree_expectation_lower ρ hp0 hp1 hr hΔ v
  have hnotv : ¬ (c ≤ |(degree (residual H (retainedSet H ρ ω)) v : ℝ)
      - (ℙ : Measure (Finset V → Bool))[fun ω =>
          (degree (residual H (retainedSet H ρ ω)) v : ℝ)]|) := fun h => hω_notin ⟨v, h⟩
  push_neg at hnotv
  have habs := (abs_lt.mp hnotv).1
  linarith only [habs, hmean]

end Nibble
