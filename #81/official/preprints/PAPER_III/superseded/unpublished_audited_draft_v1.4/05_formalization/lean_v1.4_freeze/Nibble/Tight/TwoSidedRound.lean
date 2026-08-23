/-
# Nibble — the TWO-SIDED good round

`exists_good_round_mcdiarmid` avoids the two-sided bad event
`Bad₂ = {∃ v, c ≤ |deg_res(v) − 𝔼|}` but only *exposes* the resulting floor
`deg_res(v) > deg(v)(1 − rΔp) − c`.  Both bounds are available from the same outcome; this file
extracts them.

* `exists_good_round_two_sided` — generic in the retention `ρ` and in the bad-event bound: an outcome
  `ω` which is simultaneously
  - **floor**: `deg(v)·(1 − rΔp) − c < deg_res(v)` for every `v`,
  - **ceiling**: `deg_res(v) < deg(v)·(1 − p(1−p)^{rΔ}) + c` for every `v`,
  - **covering**: its round matching has `≥ |H|·p(1−p)^{rΔ} − |V|·ℙ(Bad₂)` edges.
* `exists_good_round_two_sided_mcdiarmid` — the same at the concrete Bernoulli-configuration space,
  with the bad-event bound supplied by the McDiarmid tail sum.

The ceiling uses `residual_degree_expectation_upper`, the floor `residual_degree_expectation_lower`.

Sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.OneRoundGood
import Nibble.RegularityBadTwoSided
import Nibble.RegularityBadMcDiarmid
import Nibble.ResidualDegree
import Nibble.ResidualDegreeUpper
import Nibble.BernoulliConfig
import Nibble.Prelude

open MeasureTheory ProbabilityTheory Finset Hypergraph

namespace Nibble

variable {V : Type*} [Fintype V] [DecidableEq V] {Ω : Type*} [MeasureSpace Ω]
  [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- **The two-sided good round.**  An outcome that avoids the two-sided regularity bad event gives
BOTH a floor and a ceiling for every residual degree, together with the covering bound. -/
theorem exists_good_round_two_sided {H : Finset (Finset V)} {p : ℝ} {r Δ : ℕ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hr1 : 1 ≤ r)
    (hr : IsUniform H r) (hΔ : ∀ x, degree H x ≤ Δ) {c : ℝ}
    (hBad1 : ((ℙ : Measure Ω) {ω | ∃ v : V,
        c ≤ |(degree (Hypergraph.residual H (retainedSet H ρ ω)) v : ℝ)
          - (ℙ : Measure Ω)[fun ω =>
              (degree (Hypergraph.residual H (retainedSet H ρ ω)) v : ℝ)]|}).toReal < 1) :
    ∃ ω : Ω,
      (∀ v : V, (degree H v : ℝ) * (1 - r * Δ * p) - c
          < (degree (Hypergraph.residual H (retainedSet H ρ ω)) v : ℝ))
      ∧ (∀ v : V, (degree (Hypergraph.residual H (retainedSet H ρ ω)) v : ℝ)
          < (degree H v : ℝ) * (1 - p * (1 - p) ^ (r * Δ)) + c)
      ∧ (H.card : ℝ) * (p * (1 - p) ^ (r * Δ))
          - (Fintype.card V : ℝ) * ((ℙ : Measure Ω) {ω | ∃ v : V,
              c ≤ |(degree (Hypergraph.residual H (retainedSet H ρ ω)) v : ℝ)
                - (ℙ : Measure Ω)[fun ω =>
                    (degree (Hypergraph.residual H (retainedSet H ρ ω)) v : ℝ)]|}).toReal
        ≤ ((roundMatching (retainedSet H ρ ω)).card : ℝ) := by
  set Bad : Set Ω := {ω | ∃ v : V,
      c ≤ |(degree (Hypergraph.residual H (retainedSet H ρ ω)) v : ℝ)
        - (ℙ : Measure Ω)[fun ω =>
            (degree (Hypergraph.residual H (retainedSet H ρ ω)) v : ℝ)]|} with hBad
  have hBadMeas : MeasurableSet Bad := measurableSet_regularityBadTwoSided ρ
  obtain ⟨ω, hω_notin, hcov⟩ :=
    exists_covering_avoiding_bad ρ hp0 hp1 hr1 hr hΔ hBadMeas hBad1
  refine ⟨ω, fun v => ?_, fun v => ?_, hcov⟩
  · have hmean := residual_degree_expectation_lower ρ hp0 hp1 hr hΔ v
    have hnotv : ¬ (c ≤ |(degree (Hypergraph.residual H (retainedSet H ρ ω)) v : ℝ)
        - (ℙ : Measure Ω)[fun ω =>
            (degree (Hypergraph.residual H (retainedSet H ρ ω)) v : ℝ)]|) := fun h =>
      hω_notin ⟨v, h⟩
    push_neg at hnotv
    have habs := (abs_lt.mp hnotv).1
    linarith
  · have hmean := residual_degree_expectation_upper ρ hp0 hp1 hr1 hr hΔ v
    have hnotv : ¬ (c ≤ |(degree (Hypergraph.residual H (retainedSet H ρ ω)) v : ℝ)
        - (ℙ : Measure Ω)[fun ω =>
            (degree (Hypergraph.residual H (retainedSet H ρ ω)) v : ℝ)]|) := fun h =>
      hω_notin ⟨v, h⟩
    push_neg at hnotv
    have habs := (abs_lt.mp hnotv).2
    linarith

/-- **The two-sided good round at the Bernoulli configuration space**, with the bad-event bound
supplied by the McDiarmid tail sum (the same hypothesis as `exists_good_round_mcdiarmid`). -/
theorem exists_good_round_two_sided_mcdiarmid (H : Finset (Finset V)) {p : ℝ} {r Δ : ℕ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hr1 : 1 ≤ r) (hr : IsUniform H r) (hΔ : ∀ x, degree H x ≤ Δ)
    {c : ℝ} (hc0 : 0 ≤ c)
    (hsmall : (∑ _v : V, ENNReal.ofReal (2 * Real.exp (-c ^ 2 / (2 * mcdiarmidCoeffSum H)))) < 1) :
    letI : MeasureSpace (Finset V → Bool) := bernoulliConfigSpace p hp0 hp1
    ∃ ω : Finset V → Bool,
      (∀ v : V, (degree H v : ℝ) * (1 - r * Δ * p) - c
          < (degree (Hypergraph.residual H
              (retainedSet H (bernoulliConfigRetention H hp0 hp1) ω)) v : ℝ))
      ∧ (∀ v : V, (degree (Hypergraph.residual H
              (retainedSet H (bernoulliConfigRetention H hp0 hp1) ω)) v : ℝ)
          < (degree H v : ℝ) * (1 - p * (1 - p) ^ (r * Δ)) + c) := by
  letI : MeasureSpace (Finset V → Bool) := bernoulliConfigSpace p hp0 hp1
  haveI : IsProbabilityMeasure (ℙ : Measure (Finset V → Bool)) := by
    show IsProbabilityMeasure (Measure.pi (fun _ : Finset V => bernoulliConfigMeasure p hp0 hp1))
    infer_instance
  have hBad1 := regularityBadMcDiarmid_prob_lt_one H hp0 hp1 hc0 hsmall
  obtain ⟨ω, hfloor, hceil, _⟩ :=
    exists_good_round_two_sided (bernoulliConfigRetention H hp0 hp1) hp0 hp1 hr1 hr hΔ hBad1
  exact ⟨ω, hfloor, hceil⟩

end Nibble
