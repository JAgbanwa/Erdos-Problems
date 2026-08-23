/-
# Nibble — Finset-level good-retention bridge (dissolves the dependent Ω)

Standalone, Mathlib-only. The bridge that lets the step-2 iteration define the retention strategy `R`
WITHOUT dependent-type juggling. `exists_bernoulliRetention` produces a probability space `Ω` that
varies with `H'`; here we run it and `exists_good_round` INTERNALLY and expose only a `Finset`-level
existential:

  for `H'` (r-uniform, max degree `≤ Δ`), there is a retained subset `R' ⊆ H'` whose round
  * preserves near-regularity (every residual degree `> deg(v)·(1−rΔp) − c`), and
  * covers `≥ |H'|·p·(1−p)^{rΔ} − |V|·δ` edges,

where `δ` bounds the regularity-failure probability. The probabilistic hypothesis `hsmall` (variance
sum `< 1` and `P(Bad) ≤ δ`, for every Bernoulli retention) is left ABSTRACT here — it is discharged
downstream by `variance_sum_lt_one` (+ `regularityBad_prob_lt_one`) using the ρ-independent variance
bound. The conclusion is entirely `ρ`-free, so `R := Classical.choose` of it is an honest
`Finset (Finset V)`-valued strategy.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.GoodRound
import Nibble.BernoulliSpace
import Nibble.Prelude

open MeasureTheory ProbabilityTheory Finset Hypergraph
open scoped Classical

namespace Nibble

/-- **Finset-level good retention.** Runs `exists_bernoulliRetention` + `exists_good_round`
internally and exposes a `ρ`-free `Finset` existential: a retained subset preserving near-regularity
and covering `≥ |H'|·p·(1−p)^{rΔ} − |V|·δ`. -/
theorem exists_good_retention {V : Type u} [Fintype V] [DecidableEq V]
    (H' : Finset (Finset V)) {p : ℝ} {r Δ : ℕ} {c δ : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hr1 : 1 ≤ r)
    (hr : IsUniform H' r) (hΔ : ∀ x, degree H' x ≤ Δ) (hc : 0 < c)
    (hsmall : ∀ {Ω : Type u} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
        (ρ : BernoulliRetention (Ω := Ω) H' p),
        (∑ v : V, ENNReal.ofReal
            (Var[fun ω => (degree (Hypergraph.residual H' (retainedSet H' ρ ω)) v : ℝ);
              (ℙ : Measure Ω)] / c ^ 2)) < 1
        ∧ ((ℙ : Measure Ω) {ω | ∃ v : V,
              (degree (Hypergraph.residual H' (retainedSet H' ρ ω)) v : ℝ)
                ≤ (degree H' v : ℝ) * (1 - r * Δ * p) - c}).toReal ≤ δ) :
    ∃ R' : Finset (Finset V), R' ⊆ H'
      ∧ (∀ v : V, (degree H' v : ℝ) * (1 - r * Δ * p) - c
          < (degree (Hypergraph.residual H' R') v : ℝ))
      ∧ (H'.card : ℝ) * (p * (1 - p) ^ (r * Δ)) - (Fintype.card V : ℝ) * δ
          ≤ ((roundMatching R').card : ℝ) := by
  obtain ⟨Ω, mΩ, hProb, ⟨ρ⟩⟩ := exists_bernoulliRetention H' hp0 hp1
  letI := mΩ
  letI := hProb
  obtain ⟨hvar, hbad⟩ := hsmall ρ
  obtain ⟨ω, hreg, hcov⟩ := exists_good_round ρ hp0 hp1 hr1 hr hΔ hc hvar
  refine ⟨retainedSet H' ρ ω, Finset.filter_subset _ _, hreg, ?_⟩
  have hnn : (0 : ℝ) ≤ (Fintype.card V : ℝ) := Nat.cast_nonneg _
  have hmul := mul_le_mul_of_nonneg_left hbad hnn
  calc (H'.card : ℝ) * (p * (1 - p) ^ (r * Δ)) - (Fintype.card V : ℝ) * δ
      ≤ (H'.card : ℝ) * (p * (1 - p) ^ (r * Δ))
          - (Fintype.card V : ℝ) * ((ℙ : Measure Ω) {ω | ∃ v : V,
              (degree (Hypergraph.residual H' (retainedSet H' ρ ω)) v : ℝ)
                ≤ (degree H' v : ℝ) * (1 - r * Δ * p) - c}).toReal := by linarith
    _ ≤ ((roundMatching (retainedSet H' ρ ω)).card : ℝ) := hcov

/-- **Good retention via FREEDMAN (STEP 3c).** Same as `exists_good_retention`, but the regularity
(clause a) is obtained from `exists_good_round_freedman_uncond` — the exponential Freedman bound on the
regularity-failure event — so it holds with a SMALL slack `c` (breaking the vacuous Chebyshev `c > √|V|Δ`).
The covering leftover `δ` is still supplied abstractly (via `hbad`). -/
theorem exists_good_retention_freedman {V : Type u} [Fintype V] [DecidableEq V]
    (H' : Finset (Finset V)) {p : ℝ} {r Δ : ℕ} {c δ : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hr1 : 1 ≤ r)
    (hr : IsUniform H' r) (hΔ : ∀ x, degree H' x ≤ Δ) (hΔ0 : 0 < Δ) (hc0 : 0 ≤ c)
    (hVpos : ∀ v : V, 0 < (∑ e ∈ H'.filter (fun f => v ∈ f),
          (((H'.filter (fun f => v ∈ f)).filter
            (fun e' => ¬ Disjoint (depNbhd H' e) (depNbhd H' e'))).card : ℝ)) * ((r : ℝ) * Δ * p))
    (hcond : (Fintype.card V : ℝ) * (2 * Real.exp (-c ^ 2 / (2 * ((Δ : ℝ) ^ 2 * ((r : ℝ) * Δ * p)
        + (Δ : ℝ) / 3 * c)))) < 1)
    (hbad : ∀ {Ω : Type u} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
        (ρ : BernoulliRetention (Ω := Ω) H' p),
        ((ℙ : Measure Ω) {ω | ∃ v : V,
              (degree (Hypergraph.residual H' (retainedSet H' ρ ω)) v : ℝ)
                ≤ (degree H' v : ℝ) * (1 - r * Δ * p) - c}).toReal ≤ δ) :
    ∃ R' : Finset (Finset V), R' ⊆ H'
      ∧ (∀ v : V, (degree H' v : ℝ) * (1 - r * Δ * p) - c
          < (degree (Hypergraph.residual H' R') v : ℝ))
      ∧ (H'.card : ℝ) * (p * (1 - p) ^ (r * Δ)) - (Fintype.card V : ℝ) * δ
          ≤ ((roundMatching R').card : ℝ) := by
  obtain ⟨Ω, mΩ, hProb, ⟨ρ⟩⟩ := exists_bernoulliRetention H' hp0 hp1
  letI := mΩ
  letI := hProb
  obtain ⟨ω, hreg, hcov⟩ := exists_good_round_freedman_uncond ρ hp0 hp1 hr1 hr hΔ hΔ0 hc0 hVpos hcond
  refine ⟨retainedSet H' ρ ω, Finset.filter_subset _ _, hreg, ?_⟩
  have hnn : (0 : ℝ) ≤ (Fintype.card V : ℝ) := Nat.cast_nonneg _
  have hmul := mul_le_mul_of_nonneg_left (hbad ρ) hnn
  calc (H'.card : ℝ) * (p * (1 - p) ^ (r * Δ)) - (Fintype.card V : ℝ) * δ
      ≤ (H'.card : ℝ) * (p * (1 - p) ^ (r * Δ))
          - (Fintype.card V : ℝ) * ((ℙ : Measure Ω) {ω | ∃ v : V,
              (degree (Hypergraph.residual H' (retainedSet H' ρ ω)) v : ℝ)
                ≤ (degree H' v : ℝ) * (1 - r * Δ * p) - c}).toReal := by linarith
    _ ≤ ((roundMatching (retainedSet H' ρ ω)).card : ℝ) := hcov

end Nibble
