/-
# Nibble — one good round from the Freedman bad-event bound

Standalone, Mathlib-only. This is the STEP 3b user-facing bridge: it replaces the Chebyshev
`exists_good_round` input by the exponential all-vertices Freedman bound. The probabilistic selector is
unchanged (`exists_covering_avoiding_bad`); only the proof that the regularity-bad event has probability
less than one, and the resulting coverage penalty, change.
-/
import Nibble.OneRoundGood
import Nibble.RegularityBadFreedman
import Nibble.Prelude

open MeasureTheory ProbabilityTheory Finset Hypergraph
open scoped Classical

namespace Nibble

variable {V : Type*} [DecidableEq V] [Fintype V] {Ω : Type*} [MeasureSpace Ω]
  [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- **STEP 3b — one good round from Freedman.** If the exponential all-vertices Freedman bound is
`< 1`, there is one retained outcome whose residual degrees stay above
`deg(H,v) * (1 - rΔp) - c` and whose round matching loses only the Freedman bad-event penalty. -/
theorem exists_good_round_freedman {H : Finset (Finset V)} {p : ℝ} {r Δ : ℕ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hr1 : 1 ≤ r)
    (hr : IsUniform H r) (hΔ : ∀ x, degree H x ≤ Δ) (hΔ0 : 0 < Δ) {c : ℝ} (hc : 0 < c)
    (hVpos : ∀ v : V, 0 < degree H v →
      0 < (∑ e ∈ H.filter (fun f => v ∈ f),
          (((H.filter (fun f => v ∈ f)).filter
            (fun e' => ¬ Disjoint (depNbhd H e) (depNbhd H e'))).card : ℝ)) * ((r : ℝ) * Δ * p))
    (hsmall : (Fintype.card V : ℝ) * (2 * Real.exp (-c ^ 2 / (2 * ((Δ : ℝ) ^ 2 * ((r : ℝ) * Δ * p)
          + (Δ : ℝ) / 3 * c)))) < 1) :
    ∃ ω,
      (∀ v : V, (degree H v : ℝ) * (1 - r * Δ * p) - c
          < (degree (Hypergraph.residual H (retainedSet H ρ ω)) v : ℝ))
      ∧ (H.card : ℝ) * (p * (1 - p) ^ (r * Δ))
          - (Fintype.card V : ℝ) * ((Fintype.card V : ℝ)
              * (2 * Real.exp (-c ^ 2 / (2 * ((Δ : ℝ) ^ 2 * ((r : ℝ) * Δ * p)
                + (Δ : ℝ) / 3 * c)))))
        ≤ ((roundMatching (retainedSet H ρ ω)).card : ℝ) := by
  let Bad : Set Ω := {ω | ∃ v : V,
      (degree (Hypergraph.residual H (retainedSet H ρ ω)) v : ℝ)
        ≤ (degree H v : ℝ) * (1 - r * Δ * p) - c}
  let δ : ℝ := (Fintype.card V : ℝ)
      * (2 * Real.exp (-c ^ 2 / (2 * ((Δ : ℝ) ^ 2 * ((r : ℝ) * Δ * p)
        + (Δ : ℝ) / 3 * c))))
  have hBadMeas : MeasurableSet Bad := by
    simpa [Bad] using measurableSet_regularityBad (ρ := ρ) (r := r) (Δ := Δ) (c := c)
  have hBadδ : ((ℙ : Measure Ω) Bad).toReal ≤ δ := by
    simpa [Bad, δ] using regularityBad_freedman_active_prob_toReal_le ρ hp0 hp1 hr hΔ hΔ0 hc hVpos
  have hBad1 : ((ℙ : Measure Ω) Bad).toReal < 1 := lt_of_le_of_lt hBadδ hsmall
  obtain ⟨ω, hω_notin, hcov⟩ :=
    exists_covering_avoiding_bad ρ hp0 hp1 hr1 hr hΔ hBadMeas hBad1
  refine ⟨ω, fun v => ?_, ?_⟩
  · by_contra hle
    push_neg at hle
    exact hω_notin ⟨v, hle⟩
  · have hVnonneg : (0 : ℝ) ≤ (Fintype.card V : ℝ) := Nat.cast_nonneg _
    have hmul := mul_le_mul_of_nonneg_left hBadδ hVnonneg
    dsimp [δ] at hmul
    linarith only [hcov, hmul]

end Nibble
