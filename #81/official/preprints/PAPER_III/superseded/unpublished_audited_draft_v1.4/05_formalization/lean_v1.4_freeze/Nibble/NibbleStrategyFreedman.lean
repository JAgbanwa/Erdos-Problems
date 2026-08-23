/-
# Nibble — Freedman retention strategy

Parallel to `NibbleStrategy.lean`, but using the exponential Freedman good-retention bridge instead of
the old Chebyshev bridge. The extra hypotheses are deliberately quantified over every valid residual
input `H'`, because the iteration applies the strategy to changing residual hypergraphs.
-/
import Nibble.GoodRetentionFreedman
import Nibble.Iteration

open MeasureTheory ProbabilityTheory Finset Hypergraph
open scoped Classical

namespace Nibble

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The Freedman retention strategy: choose the good retained subset when the input is valid and
Freedman-small; otherwise leave the input unchanged. -/
noncomputable def nibbleStrategyFreedman (r Δ : ℕ) (p c : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hr1 : 1 ≤ r) (hΔ0 : 0 < Δ) (hc : 0 < c)
    (hVpos : ∀ H' : Finset (Finset V), IsUniform H' r → (∀ x, degree H' x ≤ Δ) →
      ∀ v : V, 0 < degree H' v →
        0 < (∑ e ∈ H'.filter (fun f => v ∈ f),
          (((H'.filter (fun f => v ∈ f)).filter
            (fun e' => ¬ Disjoint (depNbhd H' e) (depNbhd H' e'))).card : ℝ)) * ((r : ℝ) * Δ * p))
    (hsmall : ∀ H' : Finset (Finset V), IsUniform H' r → (∀ x, degree H' x ≤ Δ) →
      (Fintype.card V : ℝ) * (2 * Real.exp (-c ^ 2 / (2 * ((Δ : ℝ) ^ 2 * ((r : ℝ) * Δ * p)
        + (Δ : ℝ) / 3 * c)))) < 1) :
    Finset (Finset V) → Finset (Finset V) :=
  fun H' =>
    if h : IsUniform H' r ∧ (∀ x, degree H' x ≤ Δ)
    then (exists_good_retention_freedman' H' hp0 hp1 hr1 h.1 h.2 hΔ0 hc
      (hVpos H' h.1 h.2) (hsmall H' h.1 h.2)).choose
    else H'

/-- **Freedman `hR`** — the strategy keeps edges inside its input. -/
theorem nibbleStrategyFreedman_subset (r Δ : ℕ) (p c : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hr1 : 1 ≤ r) (hΔ0 : 0 < Δ) (hc : 0 < c)
    (hVpos : ∀ H' : Finset (Finset V), IsUniform H' r → (∀ x, degree H' x ≤ Δ) →
      ∀ v : V, 0 < degree H' v →
        0 < (∑ e ∈ H'.filter (fun f => v ∈ f),
          (((H'.filter (fun f => v ∈ f)).filter
            (fun e' => ¬ Disjoint (depNbhd H' e) (depNbhd H' e'))).card : ℝ)) * ((r : ℝ) * Δ * p))
    (hsmall : ∀ H' : Finset (Finset V), IsUniform H' r → (∀ x, degree H' x ≤ Δ) →
      (Fintype.card V : ℝ) * (2 * Real.exp (-c ^ 2 / (2 * ((Δ : ℝ) ^ 2 * ((r : ℝ) * Δ * p)
        + (Δ : ℝ) / 3 * c)))) < 1)
    (H' : Finset (Finset V)) :
    nibbleStrategyFreedman r Δ p c hp0 hp1 hr1 hΔ0 hc hVpos hsmall H' ⊆ H' := by
  rw [nibbleStrategyFreedman]
  by_cases h : IsUniform H' r ∧ (∀ x, degree H' x ≤ Δ)
  · rw [dif_pos h]
    exact (exists_good_retention_freedman' H' hp0 hp1 hr1 h.1 h.2 hΔ0 hc
      (hVpos H' h.1 h.2) (hsmall H' h.1 h.2)).choose_spec.1
  · rw [dif_neg h]

/-- **Freedman strategy spec** — on a valid hypergraph, the strategy preserves the lower
near-regularity threshold and covers with the exponential Freedman penalty. -/
theorem nibbleStrategyFreedman_spec (r Δ : ℕ) (p c : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hr1 : 1 ≤ r) (hΔ0 : 0 < Δ) (hc : 0 < c)
    (hVpos : ∀ H' : Finset (Finset V), IsUniform H' r → (∀ x, degree H' x ≤ Δ) →
      ∀ v : V, 0 < degree H' v →
        0 < (∑ e ∈ H'.filter (fun f => v ∈ f),
          (((H'.filter (fun f => v ∈ f)).filter
            (fun e' => ¬ Disjoint (depNbhd H' e) (depNbhd H' e'))).card : ℝ)) * ((r : ℝ) * Δ * p))
    (hsmall : ∀ H' : Finset (Finset V), IsUniform H' r → (∀ x, degree H' x ≤ Δ) →
      (Fintype.card V : ℝ) * (2 * Real.exp (-c ^ 2 / (2 * ((Δ : ℝ) ^ 2 * ((r : ℝ) * Δ * p)
        + (Δ : ℝ) / 3 * c)))) < 1)
    (H' : Finset (Finset V)) (huni : IsUniform H' r) (hdeg : ∀ x, degree H' x ≤ Δ) :
    (∀ v : V, (degree H' v : ℝ) * (1 - r * Δ * p) - c
          < (degree (Hypergraph.residual H'
          (nibbleStrategyFreedman r Δ p c hp0 hp1 hr1 hΔ0 hc hVpos hsmall H')) v : ℝ))
      ∧ (H'.card : ℝ) * (p * (1 - p) ^ (r * Δ))
          - (Fintype.card V : ℝ) * ((Fintype.card V : ℝ)
              * (2 * Real.exp (-c ^ 2 / (2 * ((Δ : ℝ) ^ 2 * ((r : ℝ) * Δ * p)
                + (Δ : ℝ) / 3 * c)))))
          ≤ ((roundMatching
            (nibbleStrategyFreedman r Δ p c hp0 hp1 hr1 hΔ0 hc hVpos hsmall H')).card : ℝ) := by
  have hkey : nibbleStrategyFreedman r Δ p c hp0 hp1 hr1 hΔ0 hc hVpos hsmall H'
      = (exists_good_retention_freedman' H' hp0 hp1 hr1 huni hdeg hΔ0 hc
          (hVpos H' huni hdeg) (hsmall H' huni hdeg)).choose := by
    rw [nibbleStrategyFreedman]
    exact dif_pos ⟨huni, hdeg⟩
  rw [hkey]
  exact ⟨
    (exists_good_retention_freedman' H' hp0 hp1 hr1 huni hdeg hΔ0 hc
      (hVpos H' huni hdeg) (hsmall H' huni hdeg)).choose_spec.2.1,
    (exists_good_retention_freedman' H' hp0 hp1 hr1 huni hdeg hΔ0 hc
      (hVpos H' huni hdeg) (hsmall H' huni hdeg)).choose_spec.2.2⟩

end Nibble
