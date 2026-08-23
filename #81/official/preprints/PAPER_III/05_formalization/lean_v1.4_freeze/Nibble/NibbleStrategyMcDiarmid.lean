/-
# Nibble — count-sharp McDiarmid retention strategy

Strategy layer for the count-sharp McDiarmid good-retention bridge. This mirrors
`NibbleStrategyFreedman`, but the smallness hypothesis is the true `neighborCoef` tail sum.
-/
import Nibble.GoodRetentionMcDiarmid
import Nibble.Iteration

open MeasureTheory ProbabilityTheory Finset Hypergraph
open scoped Classical ENNReal

namespace Nibble

variable {V : Type u} [Fintype V] [DecidableEq V]

noncomputable def mcdiarmidNeighborPenalty (V : Type u) [Fintype V]
    (H : Finset (Finset V)) (c : ℝ) : ℝ :=
  (Fintype.card V : ℝ) *
    ((∑ v : V, ENNReal.ofReal
      (2 * Real.exp (-c ^ 2 / (2 * mcdiarmidNeighborCoeffSum H v)))).toReal)

/-- The count-sharp McDiarmid retention strategy. -/
noncomputable def nibbleStrategyMcDiarmid (r Δ : ℕ) (p c : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hr1 : 1 ≤ r) (hc0 : 0 ≤ c)
    (hsmall : ∀ H' : Finset (Finset V), IsUniform H' r → (∀ x, degree H' x ≤ Δ) →
      (∑ v : V, ENNReal.ofReal
        (2 * Real.exp (-c ^ 2 / (2 * mcdiarmidNeighborCoeffSum H' v)))) < 1) :
    Finset (Finset V) → Finset (Finset V) :=
  fun H' =>
    if h : IsUniform H' r ∧ (∀ x, degree H' x ≤ Δ)
    then (exists_good_retention_mcd_neighborCoef' H' hp0 hp1 hr1 h.1 h.2 hc0
      (hsmall H' h.1 h.2)).choose
    else H'

theorem nibbleStrategyMcDiarmid_subset (r Δ : ℕ) (p c : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hr1 : 1 ≤ r) (hc0 : 0 ≤ c)
    (hsmall : ∀ H' : Finset (Finset V), IsUniform H' r → (∀ x, degree H' x ≤ Δ) →
      (∑ v : V, ENNReal.ofReal
        (2 * Real.exp (-c ^ 2 / (2 * mcdiarmidNeighborCoeffSum H' v)))) < 1)
    (H' : Finset (Finset V)) :
    nibbleStrategyMcDiarmid r Δ p c hp0 hp1 hr1 hc0 hsmall H' ⊆ H' := by
  rw [nibbleStrategyMcDiarmid]
  by_cases h : IsUniform H' r ∧ (∀ x, degree H' x ≤ Δ)
  · rw [dif_pos h]
    exact (exists_good_retention_mcd_neighborCoef' H' hp0 hp1 hr1 h.1 h.2 hc0
      (hsmall H' h.1 h.2)).choose_spec.1
  · rw [dif_neg h]

theorem nibbleStrategyMcDiarmid_spec (r Δ : ℕ) (p c : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hr1 : 1 ≤ r) (hc0 : 0 ≤ c)
    (hsmall : ∀ H' : Finset (Finset V), IsUniform H' r → (∀ x, degree H' x ≤ Δ) →
      (∑ v : V, ENNReal.ofReal
        (2 * Real.exp (-c ^ 2 / (2 * mcdiarmidNeighborCoeffSum H' v)))) < 1)
    (H' : Finset (Finset V)) (huni : IsUniform H' r) (hdeg : ∀ x, degree H' x ≤ Δ) :
    (∀ v : V, (degree H' v : ℝ) * (1 - r * Δ * p) - c
          < (degree (Hypergraph.residual H'
          (nibbleStrategyMcDiarmid r Δ p c hp0 hp1 hr1 hc0 hsmall H')) v : ℝ))
      ∧ (H'.card : ℝ) * (p * (1 - p) ^ (r * Δ))
          - (Fintype.card V : ℝ) *
              ((∑ v : V, ENNReal.ofReal
                (2 * Real.exp (-c ^ 2 / (2 * mcdiarmidNeighborCoeffSum H' v)))).toReal)
          ≤ ((roundMatching
            (nibbleStrategyMcDiarmid r Δ p c hp0 hp1 hr1 hc0 hsmall H')).card : ℝ) := by
  have hkey : nibbleStrategyMcDiarmid r Δ p c hp0 hp1 hr1 hc0 hsmall H'
      = (exists_good_retention_mcd_neighborCoef' H' hp0 hp1 hr1 huni hdeg hc0
          (hsmall H' huni hdeg)).choose := by
    rw [nibbleStrategyMcDiarmid]
    exact dif_pos ⟨huni, hdeg⟩
  rw [hkey]
  exact ⟨
    (exists_good_retention_mcd_neighborCoef' H' hp0 hp1 hr1 huni hdeg hc0
      (hsmall H' huni hdeg)).choose_spec.2.1,
    (exists_good_retention_mcd_neighborCoef' H' hp0 hp1 hr1 huni hdeg hc0
      (hsmall H' huni hdeg)).choose_spec.2.2⟩

end Nibble
