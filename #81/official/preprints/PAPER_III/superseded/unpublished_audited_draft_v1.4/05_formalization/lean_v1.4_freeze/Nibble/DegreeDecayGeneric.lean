/-
# Nibble — generic covering algebra for degree-decay strategies

This file isolates the algebraic step from a residual-edge lower bound and a one-round covering
specification to a support-covering lower bound. The loss term is an abstract function `E`, so
specialized strategies do not force Lean to unfold large probability-tail expressions.
-/
import Nibble.Iteration
import Nibble.RegularMost
import Nibble.InvariantDegree
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Tactic.Positivity

open Hypergraph Finset

namespace Nibble

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Generic round covering floor from a residual-edge floor and a strategy covering spec. -/
theorem round_cover_lower_of_residual_edge
    (r Δ : ℕ) (p η : ℝ) (R : Finset (Finset V) → Finset (Finset V))
    (E : Finset (Finset V) → ℝ)
    (hRsub : ∀ H' : Finset (Finset V), R H' ⊆ H')
    (hspec : ∀ H' : Finset (Finset V), IsUniform H' r → (∀ x, degree H' x ≤ Δ) →
      (H'.card : ℝ) * (p * (1 - p) ^ (r * Δ)) - E H'
        ≤ ((roundMatching (R H')).card : ℝ))
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (H : Finset (Finset V)) (huni : IsUniform H r) (hdeg0 : ∀ x, degree H x ≤ Δ)
    (k : ℕ) (F : ℝ)
    (hres : ∃ Exc : Finset V, (Exc.card : ℝ) ≤ η * (Fintype.card V : ℝ) ∧
      ((Fintype.card V : ℝ) - (Exc.card : ℝ)) * F
        ≤ (r : ℝ) * ((nibbleResidual R H k).card : ℝ)) :
    ∃ Exc : Finset V, (Exc.card : ℝ) ≤ η * (Fintype.card V : ℝ) ∧
      ((Fintype.card V : ℝ) - (Exc.card : ℝ)) * F * (p * (1 - p) ^ (r * Δ))
        - (r : ℝ) * E (nibbleResidual R H k)
      ≤ ((support (roundMatching (R (nibbleResidual R H k)))).card : ℝ) := by
  obtain ⟨Exc, hExc, hedge⟩ := hres
  refine ⟨Exc, hExc, ?_⟩
  set Hk := nibbleResidual R H k with hHk
  have huni_k : IsUniform Hk r := nibbleResidual_uniform huni R k
  have hdeg_k : ∀ x, degree Hk x ≤ Δ := fun x => degree_nibbleResidual_le H k hdeg0 x
  have hsub : R Hk ⊆ Hk := hRsub Hk
  have hb : (Hk.card : ℝ) * (p * (1 - p) ^ (r * Δ)) - E Hk
      ≤ ((roundMatching (R Hk)).card : ℝ) := hspec Hk huni_k hdeg_k
  have hsupp : ((support (roundMatching (R Hk))).card : ℝ)
      = (r : ℝ) * ((roundMatching (R Hk)).card : ℝ) := by
    have hnat := matching_support_card huni_k (roundMatching_isMatching hsub)
    exact_mod_cast hnat
  have hP : (0 : ℝ) ≤ p * (1 - p) ^ (r * Δ) := mul_nonneg hp0 (pow_nonneg (by linarith) _)
  have hrpos : (0 : ℝ) ≤ (r : ℝ) := by positivity
  have hProd1 : ((Fintype.card V : ℝ) - (Exc.card : ℝ)) * F * (p * (1 - p) ^ (r * Δ))
      ≤ ((r : ℝ) * (Hk.card : ℝ)) * (p * (1 - p) ^ (r * Δ)) := by
    simpa [Hk] using mul_le_mul_of_nonneg_right hedge hP
  have hProd2 : (r : ℝ) * ((Hk.card : ℝ) * (p * (1 - p) ^ (r * Δ)) - E Hk)
      ≤ (r : ℝ) * ((roundMatching (R Hk)).card : ℝ) :=
    mul_le_mul_of_nonneg_left hb hrpos
  rw [hHk]
  rw [hsupp]
  nlinarith only [hProd1, hProd2]

end Nibble
