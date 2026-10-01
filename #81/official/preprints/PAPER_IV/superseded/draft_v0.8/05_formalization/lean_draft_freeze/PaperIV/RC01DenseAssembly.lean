import PaperIV.RC01ResidualTransferClosure
import PaperIV.RC01GlobalSchedule

/-!
# RC01: deterministic assembly after the dense physical gate

This module closes the algebra between the dense residual theorem and the
physical packing returned by the cleaned gate.  The only remaining input is
the literal packing inequality produced by that gate; all residual and
multiplicative losses are charged here once.
-/

namespace PaperIV.RC01DenseAssembly

open Finset
open MixedRounding
open PaperIV.PatternTransfer
open PaperIV.PartitionBridge
open PaperIV.RegularityFormat
open PaperIV.RC01MixedPatterns
open PaperIV.RC01CleanedGate
open PaperIV.RC01ResidualCoverage
open PaperIV.RC01ResidualTransferClosure
open PaperIV.RC01GlobalSchedule

/-- Pure algebraic assembly.  If `S` is the retained transferred objective,
the residual costs `Delta`, and the physical gate retains `(1-u-v)S` up to
`zeta n^2`, then the total loss is bounded by the displayed sum. -/
theorem loss_le_of_retained_round {n : ℕ} {xval gain Delta S u v zeta : ℚ}
    (huv : 0 ≤ u + v)
    (hres : xval - Delta ≤ S)
    (hS : S ≤ (5 / 6 : ℚ) * (n : ℚ) ^ 2)
    (hround : (1 - u - v) * S - gain ≤ zeta * (n : ℚ) ^ 2) :
    xval - gain ≤ Delta + (zeta + (5 / 6) * (u + v)) * (n : ℚ) ^ 2 := by
  have hmul : (u + v) * S ≤ (u + v) * ((5 / 6 : ℚ) * (n : ℚ) ^ 2) :=
    mul_le_mul_of_nonneg_left hS huv
  have hres' : xval - Delta - S ≤ 0 := by linarith
  calc
    xval - gain = (xval - Delta - S) + ((1 - u - v) * S - gain)
        + Delta + (u + v) * S := by ring
    _ ≤ 0 + zeta * (n : ℚ) ^ 2 + Delta
        + (u + v) * ((5 / 6 : ℚ) * (n : ℚ) ^ 2) := by gcongr
    _ = Delta + (zeta + (5 / 6) * (u + v)) * (n : ℚ) ^ 2 := by ring

set_option maxHeartbeats 800000

/-- The end-to-end deterministic RC01 inequality on the literal dense active
profiles.  No residual, tag-forgetting, or objective-size hypothesis remains:
those are discharged by the preceding modules. -/
theorem packing_loss_le_of_dense_profile_round {δ : ℚ} {n : ℕ}
    {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (R : EqualRegularity G δ) (x : FracPacking G) (P : Packing G)
    (d θ u v zeta : ℚ) (hδ : 0 ≤ δ) (hd : 0 ≤ d) (hθ : 0 ≤ θ)
    {k₀ : ℕ} (hk₀ : 0 < k₀) (hk : k₀ ≤ R.parts.card)
    (huv : 0 ≤ u + v)
    (hround :
      (1 - u - v) *
          (∑ H ∈ denseActiveProfiles R x d θ,
            patternGain H * psiT x (partOf R) H) - (P.gain : ℚ)
        ≤ zeta * (n : ℚ) ^ 2) :
    x.value - (P.gain : ℚ) ≤
      5 * ((3 * δ + 1 / (k₀ : ℚ) + d) * (n : ℚ) ^ 2)
        + 5 * (((mixedPatterns R).card : ℚ) * θ)
        + (zeta + (5 / 6) * (u + v)) * (n : ℚ) ^ 2 := by
  let Delta : ℚ :=
    5 * ((3 * δ + 1 / (k₀ : ℚ) + d) * (n : ℚ) ^ 2)
      + 5 * (((mixedPatterns R).card : ℚ) * θ)
  let S : ℚ :=
    ∑ H ∈ denseActiveProfiles R x d θ,
      patternGain H * psiT x (partOf R) H
  have hres : x.value - Delta ≤ S := by
    simpa [Delta, S, Fintype.card_fin] using
      (value_sub_dense_regularity_budget_le_profiles hδ R x d θ hd hθ hk₀ hk)
  have hS : S ≤ (5 / 6 : ℚ) * (n : ℚ) ^ 2 := by
    simpa [S] using denseProfileValue_le R x d θ
  exact loss_le_of_retained_round huv hres hS (by simpa [S] using hround)

/-- The deterministic dense assembly fits in half of the requested error once
the six global accounts have been scheduled.  This is the final arithmetic
wrapper before choosing uniform parameters and invoking the physical gates. -/
theorem packing_loss_le_half_of_dense_profile_round {ε δ : ℚ} {n : ℕ}
    {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (R : EqualRegularity G δ) (x : FracPacking G) (P : Packing G)
    (d θ u v zeta light : ℚ) (hε : 0 < ε)
    (hδ : 0 ≤ δ) (hd : 0 ≤ d) (hθ : 0 ≤ θ)
    {k₀ : ℕ} (hk₀ : 0 < k₀) (hk : k₀ ≤ R.parts.card)
    (huv : 0 ≤ u + v)
    (hδBudget : 15 * δ ≤ ε / 100)
    (hdBudget : 5 * d ≤ ε / 10)
    (hzetaBudget : zeta ≤ ε / 10)
    (huvBudget : (5 / 6 : ℚ) * (u + v) ≤ ε / 10)
    (hkBudget : 5 / (k₀ : ℚ) ≤ ε / 10)
    (hlightBudget : light ≤ ε / 20)
    (hlight : 5 * ((mixedPatterns R).card : ℚ) * θ ≤
      light * (n : ℚ) ^ 2)
    (hround :
      (1 - u - v) *
          (∑ H ∈ denseActiveProfiles R x d θ,
            patternGain H * psiT x (partOf R) H) - (P.gain : ℚ)
        ≤ zeta * (n : ℚ) ^ 2) :
    x.value - (P.gain : ℚ) ≤ (ε / 2) * (n : ℚ) ^ 2 := by
  have hraw := packing_loss_le_of_dense_profile_round R x P d θ u v zeta
    hδ hd hθ hk₀ hk huv hround
  have hbudget := dense_assembly_budget_le_half hε hδBudget hdBudget
    hzetaBudget huvBudget hkBudget hlightBudget hlight
  calc
    x.value - (P.gain : ℚ) ≤
        5 * ((3 * δ + 1 / (k₀ : ℚ) + d) * (n : ℚ) ^ 2)
          + 5 * (((mixedPatterns R).card : ℚ) * θ)
          + (zeta + (5 / 6) * (u + v)) * (n : ℚ) ^ 2 := hraw
    _ = (15 * δ + 5 * d + zeta + (5 / 6 : ℚ) * (u + v) +
          5 / (k₀ : ℚ)) * (n : ℚ) ^ 2
          + 5 * ((mixedPatterns R).card : ℚ) * θ := by ring
    _ ≤ (ε / 2) * (n : ℚ) ^ 2 := hbudget

set_option maxHeartbeats 200000

end PaperIV.RC01DenseAssembly
