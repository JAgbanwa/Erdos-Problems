import PaperIV.RC01PatternCardinality
import PaperIV.RC01GlobalBudget

/-!
# RC01: global schedule adapters

These lemmas turn the exact polynomial profile bound into the codegree and
light-profile inequalities consumed by the physical gate and close the final
deterministic error ledger after `RC01DenseAssembly`.
-/

namespace PaperIV.RC01GlobalSchedule

open MixedRounding
open PaperIV.RegularityFormat
open PaperIV.RC01MixedPatterns
open PaperIV.RC01ResidualTransferClosure
open PaperIV.RC01PatternCardinality
open PaperIV.RC01GlobalBudget

variable {α : Type*} [Fintype α] [DecidableEq α]
variable {G : SimpleGraph α} [DecidableRel G.Adj]

/-- The polynomial cardinal bound implies the codegree hypothesis used by the
cleaned physical gate.  The scale inequality is deliberately exposed: it is
the sole large-cluster numerical obligation. -/
theorem dense_codegree_threshold_of_scale {δ d θ gamma : ℚ}
    (R : EqualRegularity G δ) (x : FracPacking G)
    (hk : 1 ≤ R.parts.card)
    (hc3 : 0 ≤ d ^ 3 - 3 * δ) (hc4 : 0 ≤ d ^ 6 - 6 * δ)
    (hscale :
      (2 * (R.parts.card : ℚ) ^ 4) *
          ((d ^ 3 - 3 * δ) + (d ^ 6 - 6 * δ))
        ≤ gamma * (d ^ 3 - 3 * δ) * (d ^ 6 - 6 * δ) * (R.size : ℚ)) :
    ((denseActiveProfiles R x d θ).card : ℚ) * (d ^ 6 - 6 * δ) +
        ((denseActiveProfiles R x d θ).card : ℚ) * (d ^ 3 - 3 * δ)
      ≤ gamma * (d ^ 3 - 3 * δ) * (d ^ 6 - 6 * δ) * (R.size : ℚ) := by
  have hcardNat := card_denseActiveProfiles_le_two_mul_fourth R x d θ hk
  have hcard : ((denseActiveProfiles R x d θ).card : ℚ) ≤
      2 * (R.parts.card : ℚ) ^ 4 := by
    exact_mod_cast hcardNat
  calc
    ((denseActiveProfiles R x d θ).card : ℚ) * (d ^ 6 - 6 * δ) +
          ((denseActiveProfiles R x d θ).card : ℚ) * (d ^ 3 - 3 * δ)
        = ((denseActiveProfiles R x d θ).card : ℚ) *
            ((d ^ 3 - 3 * δ) + (d ^ 6 - 6 * δ)) := by ring
    _ ≤ (2 * (R.parts.card : ℚ) ^ 4) *
          ((d ^ 3 - 3 * δ) + (d ^ 6 - 6 * δ)) := by
        exact mul_le_mul_of_nonneg_right hcard (add_nonneg hc3 hc4)
    _ ≤ _ := hscale

/-- A single scale inequality controls the entire discarded light-profile
account, independently of how many canonical profiles are active. -/
theorem five_mul_mixedPatterns_theta_le {δ θ light n : ℚ}
    (R : EqualRegularity G δ) (hk : 1 ≤ R.parts.card)
    (hθ : 0 ≤ θ)
    (hscale : 10 * (R.parts.card : ℚ) ^ 4 * θ ≤ light * n ^ 2) :
    5 * ((mixedPatterns R).card : ℚ) * θ ≤ light * n ^ 2 := by
  have hcardNat := card_mixedPatterns_le_two_mul_fourth R hk
  have hcard : ((mixedPatterns R).card : ℚ) ≤
      2 * (R.parts.card : ℚ) ^ 4 := by
    exact_mod_cast hcardNat
  have hmul := mul_le_mul_of_nonneg_right hcard hθ
  nlinarith

/-- Final deterministic budget in the exact shape returned by
`packing_loss_le_of_dense_profile_round`. -/
theorem dense_assembly_budget_le_half {ε δ d ζ u v invk light n lightTerm : ℚ}
    (hε : 0 < ε)
    (hδ : 15 * δ ≤ ε / 100)
    (hd : 5 * d ≤ ε / 10)
    (hζ : ζ ≤ ε / 10)
    (huv : (5 / 6 : ℚ) * (u + v) ≤ ε / 10)
    (hinvk : invk ≤ ε / 10)
    (hlight : light ≤ ε / 20)
    (hlightTerm : lightTerm ≤ light * n ^ 2) :
    (15 * δ + 5 * d + ζ + (5 / 6 : ℚ) * (u + v) + invk) * n ^ 2 +
        lightTerm
      ≤ (ε / 2) * n ^ 2 := by
  have hledger := six_accounts_le_half hε hδ hd hζ huv hinvk hlight
  have hn2 : 0 ≤ n ^ 2 := sq_nonneg n
  calc
    (15 * δ + 5 * d + ζ + (5 / 6 : ℚ) * (u + v) + invk) * n ^ 2 +
          lightTerm
        ≤ (15 * δ + 5 * d + ζ + (5 / 6 : ℚ) * (u + v) + invk + light) *
            n ^ 2 := by nlinarith
    _ ≤ (ε / 2) * n ^ 2 := mul_le_mul_of_nonneg_right hledger hn2

end PaperIV.RC01GlobalSchedule
