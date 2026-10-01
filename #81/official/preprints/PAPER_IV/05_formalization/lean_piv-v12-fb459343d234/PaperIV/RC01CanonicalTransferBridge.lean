import PaperIV.RC01CanonicalValueAccounting
import PaperIV.PatternTransfer
import PaperIV.MixedRoundingAdapter

/-!
# RC01: canonical value to the cleaned transferred objective

This is the downstream companion of the residual-coverage task.  It does not
classify any residual item.  Instead it proves that, once a residual bound is
available, the exact canonical value controls the transferred `psiT` objective
consumed by the already formalized cleaned gate.
-/

namespace PaperIV.RC01CanonicalTransferBridge

open Finset
open MixedRounding
open PaperIV.RegularityFormat
open PaperIV.PartitionBridge
open PaperIV.PatternTransfer
open PaperIV.RC01CleanFiber
open PaperIV.RC01CleanedGate
open PaperIV.RC01MixedPatterns
open PaperIV.RC01CanonicalProfile
open PaperIV.RC01CanonicalFiberProfile
open PaperIV.RC01CanonicalValueAccounting
open PaperIV.RC01PatternCapacity

variable {V P : Type*} [Fintype V] [DecidableEq V]
  [Fintype P] [DecidableEq P]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A literal profile fibre carries no more fractional mass than the complete
transferred profile mass `psiT`: `psiT` may additionally contain collapsed
non-transversal items, and those terms are nonnegative. -/
theorem rawMass_profileFiber_le_psiT (x : FracPacking G) (part : V → P)
    (H : Finset P) :
    rawMass (PaperIV.MixedRoundingAdapter.toFarFrac x)
      (profileFiber G part) H ≤ psiT x part H := by
  classical
  rw [rawMass, psiT]
  have heq :
      (∑ K ∈ profileFiber G part H,
          (PaperIV.MixedRoundingAdapter.toFarFrac x).weight K) =
        ∑ K ∈ profileFiber G part H,
          (if K.image part = H then x.weight K else 0) := by
    refine Finset.sum_congr rfl ?_
    intro K hK
    rw [if_pos (mem_profileFiber.1 hK).2.1]
    rfl
  rw [heq]
  refine Finset.sum_le_sum_of_subset_of_nonneg
    (profileFiber_subset_items (G := G) part H) ?_
  intro K _ _
  by_cases hKH : K.image part = H
  · rw [if_pos hKH]
    exact x.weight_nonneg K
  · rw [if_neg hKH]

/-- Canonical tagged raw mass is bounded by the corresponding transferred
untagged profile mass. -/
theorem rawMass_mixedFiber_le_psiT {δ : ℚ} (R : EqualRegularity G δ)
    (x : FracPacking G) {σ : MixedPattern V}
    (hσ : σ ∈ mixedPatterns R) :
    rawMass (PaperIV.MixedRoundingAdapter.toFarFrac x) (mixedFiber R) σ ≤
      psiT x (partOf R) (profileOfMixed σ) := by
  rw [rawMass_mixedFiber_eq R (PaperIV.MixedRoundingAdapter.toFarFrac x) hσ]
  exact rawMass_profileFiber_le_psiT x (partOf R) (profileOfMixed σ)

/-- Every selected canonical K3/K4 profile has nonnegative reward. -/
theorem patternGain_profileOfMixed_nonneg {δ : ℚ} (R : EqualRegularity G δ)
    {σ : MixedPattern V} (hσ : σ ∈ mixedPatterns R) :
    0 ≤ patternGain (profileOfMixed σ) := by
  rw [patternGain, card_profileOfMixed R hσ]
  split <;> norm_num [Nat.choose]

/-- The literal canonical value is bounded by the transferred objective used
by the clean physical gate. -/
theorem canonicalValue_le_transferred {δ : ℚ} (R : EqualRegularity G δ)
    (x : FracPacking G) (Active : Finset (MixedPattern V))
    (hActive : Active ⊆ mixedPatterns R) :
    canonicalValue R (PaperIV.MixedRoundingAdapter.toFarFrac x) Active ≤
      ∑ σ ∈ Active,
        patternGain (profileOfMixed σ) *
          psiT x (partOf R) (profileOfMixed σ) := by
  rw [canonicalValue_eq_sum_rawMass R
    (PaperIV.MixedRoundingAdapter.toFarFrac x) Active hActive]
  refine Finset.sum_le_sum ?_
  intro σ hσ
  exact mul_le_mul_of_nonneg_left
    (rawMass_mixedFiber_le_psiT R x (hActive hσ))
    (patternGain_profileOfMixed_nonneg R (hActive hσ))

/-- **Residual-to-transfer bridge.**  Any future upper bound `Δ` on the one
explicit off-pool residual immediately yields the retained transferred-value
inequality required downstream. -/
theorem value_sub_residual_le_transferred {δ : ℚ}
    (R : EqualRegularity G δ) (x : FracPacking G)
    (Active : Finset (MixedPattern V)) (hActive : Active ⊆ mixedPatterns R)
    (Δ : ℚ)
    (hoff : offCanonicalValue R (PaperIV.MixedRoundingAdapter.toFarFrac x) Active ≤ Δ) :
    x.value - Δ ≤
      ∑ σ ∈ Active,
        patternGain (profileOfMixed σ) *
          psiT x (partOf R) (profileOfMixed σ) := by
  have hsplit := value_eq_canonical_add_off R
    (PaperIV.MixedRoundingAdapter.toFarFrac x) Active hActive
  rw [PaperIV.MixedRoundingAdapter.value_toFarFrac] at hsplit
  have hcan : x.value - Δ ≤
      canonicalValue R (PaperIV.MixedRoundingAdapter.toFarFrac x) Active := by
    linarith
  exact hcan.trans (canonicalValue_le_transferred R x Active hActive)

end PaperIV.RC01CanonicalTransferBridge
