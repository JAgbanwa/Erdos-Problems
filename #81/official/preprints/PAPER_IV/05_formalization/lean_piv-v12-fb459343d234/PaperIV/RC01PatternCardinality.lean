import PaperIV.RC01CanonicalProfile
import PaperIV.RC01ResidualTransferClosure

/-!
# RC01: exact cardinality bound for canonical profiles

Canonical K3/K4 slots are literally 3/4-subsets of the regularity classes.
Thus the whole mixed family has size at most `choose k 3 + choose k 4`, and
every active subfamily inherits the same bound.
-/

namespace PaperIV.RC01PatternCardinality

open Finset
open MixedRounding
open PaperIV.RegularityFormat
open PaperIV.RC01CandidatePool
open PaperIV.RC01CanonicalSlots
open PaperIV.RC01K3Pool
open PaperIV.RC01MixedPatterns
open PaperIV.RC01CanonicalProfile
open PaperIV.RC01ResidualCoverage
open PaperIV.RC01ResidualTransferClosure

variable {α : Type*} [Fintype α] [DecidableEq α]
variable {G : SimpleGraph α} [DecidableRel G.Adj]

theorem goodK3Slots_subset_powersetCard {δ : ℚ} (R : EqualRegularity G δ) :
    goodK3Slots R ⊆ R.parts.powersetCard 3 := by
  intro S hS
  rw [Finset.mem_powersetCard]
  refine ⟨?_, card_goodK3Slot R hS⟩
  intro Q hQS
  rw [← (canonicalTripleOf_spec R hS).2] at hQS
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hQS
  exact canonicalTripleOf_mem_parts R hS i

theorem goodK4Slots_subset_powersetCard {δ : ℚ} (R : EqualRegularity G δ) :
    goodK4Slots R ⊆ R.parts.powersetCard 4 := by
  intro S hS
  rw [Finset.mem_powersetCard]
  refine ⟨?_, card_goodK4Slot R hS⟩
  intro Q hQS
  rw [← (canonicalTuple_spec R hS).2] at hQS
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hQS
  exact (mem_goodK4Tuples.1 (canonicalTuple_spec R hS).1).1 i

theorem card_mixedPatterns_le_choose {δ : ℚ} (R : EqualRegularity G δ) :
    (mixedPatterns R).card ≤ R.parts.card.choose 3 + R.parts.card.choose 4 := by
  classical
  calc
    (mixedPatterns R).card
        ≤ ((goodK3Slots R).image Sum.inl).card +
            ((goodK4Slots R).image Sum.inr).card := by
          rw [mixedPatterns]
          exact Finset.card_union_le _ _
    _ = (goodK3Slots R).card + (goodK4Slots R).card := by
          rw [Finset.card_image_of_injective _ Sum.inl_injective,
            Finset.card_image_of_injective _ Sum.inr_injective]
    _ ≤ (R.parts.powersetCard 3).card + (R.parts.powersetCard 4).card :=
          Nat.add_le_add
            (Finset.card_le_card (goodK3Slots_subset_powersetCard R))
            (Finset.card_le_card (goodK4Slots_subset_powersetCard R))
    _ = R.parts.card.choose 3 + R.parts.card.choose 4 := by
          rw [Finset.card_powersetCard, Finset.card_powersetCard]

theorem card_denseActiveProfiles_le_mixedPatterns {δ : ℚ}
    (R : EqualRegularity G δ) (x : FracPacking G) (d θ : ℚ) :
    (denseActiveProfiles R x d θ).card ≤ (mixedPatterns R).card := by
  classical
  calc
    (denseActiveProfiles R x d θ).card
        ≤ (denseHeavyPatterns R (PaperIV.MixedRoundingAdapter.toFarFrac x) d θ).card := by
          exact Finset.card_image_le
    _ ≤ (mixedPatterns R).card :=
          Finset.card_le_card (denseHeavyPatterns_subset R _ d θ)

theorem card_denseActiveProfiles_le_choose {δ : ℚ}
    (R : EqualRegularity G δ) (x : FracPacking G) (d θ : ℚ) :
    (denseActiveProfiles R x d θ).card ≤
      R.parts.card.choose 3 + R.parts.card.choose 4 :=
  (card_denseActiveProfiles_le_mixedPatterns R x d θ).trans
    (card_mixedPatterns_le_choose R)

/-- Coarse polynomial bound for the whole canonical mixed family. -/
theorem card_mixedPatterns_le_two_mul_fourth {δ : ℚ}
    (R : EqualRegularity G δ) (hk : 1 ≤ R.parts.card) :
    (mixedPatterns R).card ≤ 2 * R.parts.card ^ 4 := by
  have h3 : R.parts.card.choose 3 ≤ R.parts.card ^ 3 :=
    Nat.choose_le_pow _ _
  have h34 : R.parts.card ^ 3 ≤ R.parts.card ^ 4 := by
    calc
      R.parts.card ^ 3 = R.parts.card ^ 3 * 1 := by omega
      _ ≤ R.parts.card ^ 3 * R.parts.card := Nat.mul_le_mul_left _ hk
      _ = R.parts.card ^ 4 := by ring
  have h4 : R.parts.card.choose 4 ≤ R.parts.card ^ 4 :=
    Nat.choose_le_pow _ _
  exact (card_mixedPatterns_le_choose R).trans (by nlinarith)

/-- Coarse polynomial form used by the global parameter schedule. -/
theorem card_denseActiveProfiles_le_two_mul_fourth {δ : ℚ}
    (R : EqualRegularity G δ) (x : FracPacking G) (d θ : ℚ)
    (hk : 1 ≤ R.parts.card) :
    (denseActiveProfiles R x d θ).card ≤ 2 * R.parts.card ^ 4 := by
  exact (card_denseActiveProfiles_le_mixedPatterns R x d θ).trans
    (card_mixedPatterns_le_two_mul_fourth R hk)

end PaperIV.RC01PatternCardinality
