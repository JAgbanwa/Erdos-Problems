import PaperIV.RC01ResidualCoverage
import PaperIV.RC01CanonicalTransferBridge
import PaperIV.SpreadValueTransfer

/-!
# RC01: residual coverage closed into the transferred objective

This module composes the literal geometric classification of
`RC01ResidualCoverage` with the algebraic transfer bridge.  It is deliberately
small: no rounding hypothesis is introduced here.
-/

namespace PaperIV.RC01ResidualTransferClosure

open Finset
open MixedRounding
open PaperIV.RegularityFormat
open PaperIV.PartitionBridge
open PaperIV.PatternTransfer
open PaperIV.RC01MixedPatterns
open PaperIV.RC01CandidatePool
open PaperIV.RC01CanonicalSlots
open PaperIV.RC01K3Pool
open PaperIV.RC01CanonicalProfile
open PaperIV.RC01CanonicalFiberProfile
open PaperIV.RC01CleanedGate
open PaperIV.RC01ResidualCoverage

variable {α : Type*} [Fintype α] [DecidableEq α]
variable {G : SimpleGraph α} [DecidableRel G.Adj]

/-- The untagged dense active profiles consumed by the cleaned physical gate. -/
noncomputable def denseActiveProfiles {δ : ℚ} (R : EqualRegularity G δ)
    (x : FracPacking G) (d θ : ℚ) : Finset (Finset (Option (Finset α))) :=
  (denseHeavyPatterns R (PaperIV.MixedRoundingAdapter.toFarFrac x) d θ).image
    profileOfMixed

/-- Forgetting the K3/K4 tag preserves the whole transferred objective, not
only the fibres and their cardinalities.  This is the exact change of index
needed before invoking `RC01CleanedGate`. -/
theorem sum_denseActiveProfiles_eq {δ : ℚ} (R : EqualRegularity G δ)
    (x : FracPacking G) (d θ : ℚ) :
    ∑ H ∈ denseActiveProfiles R x d θ,
        patternGain H * psiT x (partOf R) H =
      ∑ σ ∈ denseHeavyPatterns R (PaperIV.MixedRoundingAdapter.toFarFrac x) d θ,
        patternGain (profileOfMixed σ) *
          psiT x (partOf R) (profileOfMixed σ) := by
  classical
  rw [denseActiveProfiles, Finset.sum_image]
  intro σ hσ τ hτ heq
  exact profileOfMixed_injOn R
    (denseHeavyPatterns_subset R _ d θ hσ)
    (denseHeavyPatterns_subset R _ d θ hτ) heq

/-- Every active untagged profile is literally a K3 or K4 profile. -/
theorem denseActiveProfiles_card {δ : ℚ} (R : EqualRegularity G δ)
    (x : FracPacking G) (d θ : ℚ) {H : Finset (Option (Finset α))}
    (hH : H ∈ denseActiveProfiles R x d θ) : H.card = 3 ∨ H.card = 4 := by
  classical
  obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.1 hH
  have hσ' : σ ∈ mixedPatterns R := denseHeavyPatterns_subset R _ d θ hσ
  have hc := card_profileOfMixed R hσ'
  by_cases hleft : σ.isLeft
  · left
    simpa [hleft] using hc
  · right
    simpa [hleft] using hc

/-- Every colour occurring in an active dense profile is a genuine regularity
part.  Hence its physical colour class has exactly `R.size` vertices.  Notice
that no bound is imposed on the garbage colour `none`, because it occurs in no
active canonical profile. -/
theorem denseActiveProfiles_class_card_le {δ : ℚ} (R : EqualRegularity G δ)
    (x : FracPacking G) (d θ : ℚ) :
    ∀ H ∈ denseActiveProfiles R x d θ, ∀ p ∈ H,
      (univ.filter (fun v => partOf R v = p)).card ≤ R.size := by
  classical
  intro H hH p hp
  obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.1 hH
  have hσ' : σ ∈ mixedPatterns R := denseHeavyPatterns_subset R _ d θ hσ
  rw [mem_mixedPatterns_iff] at hσ'
  rcases hσ' with ⟨S, hS, rfl⟩ | ⟨S, hS, rfl⟩
  · change p ∈ S.image some at hp
    obtain ⟨Q, hQS, rfl⟩ := Finset.mem_image.1 hp
    have hQparts : Q ∈ R.parts := by
      rw [← (canonicalTripleOf_spec R hS).2] at hQS
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hQS
      exact canonicalTripleOf_mem_parts R hS i
    have heq : univ.filter (fun v => partOf R v = some Q) = Q := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · exact mem_of_partOf_eq_some R
      · exact partOf_eq_some R hQparts
    rw [heq, R.card_part Q hQparts]
  · change p ∈ S.image some at hp
    obtain ⟨Q, hQS, rfl⟩ := Finset.mem_image.1 hp
    have hQparts : Q ∈ R.parts := by
      rw [← (canonicalTuple_spec R hS).2] at hQS
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hQS
      exact (mem_goodK4Tuples.1 (canonicalTuple_spec R hS).1).1 i
    have heq : univ.filter (fun v => partOf R v = some Q) = Q := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · exact mem_of_partOf_eq_some R
      · exact partOf_eq_some R hQparts
    rw [heq, R.card_part Q hQparts]

/-- The transferred objective over the active dense profiles is nonnegative. -/
theorem denseProfileValue_nonneg {δ : ℚ} (R : EqualRegularity G δ)
    (x : FracPacking G) (d θ : ℚ) :
    0 ≤ ∑ H ∈ denseActiveProfiles R x d θ,
      patternGain H * psiT x (partOf R) H := by
  refine Finset.sum_nonneg fun H hH => ?_
  have hc := denseActiveProfiles_card R x d θ hH
  have hg : 0 ≤ patternGain H := by
    rcases hc with h3 | h4
    · rw [patternGain, h3]
      norm_num [Nat.choose]
    · rw [patternGain, h4]
      norm_num [Nat.choose]
  exact mul_nonneg hg (PaperIV.PatternTransfer.psiT_nonneg x (partOf R) H)

/-- Uniform quadratic bound for the whole active transferred objective.  It
uses no graph density assumption: gains are at most five and the total slot
mass is controlled by edge capacity. -/
theorem denseProfileValue_le {δ : ℚ} {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] (R : EqualRegularity G δ) (x : FracPacking G)
    (d θ : ℚ) :
    ∑ H ∈ denseActiveProfiles R x d θ,
        patternGain H * psiT x (partOf R) H ≤ (5 / 6 : ℚ) * (n : ℚ) ^ 2 := by
  have hterm :
      ∑ H ∈ denseActiveProfiles R x d θ,
          patternGain H * psiT x (partOf R) H
        ≤ 5 * ∑ H ∈ denseActiveProfiles R x d θ, psiT x (partOf R) H := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum ?_
    intro H hH
    have hc := denseActiveProfiles_card R x d θ hH
    have hg : patternGain H ≤ 5 := by
      rcases hc with h3 | h4
      · rw [patternGain, h3]
        norm_num [Nat.choose]
      · rw [patternGain, h4]
        norm_num [Nat.choose]
    exact mul_le_mul_of_nonneg_right hg
      (PaperIV.PatternTransfer.psiT_nonneg x (partOf R) H)
  exact hterm.trans
    (PaperIV.SpreadValueTransfer.five_sum_psiT_le x (partOf R)
      (denseActiveProfiles R x d θ))

/-- The literal discard/small-pattern budget controls the exact transferred
objective consumed by the cleaned physical gate. -/
theorem value_sub_discard_budget_le_transferred {δ : ℚ}
    (R : EqualRegularity G δ) (x : FracPacking G) (d θ : ℚ) (hθ : 0 ≤ θ) :
    x.value
        - (5 * ((discardEdges G R (garbage R) d).card : ℚ)
          + 5 * (((mixedPatterns R).card : ℚ) * θ)) ≤
      ∑ σ ∈ heavyPatterns R (PaperIV.MixedRoundingAdapter.toFarFrac x) θ,
        patternGain (profileOfMixed σ) *
          psiT x (partOf R) (profileOfMixed σ) := by
  refine PaperIV.RC01CanonicalTransferBridge.value_sub_residual_le_transferred
    (R := R) (x := x)
    (Active := heavyPatterns R (PaperIV.MixedRoundingAdapter.toFarFrac x) θ)
    (heavyPatterns_subset R (PaperIV.MixedRoundingAdapter.toFarFrac x) θ)
    (Δ := 5 * ((discardEdges G R (garbage R) d).card : ℚ)
      + 5 * (((mixedPatterns R).card : ℚ) * θ)) ?_
  exact offCanonicalValue_le_garbage_discards R
    (PaperIV.MixedRoundingAdapter.toFarFrac x) d θ hθ

/-- Fully numerical `(15.1)` form of the same closure. -/
theorem value_sub_regularity_budget_le_transferred {δ : ℚ} (hδ : 0 ≤ δ)
    (R : EqualRegularity G δ) (x : FracPacking G) (d θ : ℚ)
    (hd : 0 ≤ d) (hθ : 0 ≤ θ) {k₀ : ℕ} (hk₀ : 0 < k₀)
    (hk : k₀ ≤ R.parts.card) :
    x.value
        - (5 * ((3 * δ + 1 / (k₀ : ℚ) + d) * (Fintype.card α : ℚ) ^ 2)
          + 5 * (((mixedPatterns R).card : ℚ) * θ)) ≤
      ∑ σ ∈ heavyPatterns R (PaperIV.MixedRoundingAdapter.toFarFrac x) θ,
        patternGain (profileOfMixed σ) *
          psiT x (partOf R) (profileOfMixed σ) := by
  refine PaperIV.RC01CanonicalTransferBridge.value_sub_residual_le_transferred
    (R := R) (x := x)
    (Active := heavyPatterns R (PaperIV.MixedRoundingAdapter.toFarFrac x) θ)
    (heavyPatterns_subset R (PaperIV.MixedRoundingAdapter.toFarFrac x) θ)
    (Δ := 5 * ((3 * δ + 1 / (k₀ : ℚ) + d) * (Fintype.card α : ℚ) ^ 2)
      + 5 * (((mixedPatterns R).card : ℚ) * θ)) ?_
  exact offCanonicalValue_le_regularity_budget hδ R
    (PaperIV.MixedRoundingAdapter.toFarFrac x) d θ hd hθ hk₀ hk

/-- The numerical transferred-value closure with a surviving family that is
already `d`-dense.  This removes the former mismatch between residual coverage
and the positive-volume hypotheses of the cleaned physical gate. -/
theorem value_sub_dense_regularity_budget_le_transferred {δ : ℚ} (hδ : 0 ≤ δ)
    (R : EqualRegularity G δ) (x : FracPacking G) (d θ : ℚ)
    (hd : 0 ≤ d) (hθ : 0 ≤ θ) {k₀ : ℕ} (hk₀ : 0 < k₀)
    (hk : k₀ ≤ R.parts.card) :
    x.value
        - (5 * ((3 * δ + 1 / (k₀ : ℚ) + d) * (Fintype.card α : ℚ) ^ 2)
          + 5 * (((mixedPatterns R).card : ℚ) * θ)) ≤
      ∑ σ ∈ denseHeavyPatterns R (PaperIV.MixedRoundingAdapter.toFarFrac x) d θ,
        patternGain (profileOfMixed σ) *
          psiT x (partOf R) (profileOfMixed σ) := by
  refine PaperIV.RC01CanonicalTransferBridge.value_sub_residual_le_transferred
    (R := R) (x := x)
    (Active := denseHeavyPatterns R (PaperIV.MixedRoundingAdapter.toFarFrac x) d θ)
    (denseHeavyPatterns_subset R (PaperIV.MixedRoundingAdapter.toFarFrac x) d θ)
    (Δ := 5 * ((3 * δ + 1 / (k₀ : ℚ) + d) * (Fintype.card α : ℚ) ^ 2)
      + 5 * (((mixedPatterns R).card : ℚ) * θ)) ?_
  exact offCanonicalValue_le_dense_regularity_budget hδ R
    (PaperIV.MixedRoundingAdapter.toFarFrac x) d θ hd hθ hk₀ hk

/-- The same numerical closure, already indexed by the untagged profiles that
the cleaned physical gate consumes. -/
theorem value_sub_dense_regularity_budget_le_profiles {δ : ℚ} (hδ : 0 ≤ δ)
    (R : EqualRegularity G δ) (x : FracPacking G) (d θ : ℚ)
    (hd : 0 ≤ d) (hθ : 0 ≤ θ) {k₀ : ℕ} (hk₀ : 0 < k₀)
    (hk : k₀ ≤ R.parts.card) :
    x.value
        - (5 * ((3 * δ + 1 / (k₀ : ℚ) + d) * (Fintype.card α : ℚ) ^ 2)
          + 5 * (((mixedPatterns R).card : ℚ) * θ)) ≤
      ∑ H ∈ denseActiveProfiles R x d θ,
        patternGain H * psiT x (partOf R) H := by
  rw [sum_denseActiveProfiles_eq R x d θ]
  exact value_sub_dense_regularity_budget_le_transferred hδ R x d θ hd hθ hk₀ hk

end PaperIV.RC01ResidualTransferClosure
