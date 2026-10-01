import PaperIV.RC01MixedPatterns
import PaperIV.RC01RegularVolume

/-!
# RC01: canonical mixed slots as coordinate-free profiles

The probabilistic selection layer uses a tagged `MixedPattern`, while the
cleaned physical gate uses an untagged finite set of partition colours.  The
tag carries no mathematical information: a `K3` profile has cardinality three
and a `K4` profile has cardinality four.  This module proves that the forgetful
map is injective on the canonical family and identifies its literal profile.
-/

namespace PaperIV.RC01CanonicalProfile

open Finset
open PaperIV.PatternCounting
open PaperIV.RegularityFormat
open PaperIV.PartitionBridge
open PaperIV.RC01Candidates
open PaperIV.RC01CandidatePool
open PaperIV.RC01CanonicalSlots
open PaperIV.RC01K3Pool
open PaperIV.RC01MixedPatterns
open PaperIV.RC01RegularVolume

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Forget the K3/K4 tag and regard a canonical slot as a set of actual
partition colours. -/
noncomputable def profileOfMixed : MixedPattern V → Finset (Option (Finset V))
  | Sum.inl S => S.image some
  | Sum.inr S => S.image some

private theorem image_some_injective {S T : Finset (Finset V)}
    (h : S.image some = T.image some) : S = T := by
  ext Q
  have hQ := Finset.ext_iff.1 h (some Q)
  simpa using hQ

/-- Every canonical triangle slot contains exactly three regularity parts. -/
theorem card_goodK3Slot {δ : ℚ} (R : EqualRegularity G δ)
    {S : Finset (Finset V)} (hS : S ∈ goodK3Slots R) : S.card = 3 := by
  have hspec := canonicalTripleOf_spec R hS
  have hne := (mem_goodK3Tuples.1 hspec.1).2.1
  rw [← hspec.2, partImageOf, Finset.card_image_of_injective,
    Finset.card_univ, Fintype.card_fin]
  intro i j hEq
  by_contra hij
  exact hne i j hij hEq

/-- Every canonical four-clique slot contains exactly four regularity parts. -/
theorem card_goodK4Slot {δ : ℚ} (R : EqualRegularity G δ)
    {S : Finset (Finset V)} (hS : S ∈ goodK4Slots R) : S.card = 4 := by
  have hspec := canonicalTuple_spec R hS
  have hne := (mem_goodK4Tuples.1 hspec.1).2.1
  rw [← hspec.2, partImage, Finset.card_image_of_injective,
    Finset.card_univ, Fintype.card_fin]
  intro i j hEq
  by_contra hij
  exact hne i j hij hEq

/-- The tag-forgetting profile has the expected cardinality. -/
theorem card_profileOfMixed {δ : ℚ} (R : EqualRegularity G δ)
    {σ : MixedPattern V} (hσ : σ ∈ mixedPatterns R) :
    (profileOfMixed σ).card = if σ.isLeft then 3 else 4 := by
  rw [mem_mixedPatterns_iff] at hσ
  rcases hσ with ⟨S, hS, rfl⟩ | ⟨S, hS, rfl⟩
  · rw [profileOfMixed,
      Finset.card_image_of_injective _ (Option.some_injective _),
      card_goodK3Slot R hS]
    rfl
  · rw [profileOfMixed,
      Finset.card_image_of_injective _ (Option.some_injective _),
      card_goodK4Slot R hS]
    rfl

/-- Forgetting the tag is injective on the selected canonical family.  Cross
type collisions are ruled out by the literal cardinalities three and four. -/
theorem profileOfMixed_injOn {δ : ℚ} (R : EqualRegularity G δ) :
    Set.InjOn profileOfMixed (mixedPatterns R : Set (MixedPattern V)) := by
  intro σ hσ τ hτ hEq
  have hσ' : σ ∈ mixedPatterns R := hσ
  have hτ' : τ ∈ mixedPatterns R := hτ
  rw [mem_mixedPatterns_iff] at hσ' hτ'
  rcases hσ' with ⟨S, hS, rfl⟩ | ⟨S, hS, rfl⟩ <;>
    rcases hτ' with ⟨T, hT, rfl⟩ | ⟨T, hT, rfl⟩
  · exact congrArg Sum.inl (image_some_injective hEq)
  · exfalso
    have hc := congrArg Finset.card hEq
    rw [profileOfMixed, profileOfMixed,
      Finset.card_image_of_injective _ (Option.some_injective _),
      Finset.card_image_of_injective _ (Option.some_injective _),
      card_goodK3Slot R hS, card_goodK4Slot R hT] at hc
    omega
  · exfalso
    have hc := congrArg Finset.card hEq
    rw [profileOfMixed, profileOfMixed,
      Finset.card_image_of_injective _ (Option.some_injective _),
      Finset.card_image_of_injective _ (Option.some_injective _),
      card_goodK4Slot R hS, card_goodK3Slot R hT] at hc
    omega
  · exact congrArg Sum.inr (image_some_injective hEq)

/-- The indexed representative of a canonical triangle slot has exactly the
coordinate-free profile obtained by forgetting its tag. -/
theorem regularPattern_canonicalTriple {δ : ℚ} (R : EqualRegularity G δ)
    {S : Finset (Finset V)} (hS : S ∈ goodK3Slots R) :
    regularPattern (canonicalTripleOf R S) = profileOfMixed (Sum.inl S) := by
  change regularPattern (canonicalTripleOf R S) = S.image some
  calc
    regularPattern (canonicalTripleOf R S)
        = (partImageOf (canonicalTripleOf R S)).image some := by
          ext Q
          simp [regularPattern, partImageOf]
    _ = S.image some := congrArg (Finset.image some) (canonicalTripleOf_spec R hS).2

/-- The indexed representative of a canonical K4 slot has exactly the
coordinate-free profile obtained by forgetting its tag. -/
theorem regularPattern_canonicalTuple {δ : ℚ} (R : EqualRegularity G δ)
    {S : Finset (Finset V)} (hS : S ∈ goodK4Slots R) :
    regularPattern (canonicalTuple R S) = profileOfMixed (Sum.inr S) := by
  change regularPattern (canonicalTuple R S) = S.image some
  calc
    regularPattern (canonicalTuple R S)
        = (partImage (canonicalTuple R S)).image some := by
          ext Q
          simp [regularPattern, partImage]
    _ = S.image some := congrArg (Finset.image some) (canonicalTuple_spec R hS).2

end PaperIV.RC01CanonicalProfile
