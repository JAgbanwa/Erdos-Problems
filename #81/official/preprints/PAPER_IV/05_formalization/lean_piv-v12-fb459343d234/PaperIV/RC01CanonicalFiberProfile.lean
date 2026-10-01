import PaperIV.RC01CanonicalProfile

/-!
# RC01: the exact canonical fibre/profile adapter

`RC01RegularVolume` proves one inclusion: every indexed transversal candidate of
a regular tuple lies in the coordinate-free profile fibre of the cleaned gate.
This module proves the **reciprocal** inclusion and therefore the exact identity

```
mixedFiber R σ = profileFiber G (partOf R) (profileOfMixed σ)
```

for every selected canonical pattern `σ ∈ mixedPatterns R`.

The reverse inclusion is a genuine reconstruction: from an item `K` whose image
under `partOf R` is exactly the canonical profile, and whose cardinality equals
the cardinality of that profile, one recovers the *unique* indexed transversal
`φ` with `piece φ = K`.  Injectivity of `partOf R` on `K` is exactly what the
cardinality condition provides, and the clique condition of `IsItem` supplies
all the adjacencies required by `patK3` / `patK4`.

Nothing is postulated: no equality interface and no choice interface is
assumed.  The only choice used is the ordinary `Classical.choice` behind
`Finset.image` membership.

The last section derives the corollaries that make this adapter usable in the
cleanup layer: equality of fibre cardinalities, exact transport of arbitrary
additive fibre functionals (hence of `rawMass` and `slotMass`) along the
injective forgetful map, and the family-level statement allowing tagged
`mixedFiber` to be replaced by untagged `profileFiber`.

This is only the canonical fibre/profile adapter; it says nothing about the
far-rounding layer, the deviation cleanup, or the global RC01 route.
-/

namespace PaperIV.RC01CanonicalFiberProfile

open Finset
open PaperIV.PatternCounting
open PaperIV.RegularityFormat
open PaperIV.PartitionBridge
open PaperIV.FarRounding
open PaperIV.RC01Candidates
open PaperIV.RC01CandidatePool
open PaperIV.RC01CanonicalSlots
open PaperIV.RC01K3Pool
open PaperIV.RC01CleanFiber
open PaperIV.RC01MixedPatterns
open PaperIV.RC01RegularVolume
open PaperIV.RC01CanonicalProfile

variable {α : Type*} [Fintype α] [DecidableEq α]
variable {G : SimpleGraph α} [DecidableRel G.Adj]

/-! ## 1. Reading a colour backwards -/

/-- If a vertex has colour `some Q`, then it really lies in the part `Q`.  This
is the converse of `PartitionBridge.partOf_eq_some` and is what allows an item
of the profile fibre to be read as an indexed transversal. -/
theorem mem_of_partOf_eq_some {δ : ℚ} (R : EqualRegularity G δ) {v : α}
    {Q : Finset α} (h : partOf R v = some Q) : v ∈ Q := by
  classical
  by_cases hex : ∃ Q' ∈ R.parts, v ∈ Q'
  · rw [partOf, dif_pos hex] at h
    have hQ : hex.choose = Q := Option.some.inj h
    have hspec := hex.choose_spec
    rw [hQ] at hspec
    exact hspec.2
  · rw [partOf, dif_neg hex] at h
    exact absurd h (by simp)

/-- If a vertex has colour `some Q`, then `Q` is a genuine regularity part. -/
theorem mem_parts_of_partOf_eq_some {δ : ℚ} (R : EqualRegularity G δ) {v : α}
    {Q : Finset α} (h : partOf R v = some Q) : Q ∈ R.parts := by
  classical
  by_cases hex : ∃ Q' ∈ R.parts, v ∈ Q'
  · rw [partOf, dif_pos hex] at h
    have hQ : hex.choose = Q := Option.some.inj h
    have hspec := hex.choose_spec
    rw [hQ] at hspec
    exact hspec.1
  · rw [partOf, dif_neg hex] at h
    exact absurd h (by simp)

/-! ## 2. Reconstructing the indexed transversal -/

/-- **The reverse inclusion.**  An item whose `partOf R`-image is exactly the
reduced pattern of an injective family of regularity parts, and whose
cardinality equals the cardinality of that pattern, is the piece of a (unique)
indexed transversal of that family.  Only the off-diagonality of the pattern
`F` is needed: all its adjacencies come from the clique condition of `IsItem`.
-/
theorem profileFiber_subset_candidates {ι : Type*} [Fintype ι] [DecidableEq ι]
    {δ : ℚ} (R : EqualRegularity G δ) (V : ι → Finset α)
    (hV : ∀ i, V i ∈ R.parts) (hVinj : Function.Injective V)
    (F : Finset (ι × ι)) (hF : ∀ e ∈ F, e.1 ≠ e.2) :
    profileFiber G (partOf R) (regularPattern V) ⊆ candidates G V F := by
  classical
  intro K hK
  obtain ⟨hitem, himg, hcard⟩ := mem_profileFiber.1 hK
  obtain ⟨hclique, -⟩ := mem_items.1 hitem
  have hex : ∀ i : ι, ∃ x, x ∈ K ∧ partOf R x = some (V i) := by
    intro i
    have hmem : some (V i) ∈ K.image (partOf R) := by
      rw [himg, regularPattern]
      exact Finset.mem_image.2 ⟨i, Finset.mem_univ i, rfl⟩
    obtain ⟨x, hx, hxp⟩ := Finset.mem_image.1 hmem
    exact ⟨x, hx, hxp⟩
  choose φ hφK hφp using hex
  have hφV : ∀ i, φ i ∈ V i := fun i => mem_of_partOf_eq_some R (hφp i)
  have hdisj : ∀ i j : ι, i ≠ j → Disjoint (V i) (V j) := by
    intro i j hij
    exact R.pairwise_disjoint _ (hV i) _ (hV j) (fun h => hij (hVinj h))
  have hinj : Function.Injective φ := injective_of_mem_piFinset hdisj hφV
  have hmem : φ ∈ transversal G V F := by
    refine mem_transversal.2 ⟨hφV, ?_⟩
    intro e he
    exact hclique _ (hφK e.1) _ (hφK e.2) (fun h => hF e he (hinj h))
  refine mem_candidates.2 ⟨φ, hmem, ?_⟩
  have hsub : piece φ ⊆ K := by
    intro a ha
    obtain ⟨i, rfl⟩ := mem_piece.1 ha
    exact hφK i
  have hcardpiece : (piece φ).card = K.card := by
    rw [card_piece hdisj hφV, hcard, card_regularPattern V hVinj]
  exact Finset.eq_of_subset_of_card_le hsub (le_of_eq hcardpiece.symm)

/-! ## 3. The exact identity for one indexed family -/

/-- Exact identification of the literal `K3` candidate fibre with the
coordinate-free profile fibre. -/
theorem candidates_K3_eq_profileFiber {δ : ℚ} (R : EqualRegularity G δ)
    (V : Fin 3 → Finset α) (hV : ∀ i, V i ∈ R.parts)
    (hVinj : Function.Injective V) :
    candidates G V patK3 = profileFiber G (partOf R) (regularPattern V) :=
  Finset.Subset.antisymm
    (candidates_K3_subset_profileFiber R V hV hVinj)
    (profileFiber_subset_candidates R V hV hVinj patK3 patK3_ne)

/-- Exact identification of the literal `K4` candidate fibre with the
coordinate-free profile fibre. -/
theorem candidates_K4_eq_profileFiber {δ : ℚ} (R : EqualRegularity G δ)
    (V : Fin 4 → Finset α) (hV : ∀ i, V i ∈ R.parts)
    (hVinj : Function.Injective V) :
    candidates G V patK4 = profileFiber G (partOf R) (regularPattern V) :=
  Finset.Subset.antisymm
    (candidates_K4_subset_profileFiber R V hV hVinj)
    (profileFiber_subset_candidates R V hV hVinj patK4 patK4_ne)

/-! ## 4. The tagged canonical statement -/

theorem canonicalTripleOf_injective {δ : ℚ} (R : EqualRegularity G δ)
    {S : Finset (Finset α)} (hS : S ∈ goodK3Slots R) :
    Function.Injective (canonicalTripleOf R S) := by
  intro i j hij
  by_contra hne
  exact canonicalTripleOf_ne R hS hne hij

theorem canonicalTuple_mem_parts {δ : ℚ} (R : EqualRegularity G δ)
    {S : Finset (Finset α)} (hS : S ∈ goodK4Slots R) (i : Fin 4) :
    canonicalTuple R S i ∈ R.parts :=
  (mem_goodK4Tuples.1 (canonicalTuple_spec R hS).1).1 i

theorem canonicalTuple_injective {δ : ℚ} (R : EqualRegularity G δ)
    {S : Finset (Finset α)} (hS : S ∈ goodK4Slots R) :
    Function.Injective (canonicalTuple R S) := by
  intro i j hij
  by_contra hne
  exact (mem_goodK4Tuples.1 (canonicalTuple_spec R hS).1).2.1 i j hne hij

/-- **The `K3` case of the adapter.** -/
theorem mixedFiber_inl_eq_profileFiber {δ : ℚ} (R : EqualRegularity G δ)
    {S : Finset (Finset α)} (hS : S ∈ goodK3Slots R) :
    mixedFiber R (Sum.inl S)
      = profileFiber G (partOf R) (profileOfMixed (Sum.inl S)) := by
  have h := candidates_K3_eq_profileFiber R (canonicalTripleOf R S)
    (canonicalTripleOf_mem_parts R hS) (canonicalTripleOf_injective R hS)
  rw [mixedFiber, h, regularPattern_canonicalTriple R hS]

/-- **The `K4` case of the adapter.** -/
theorem mixedFiber_inr_eq_profileFiber {δ : ℚ} (R : EqualRegularity G δ)
    {S : Finset (Finset α)} (hS : S ∈ goodK4Slots R) :
    mixedFiber R (Sum.inr S)
      = profileFiber G (partOf R) (profileOfMixed (Sum.inr S)) := by
  have h := candidates_K4_eq_profileFiber R (canonicalTuple R S)
    (canonicalTuple_mem_parts R hS) (canonicalTuple_injective R hS)
  rw [mixedFiber, h, regularPattern_canonicalTuple R hS]

/-- **The exact reciprocal identification.**  For every selected canonical
pattern the tagged literal fibre and the untagged coordinate-free profile
fibre are the *same* finite set of items. -/
theorem mixedFiber_eq_profileFiber {δ : ℚ} (R : EqualRegularity G δ)
    {σ : MixedPattern α} (hσ : σ ∈ mixedPatterns R) :
    mixedFiber R σ = profileFiber G (partOf R) (profileOfMixed σ) := by
  rw [mem_mixedPatterns_iff] at hσ
  rcases hσ with ⟨S, hS, rfl⟩ | ⟨S, hS, rfl⟩
  · exact mixedFiber_inl_eq_profileFiber R hS
  · exact mixedFiber_inr_eq_profileFiber R hS

/-! ## 5. Corollaries -/

/-- Equality of fibre cardinalities. -/
theorem card_mixedFiber_eq {δ : ℚ} (R : EqualRegularity G δ)
    {σ : MixedPattern α} (hσ : σ ∈ mixedPatterns R) :
    (mixedFiber R σ).card
      = (profileFiber G (partOf R) (profileOfMixed σ)).card := by
  rw [mixedFiber_eq_profileFiber R hσ]

/-- Membership transport: an item is in the tagged fibre exactly when it is in
the untagged profile fibre. -/
theorem mem_mixedFiber_iff_mem_profileFiber {δ : ℚ} (R : EqualRegularity G δ)
    {σ : MixedPattern α} (hσ : σ ∈ mixedPatterns R) {K : Finset α} :
    K ∈ mixedFiber R σ ↔ K ∈ profileFiber G (partOf R) (profileOfMixed σ) := by
  rw [mixedFiber_eq_profileFiber R hσ]

/-- The untagged canonical profile family. -/
noncomputable def canonicalProfiles {δ : ℚ} (R : EqualRegularity G δ) :
    Finset (Finset (Option (Finset α))) :=
  (mixedPatterns R).image profileOfMixed

theorem mem_canonicalProfiles {δ : ℚ} {R : EqualRegularity G δ}
    {H : Finset (Option (Finset α))} :
    H ∈ canonicalProfiles R ↔ ∃ σ ∈ mixedPatterns R, profileOfMixed σ = H := by
  rw [canonicalProfiles, Finset.mem_image]

/-- Forgetting the tag loses no patterns. -/
theorem card_canonicalProfiles {δ : ℚ} (R : EqualRegularity G δ) :
    (canonicalProfiles R).card = (mixedPatterns R).card :=
  Finset.card_image_of_injOn (profileOfMixed_injOn R)

/-- **Exact transport of any additive fibre functional** along the injective
forgetful map, for an arbitrary selected subfamily. -/
theorem sum_mixedFiber_eq_sum_profileFiber {M : Type*} [AddCommMonoid M]
    {δ : ℚ} (R : EqualRegularity G δ) (Active : Finset (MixedPattern α))
    (hActive : Active ⊆ mixedPatterns R) (f : Finset (Finset α) → M) :
    ∑ σ ∈ Active, f (mixedFiber R σ)
      = ∑ H ∈ Active.image profileOfMixed,
          f (profileFiber G (partOf R) H) := by
  classical
  rw [Finset.sum_image
    (fun σ hσ τ hτ h => profileOfMixed_injOn R (hActive hσ) (hActive hτ) h)]
  refine Finset.sum_congr rfl ?_
  intro σ hσ
  rw [mixedFiber_eq_profileFiber R (hActive hσ)]

/-- Pointwise mass identity: the tagged and untagged raw masses of one
canonical pattern agree. -/
theorem rawMass_mixedFiber_eq {δ : ℚ} (R : EqualRegularity G δ)
    (x : FracPacking G ℚ) {σ : MixedPattern α}
    (hσ : σ ∈ mixedPatterns R) :
    PaperIV.RC01PatternCapacity.rawMass x (mixedFiber R) σ
      = PaperIV.RC01PatternCapacity.rawMass x
          (profileFiber G (partOf R)) (profileOfMixed σ) := by
  unfold PaperIV.RC01PatternCapacity.rawMass
  rw [mixedFiber_eq_profileFiber R hσ]

/-- Pointwise mass identity for the normalized slot mass. -/
theorem slotMass_mixedFiber_eq {δ : ℚ} (R : EqualRegularity G δ)
    (x : FracPacking G ℚ) (t : ℕ) {σ : MixedPattern α}
    (hσ : σ ∈ mixedPatterns R) :
    PaperIV.RC01PatternCapacity.slotMass x t (mixedFiber R) σ
      = PaperIV.RC01PatternCapacity.slotMass x t
          (profileFiber G (partOf R)) (profileOfMixed σ) := by
  unfold PaperIV.RC01PatternCapacity.slotMass
  rw [mixedFiber_eq_profileFiber R hσ]

/-- Exact transport of the raw fractional fibre mass. -/
theorem sum_rawMass_eq {δ : ℚ} (R : EqualRegularity G δ)
    (x : FracPacking G ℚ)
    (Active : Finset (MixedPattern α)) (hActive : Active ⊆ mixedPatterns R) :
    ∑ σ ∈ Active, PaperIV.RC01PatternCapacity.rawMass x (mixedFiber R) σ
      = ∑ H ∈ Active.image profileOfMixed,
          PaperIV.RC01PatternCapacity.rawMass x
            (profileFiber G (partOf R)) H := by
  classical
  rw [Finset.sum_image
    (fun σ hσ τ hτ h => profileOfMixed_injOn R (hActive hσ) (hActive hτ) h)]
  exact Finset.sum_congr rfl
    (fun σ hσ => rawMass_mixedFiber_eq R x (hActive hσ))

/-- Exact transport of the normalized fractional fibre mass. -/
theorem sum_slotMass_eq {δ : ℚ} (R : EqualRegularity G δ)
    (x : FracPacking G ℚ) (t : ℕ)
    (Active : Finset (MixedPattern α)) (hActive : Active ⊆ mixedPatterns R) :
    ∑ σ ∈ Active, PaperIV.RC01PatternCapacity.slotMass x t (mixedFiber R) σ
      = ∑ H ∈ Active.image profileOfMixed,
          PaperIV.RC01PatternCapacity.slotMass x t
            (profileFiber G (partOf R)) H := by
  classical
  rw [Finset.sum_image
    (fun σ hσ τ hτ h => profileOfMixed_injOn R (hActive hσ) (hActive hτ) h)]
  exact Finset.sum_congr rfl
    (fun σ hσ => slotMass_mixedFiber_eq R x t (hActive hσ))

/-- **The cleanup-ready statement.**  The union of the tagged fibres over any
selected subfamily is literally the union of the untagged profile fibres over
its image.  Tagged `mixedFiber` may therefore be replaced by untagged
`profileFiber` with no loss and no duplication. -/
theorem biUnion_mixedFiber_eq {δ : ℚ} (R : EqualRegularity G δ)
    (Active : Finset (MixedPattern α)) (hActive : Active ⊆ mixedPatterns R) :
    Active.biUnion (mixedFiber R)
      = (Active.image profileOfMixed).biUnion
          (profileFiber G (partOf R)) := by
  classical
  rw [Finset.image_biUnion]
  refine Finset.biUnion_congr rfl ?_
  intro σ hσ
  exact mixedFiber_eq_profileFiber R (hActive hσ)

/-- The untagged profile fibres of a selected subfamily are pairwise disjoint:
the exact hypothesis needed to run the cleaned physical gate on profiles
instead of tags. -/
theorem profileFiber_pairwiseDisjoint {δ : ℚ} (R : EqualRegularity G δ)
    (Active : Finset (MixedPattern α)) (hActive : Active ⊆ mixedPatterns R) :
    Set.PairwiseDisjoint
      ((Active.image profileOfMixed : Finset (Finset (Option (Finset α))))
        : Set (Finset (Option (Finset α))))
      (profileFiber G (partOf R)) := by
  classical
  intro H hH H' hH' hne
  obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.1 hH
  obtain ⟨τ, hτ, rfl⟩ := Finset.mem_image.1 hH'
  have hστ : σ ≠ τ := by
    intro h
    exact hne (congrArg profileOfMixed h)
  have hdisj : Disjoint (mixedFiber R σ) (mixedFiber R τ) :=
    mixedFiber_pairwiseDisjoint R (hActive hσ) (hActive hτ) hστ
  rw [mixedFiber_eq_profileFiber R (hActive hσ),
    mixedFiber_eq_profileFiber R (hActive hτ)] at hdisj
  exact hdisj

/-- Cardinality of the selected union, computed on untagged profiles. -/
theorem card_biUnion_profileFiber {δ : ℚ} (R : EqualRegularity G δ)
    (Active : Finset (MixedPattern α)) (hActive : Active ⊆ mixedPatterns R) :
    ((Active.image profileOfMixed).biUnion
        (profileFiber G (partOf R))).card
      = ∑ σ ∈ Active, (mixedFiber R σ).card := by
  classical
  rw [← biUnion_mixedFiber_eq R Active hActive]
  refine Finset.card_biUnion ?_
  intro σ hσ τ hτ hne
  exact mixedFiber_pairwiseDisjoint R (hActive hσ) (hActive hτ) hne

end PaperIV.RC01CanonicalFiberProfile


