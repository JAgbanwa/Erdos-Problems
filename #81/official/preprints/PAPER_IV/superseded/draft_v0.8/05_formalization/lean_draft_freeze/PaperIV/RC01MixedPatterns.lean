import PaperIV.RC01PatternCapacity
import PaperIV.RC01CanonicalSlots
import PaperIV.RC01K3Pool

/-!
# RC01: one typed family of canonical K3/K4 reduced patterns

The two clique sizes must compete for the same physical edge capacity.  This
module therefore combines their canonical slots into one tagged pattern type
and proves that the corresponding literal item fibres are pairwise disjoint.
-/

namespace PaperIV.RC01MixedPatterns

open Finset
open PaperIV.PatternCounting PaperIV.RegularityFormat PaperIV.RC01Candidates
open PaperIV.RC01CanonicalSlots PaperIV.RC01K3Pool
open PaperIV.FarRounding PaperIV.PatternMass PaperIV.RC01PatternCapacity

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A tag is essential: a triangle slot and a K4 slot are different colours
even though both are represented by a finite set of regularity parts. -/
abbrev MixedPattern (V : Type*) :=
  Sum (Finset (Finset V)) (Finset (Finset V))

/-- All canonical reduced patterns, with K3 on the left and K4 on the right. -/
noncomputable def mixedPatterns {δ : ℚ} (R : EqualRegularity G δ) :
    Finset (MixedPattern V) :=
  (goodK3Slots R).image Sum.inl ∪ (goodK4Slots R).image Sum.inr

/-- The literal fractional-item fibre represented by one reduced pattern. -/
noncomputable def mixedFiber {δ : ℚ} (R : EqualRegularity G δ) :
    MixedPattern V → Finset (Finset V)
  | Sum.inl S => candidates G (canonicalTripleOf R S) patK3
  | Sum.inr S => candidates G (canonicalTuple R S) patK4

theorem mem_mixedPatterns_iff {δ : ℚ} {R : EqualRegularity G δ}
    {σ : MixedPattern V} :
    σ ∈ mixedPatterns R ↔
      (∃ S ∈ goodK3Slots R, σ = Sum.inl S) ∨
      (∃ S ∈ goodK4Slots R, σ = Sum.inr S) := by
  constructor
  · intro h
    rw [mixedPatterns, Finset.mem_union] at h
    rcases h with h | h
    · obtain ⟨S, hS, hEq⟩ := Finset.mem_image.1 h
      exact Or.inl ⟨S, hS, hEq.symm⟩
    · obtain ⟨S, hS, hEq⟩ := Finset.mem_image.1 h
      exact Or.inr ⟨S, hS, hEq.symm⟩
  · rintro (⟨S, hS, rfl⟩ | ⟨S, hS, rfl⟩)
    · rw [mixedPatterns, Finset.mem_union]
      exact Or.inl (Finset.mem_image.2 ⟨S, hS, rfl⟩)
    · rw [mixedPatterns, Finset.mem_union]
      exact Or.inr (Finset.mem_image.2 ⟨S, hS, rfl⟩)

private theorem card_of_mem_k3Fiber {δ : ℚ} (R : EqualRegularity G δ)
    {S : Finset (Finset V)} (hS : S ∈ goodK3Slots R) {K : Finset V}
    (hK : K ∈ mixedFiber R (Sum.inl S)) : K.card = 3 := by
  rw [mixedFiber] at hK
  obtain ⟨φ, hφ, rfl⟩ := mem_candidates.1 hK
  rw [card_piece (fun i j hij => canonicalTripleOf_disjoint R hS hij)
    (mem_transversal.1 hφ).1]
  decide

private theorem card_of_mem_k4Fiber {δ : ℚ} (R : EqualRegularity G δ)
    {S : Finset (Finset V)} (hS : S ∈ goodK4Slots R) {K : Finset V}
    (hK : K ∈ mixedFiber R (Sum.inr S)) : K.card = 4 := by
  rw [mixedFiber] at hK
  obtain ⟨φ, hφ, rfl⟩ := mem_candidates.1 hK
  have hgood := (canonicalTuple_spec R hS).1
  have hparts := (PaperIV.RC01CandidatePool.mem_goodK4Tuples.1 hgood).1
  have hdisj : ∀ i j : Fin 4, i ≠ j →
      Disjoint (canonicalTuple R S i) (canonicalTuple R S j) := by
    intro i j hij
    exact R.pairwise_disjoint _ (hparts i) _ (hparts j)
      ((PaperIV.RC01CandidatePool.mem_goodK4Tuples.1 hgood).2.1 i j hij)
  rw [card_piece hdisj (mem_transversal.1 hφ).1]
  decide

/-- Canonical reduced patterns have disjoint literal item fibres.  Same-size
fibres are disjoint by canonicalization; cross-size fibres are disjoint because
a finite vertex set cannot simultaneously have cardinalities three and four. -/
theorem mixedFiber_pairwiseDisjoint {δ : ℚ} (R : EqualRegularity G δ) :
    Set.PairwiseDisjoint (mixedPatterns R : Set (MixedPattern V)) (mixedFiber R) := by
  intro σ hσ τ hτ hne
  have hσ' : σ ∈ mixedPatterns R := hσ
  have hτ' : τ ∈ mixedPatterns R := hτ
  rw [mem_mixedPatterns_iff] at hσ' hτ'
  rcases hσ' with ⟨S, hS, rfl⟩ | ⟨S, hS, rfl⟩ <;>
    rcases hτ' with ⟨T, hT, hτ⟩ | ⟨T, hT, hτ⟩
  · cases hτ
    exact canonical_slot_candidates_disjointK3 R hS hT
      (fun h => hne (congrArg Sum.inl h))
  · cases hτ
    change Disjoint (mixedFiber R (Sum.inl S)) (mixedFiber R (Sum.inr T))
    rw [Finset.disjoint_left]
    intro K hK3 hK4
    have h3 := card_of_mem_k3Fiber R hS hK3
    have h4 := card_of_mem_k4Fiber R hT hK4
    omega
  · cases hτ
    change Disjoint (mixedFiber R (Sum.inr S)) (mixedFiber R (Sum.inl T))
    rw [Finset.disjoint_left]
    intro K hK4 hK3
    have h4 := card_of_mem_k4Fiber R hS hK4
    have h3 := card_of_mem_k3Fiber R hT hK3
    omega
  · cases hτ
    exact canonical_slot_candidates_disjoint R hS hT
      (fun h => hne (congrArg Sum.inr h))

/-- Every selected subfamily of canonical mixed patterns inherits disjoint
fibres.  This is the exact hypothesis consumed by `RC01PatternCapacity`. -/
theorem mixedFiber_pairwiseDisjoint_of_subset {δ : ℚ} (R : EqualRegularity G δ)
    (Active : Finset (MixedPattern V)) (hActive : Active ⊆ mixedPatterns R) :
    Set.PairwiseDisjoint (Active : Set (MixedPattern V)) (mixedFiber R) := by
  intro σ hσ τ hτ hne
  exact mixedFiber_pairwiseDisjoint R (hActive hσ) (hActive hτ) hne

/-- Every item in a canonical mixed fibre is a literal K3/K4 item of `G`. -/
theorem mixedFiber_subset_items {δ : ℚ} (R : EqualRegularity G δ)
    {σ : MixedPattern V} (hσ : σ ∈ mixedPatterns R) :
    mixedFiber R σ ⊆ items G := by
  rw [mem_mixedPatterns_iff] at hσ
  rcases hσ with ⟨S, hS, rfl⟩ | ⟨S, hS, rfl⟩
  · intro K hK
    rw [mixedFiber] at hK
    exact mem_items.2 (candidates_K3_isItem
      (fun i j hij => canonicalTripleOf_disjoint R hS hij) hK)
  · intro K hK
    rw [mixedFiber] at hK
    have hgood := (canonicalTuple_spec R hS).1
    have hparts := (PaperIV.RC01CandidatePool.mem_goodK4Tuples.1 hgood).1
    have hdisj : ∀ i j : Fin 4, i ≠ j →
        Disjoint (canonicalTuple R S i) (canonicalTuple R S j) := by
      intro i j hij
      exact R.pairwise_disjoint _ (hparts i) _ (hparts j)
        ((PaperIV.RC01CandidatePool.mem_goodK4Tuples.1 hgood).2.1 i j hij)
    exact mem_items.2 (candidates_K4_isItem hdisj hK)

/-- Patterns which are physically eligible on the regular pair `(A,B)`: all
items in their canonical fibre contain a real cross edge of that pair.  This
semantic definition avoids choosing orientations of an unordered slot. -/
noncomputable def activePatterns {δ : ℚ} (R : EqualRegularity G δ)
    (A B : Finset V) : Finset (MixedPattern V) :=
  (mixedPatterns R).filter (fun σ =>
    ∀ K ∈ mixedFiber R σ, ∃ e ∈ crossEdges G A B, e ∈ pairs K)

theorem activePatterns_subset {δ : ℚ} (R : EqualRegularity G δ) (A B : Finset V) :
    activePatterns R A B ⊆ mixedPatterns R :=
  Finset.filter_subset _ _

theorem activePatterns_pairwiseDisjoint {δ : ℚ} (R : EqualRegularity G δ)
    (A B : Finset V) :
    Set.PairwiseDisjoint (activePatterns R A B : Set (MixedPattern V))
      (mixedFiber R) :=
  mixedFiber_pairwiseDisjoint_of_subset R (activePatterns R A B)
    (activePatterns_subset R A B)

theorem activePatterns_biUnion_subset_items {δ : ℚ} (R : EqualRegularity G δ)
    (A B : Finset V) :
    (activePatterns R A B).biUnion (mixedFiber R) ⊆ items G := by
  intro K hK
  obtain ⟨σ, hσ, hKσ⟩ := Finset.mem_biUnion.1 hK
  exact mixedFiber_subset_items R (activePatterns_subset R A B hσ) hKσ

theorem activePatterns_biUnion_meets {δ : ℚ} (R : EqualRegularity G δ)
    (A B : Finset V) {K : Finset V}
    (hK : K ∈ (activePatterns R A B).biUnion (mixedFiber R)) :
    ∃ e ∈ crossEdges G A B, e ∈ pairs K := by
  obtain ⟨σ, hσ, hKσ⟩ := Finset.mem_biUnion.1 hK
  exact (Finset.mem_filter.1 hσ).2 K hKσ

/-- The canonical mixed K3/K4 fibres discharge the complete weighted owner
capacity condition on any family of positive-density equal-size regular pairs.
The remaining RC01 work is therefore concentration/selection, not LP capacity. -/
theorem canonical_patternCapacity {W : Type*} [Fintype W] [DecidableEq W]
    {δ : ℚ} (R : EqualRegularity G δ) (x : FracPacking G ℚ)
    (left right : W → Finset V)
    (hparts : ∀ e, Disjoint (left e) (right e) ∧
      (left e).card = R.size ∧ (right e).card = R.size)
    (hdensity : ∀ e, 0 < G.edgeDensity (left e) (right e)) :
    PaperIV.WeightedPatternCoins.PatternCapacity
      (fun e => activePatterns R (left e) (right e))
      (slotMass x R.size (mixedFiber R))
      (fun e => G.edgeDensity (left e) (right e)) := by
  apply patternCapacity_of_grouped_fibers x R.size R.size_pos (mixedFiber R)
    (fun e => activePatterns R (left e) (right e)) left right
  · intro e
    exact activePatterns_pairwiseDisjoint R (left e) (right e)
  · exact hparts
  · exact hdensity
  · intro e
    exact activePatterns_biUnion_subset_items R (left e) (right e)
  · intro e K hK
    exact activePatterns_biUnion_meets R (left e) (right e) hK

/-- Unnormalized companion of `canonical_patternCapacity`.  The denominator
is the physical pair volume `density * size^2`; this is the scale needed by
safe post-cleaning spreading. -/
theorem canonical_rawPatternCapacity {W : Type*} [Fintype W] [DecidableEq W]
    {δ : ℚ} (R : EqualRegularity G δ) (x : FracPacking G ℚ)
    (left right : W → Finset V)
    (hparts : ∀ e, Disjoint (left e) (right e) ∧
      (left e).card = R.size ∧ (right e).card = R.size)
    (hdensity : ∀ e, 0 < G.edgeDensity (left e) (right e)) :
    PaperIV.WeightedPatternCoins.PatternCapacity
      (fun e => activePatterns R (left e) (right e))
      (rawMass x (mixedFiber R))
      (fun e => G.edgeDensity (left e) (right e) * (R.size : ℚ) ^ 2) := by
  apply rawPatternCapacity_of_grouped_fibers x R.size R.size_pos (mixedFiber R)
    (fun e => activePatterns R (left e) (right e)) left right
  · intro e
    exact activePatterns_pairwiseDisjoint R (left e) (right e)
  · exact hparts
  · exact hdensity
  · intro e
    exact activePatterns_biUnion_subset_items R (left e) (right e)
  · intro e K hK
    exact activePatterns_biUnion_meets R (left e) (right e) hK

end PaperIV.RC01MixedPatterns
