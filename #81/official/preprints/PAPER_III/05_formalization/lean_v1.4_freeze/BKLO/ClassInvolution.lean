/-
# Gluing matchings into a fixed-point-free involution.

The pairing of one link of a class-matched sweep is assembled from matchings between *pairs of
classes* of the link's region (`BKLO.exists_class_matching_avoiding` produces one such matching) and
from pairings *inside* a class.  Turning that data into the single function `p` a sweep step has to
produce — an involution of the link without fixed points, all of whose pairs satisfy a prescribed
relation (an edge of `F` outside the forbidden set) — is a purely combinatorial step, and it is
proved here once and for all.

* `BKLO.exists_swap_involution` — a bijection between two **disjoint** sets becomes an involution of
  their union: `p` is the bijection on one side and its inverse on the other, and it has no fixed
  point;
* `BKLO.exists_involution_biUnion` — involutions of the blocks of a **disjoint** family glue to an
  involution of the union, carrying any relation of the pairs along.

Everything here is `sorry`-free.
-/
import BKLO.Basic

open Finset

namespace BKLO

variable {V : Type*} [DecidableEq V]

/-- **A bijection between two disjoint sets is half of an involution.**  If `f` maps `A`
injectively into `B` and the two sets have the same size, then the function that is `f` on `A`, its
inverse on `B`, and the identity elsewhere is an involution of `A ∪ B` without fixed points, whose
pairs are the pairs of `f`. -/
theorem exists_swap_involution {A B : Finset V} (hdisj : Disjoint A B)
    {f : V → V} (hmaps : ∀ a ∈ A, f a ∈ B) (hinj : Set.InjOn f ↑A) (hcard : A.card = B.card)
    (r : V → V → Prop) (hsymm : ∀ a b, r a b → r b a) (hr : ∀ a ∈ A, r a (f a)) :
    ∃ p : V → V, (∀ a ∈ A, p a = f a) ∧ (∀ z ∈ A ∪ B, p z ∈ A ∪ B) ∧
      (∀ z ∈ A ∪ B, p (p z) = z) ∧ (∀ z ∈ A ∪ B, p z ≠ z) ∧
      (∀ z ∈ A ∪ B, r z (p z)) := by
  classical
  -- `f` is onto `B`
  have himg : A.image f = B := by
    refine Finset.eq_of_subset_of_card_le (fun b hb => ?_) ?_
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hb
      exact hmaps a ha
    · rw [Finset.card_image_of_injOn hinj, hcard]
  have hsurj : ∀ b ∈ B, ∃ a ∈ A, f a = b := by
    intro b hb
    rw [← himg] at hb
    obtain ⟨a, ha, hfa⟩ := Finset.mem_image.1 hb
    exact ⟨a, ha, hfa⟩
  -- the inverse of `f`
  set g : V → V := fun b => if h : ∃ a ∈ A, f a = b then h.choose else b with hgdef
  have hg : ∀ b ∈ B, g b ∈ A ∧ f (g b) = b := by
    intro b hb
    have hex : ∃ a ∈ A, f a = b := hsurj b hb
    have : g b = hex.choose := by
      rw [hgdef]
      simp only [dif_pos hex]
    rw [this]
    exact ⟨hex.choose_spec.1, hex.choose_spec.2⟩
  refine ⟨fun z => if z ∈ A then f z else if z ∈ B then g z else z, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha
    simp [ha]
  · intro z hz
    rcases Finset.mem_union.1 hz with hzA | hzB
    · simp only [if_pos hzA]
      exact Finset.mem_union_right _ (hmaps z hzA)
    · have hzA : z ∉ A := fun h => (Finset.disjoint_left.1 hdisj) h hzB
      simp only [if_neg hzA, if_pos hzB]
      exact Finset.mem_union_left _ (hg z hzB).1
  · intro z hz
    rcases Finset.mem_union.1 hz with hzA | hzB
    · have hfzB : f z ∈ B := hmaps z hzA
      have hfzA : f z ∉ A := fun h => (Finset.disjoint_left.1 hdisj) h hfzB
      simp only [if_pos hzA, if_neg hfzA, if_pos hfzB]
      -- both `z` and `g (f z)` are preimages of `f z`
      have h1 := hg (f z) hfzB
      exact hinj (by exact_mod_cast h1.1) (by exact_mod_cast hzA) h1.2
    · have hzA : z ∉ A := fun h => (Finset.disjoint_left.1 hdisj) h hzB
      have h1 := hg z hzB
      simp only [if_neg hzA, if_pos hzB, if_pos h1.1]
      exact h1.2
  · intro z hz
    rcases Finset.mem_union.1 hz with hzA | hzB
    · simp only [if_pos hzA]
      intro hcon
      exact (Finset.disjoint_left.1 hdisj) hzA (hcon ▸ hmaps z hzA)
    · have hzA : z ∉ A := fun h => (Finset.disjoint_left.1 hdisj) h hzB
      have h1 := hg z hzB
      simp only [if_neg hzA, if_pos hzB]
      intro hcon
      exact (Finset.disjoint_left.1 hdisj) (hcon ▸ h1.1) hzB
  · intro z hz
    rcases Finset.mem_union.1 hz with hzA | hzB
    · simp only [if_pos hzA]
      exact hr z hzA
    · have hzA : z ∉ A := fun h => (Finset.disjoint_left.1 hdisj) h hzB
      have h1 := hg z hzB
      simp only [if_neg hzA, if_pos hzB]
      have h2 : r (g z) z := by
        have := hr (g z) h1.1
        rwa [h1.2] at this
      exact hsymm _ _ h2

/-- **Involutions of disjoint blocks glue.**  If each block `T i` of a disjoint family carries an
involution `p i` without fixed points whose pairs satisfy `r`, then their union carries one. -/
theorem exists_involution_biUnion {ι : Type*} [DecidableEq ι] (I : Finset ι) (T : ι → Finset V)
    (p : ι → V → V) (r : V → V → Prop)
    (hdisj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (T i) (T j))
    (hmaps : ∀ i ∈ I, ∀ z ∈ T i, p i z ∈ T i)
    (hinv : ∀ i ∈ I, ∀ z ∈ T i, p i (p i z) = z)
    (hne : ∀ i ∈ I, ∀ z ∈ T i, p i z ≠ z)
    (hr : ∀ i ∈ I, ∀ z ∈ T i, r z (p i z)) :
    ∃ P : V → V, (∀ i ∈ I, ∀ z ∈ T i, P z = p i z) ∧
      (∀ z ∈ I.biUnion T, P z ∈ I.biUnion T) ∧
      (∀ z ∈ I.biUnion T, P (P z) = z) ∧
      (∀ z ∈ I.biUnion T, P z ≠ z) ∧
      (∀ z ∈ I.biUnion T, r z (P z)) := by
  classical
  set P : V → V := fun z => if h : ∃ i ∈ I, z ∈ T i then p h.choose z else z with hPdef
  -- the block of a point of the union is unique
  have hblock : ∀ z ∈ I.biUnion T, ∃ i ∈ I, z ∈ T i ∧ P z = p i z := by
    intro z hz
    have hex : ∃ i ∈ I, z ∈ T i := by
      obtain ⟨i, hi, hzi⟩ := Finset.mem_biUnion.1 hz
      exact ⟨i, hi, hzi⟩
    refine ⟨hex.choose, hex.choose_spec.1, hex.choose_spec.2, ?_⟩
    rw [hPdef]
    simp only [dif_pos hex]
  have hPeq : ∀ i ∈ I, ∀ z ∈ T i, P z = p i z := by
    intro i hi z hz
    have hzU : z ∈ I.biUnion T := Finset.mem_biUnion.2 ⟨i, hi, hz⟩
    obtain ⟨j, hj, hzj, hPz⟩ := hblock z hzU
    by_cases hij : i = j
    · rw [hPz, hij]
    · exact absurd hzj (Finset.disjoint_left.1 (hdisj i hi j hj hij) hz)
  refine ⟨P, hPeq, ?_, ?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨i, hi, hzi, hPz⟩ := hblock z hz
    rw [hPz]
    exact Finset.mem_biUnion.2 ⟨i, hi, hmaps i hi z hzi⟩
  · intro z hz
    obtain ⟨i, hi, hzi, hPz⟩ := hblock z hz
    rw [hPz, hPeq i hi (p i z) (hmaps i hi z hzi)]
    exact hinv i hi z hzi
  · intro z hz
    obtain ⟨i, hi, hzi, hPz⟩ := hblock z hz
    rw [hPz]
    exact hne i hi z hzi
  · intro z hz
    obtain ⟨i, hi, hzi, hPz⟩ := hblock z hz
    rw [hPz]
    exact hr i hi z hzi

end BKLO
