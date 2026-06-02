import ErdosProblems.FiniteSumsProducts

import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Basic

/-!
# Supporting Lemmas for Finite Sums and Products

Helper lemmas and auxiliary results for the formalization.
-/

namespace ErdosProblem172

variable {A B : Finset ℕ} {r : ℕ} (χ : Coloring r)

/-! ## Pigeonhole Principle -/

lemma pigeonhole_principle {α : Type*} {s : Finset α} {r : ℕ}
    (h : s.card > r) (χ : α → Fin r) :
    ∃ i : Fin r, ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ χ a = i ∧ χ b = i := by
  classical
  have hcard : (Finset.univ : Finset (Fin r)).card < s.card := by
    simpa using h
  obtain ⟨a, ha, b, hb, hab, hχ⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to
      (s := s) (t := (Finset.univ : Finset (Fin r))) (f := χ) hcard
      (by intro x hx; simp)
  exact ⟨χ a, a, ha, b, hb, hab, rfl, hχ.symm⟩

lemma pigeonhole_on_union {α : Type*} [DecidableEq α] {s₁ s₂ : Finset α} {r : ℕ}
    (h : (s₁ ∪ s₂).card > r) (χ : α → Fin r) :
    ∃ i : Fin r, (s₁.filter (fun x => χ x = i)).Nonempty ∨ 
                  (s₂.filter (fun x => χ x = i)).Nonempty := by
  have hpos : 0 < (s₁ ∪ s₂).card := Nat.lt_of_le_of_lt (Nat.zero_le r) h
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
  rw [Finset.mem_union] at hx
  refine ⟨χ x, ?_⟩
  rcases hx with hx | hx
  · left
    exact ⟨x, by simp [hx]⟩
  · right
    exact ⟨x, by simp [hx]⟩

/-! ## Color Classes and Partitions -/

def ColorClass (χ : Coloring r) (i : Fin r) : Set ℕ :=
  {x : ℕ | χ x = i}

lemma color_partition (χ : Coloring r) :
    (Set.univ : Set ℕ) = ⋃ i : Fin r, ColorClass χ i := by
  ext x
  simp [ColorClass]

lemma color_classes_disjoint (χ : Coloring r) (i j : Fin r) (h : i ≠ j) :
    (ColorClass χ i : Set ℕ) ∩ (ColorClass χ j : Set ℕ) = ∅ := by
  ext x
  constructor
  · rintro ⟨hxi, hxj⟩
    exact False.elim (h (hxi.symm.trans hxj))
  · intro hx
    simp at hx

/-! ## Monotonicity and Containment -/

lemma fs_monotone : A ⊆ B → FS A ⊆ FS B := by
  exact fs_mono

lemma fp_monotone : A ⊆ B → FP A ⊆ FP B := by
  exact fp_mono

/-! ## Monochromaticity Lemmas -/

lemma monochromatic_iff {S : Finset ℕ} :
    IsMonochromatic χ S ↔ ∃ i : Fin r, ∀ x ∈ S, χ x = i := by
  rfl

lemma union_monochromatic_iff {S₁ S₂ : Finset ℕ} :
    IsMonochromatic χ (S₁ ∪ S₂) ↔ 
      IsMonochromatic χ S₁ ∧ IsMonochromatic χ S₂ ∧ 
      ∃ i : Fin r, ∀ x ∈ S₁ ∪ S₂, χ x = i := by
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨⟨i, ?_⟩, ⟨i, ?_⟩, ⟨i, hi⟩⟩
    · intro x hx
      exact hi x (Finset.mem_union.mpr (Or.inl hx))
    · intro x hx
      exact hi x (Finset.mem_union.mpr (Or.inr hx))
  · rintro ⟨_, _, i, hi⟩
    exact ⟨i, hi⟩

end ErdosProblem172
