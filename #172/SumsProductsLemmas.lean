/-
Supporting definitions and lemmas for finite sums and products formalization
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Tactic

namespace FiniteSumsProducts

variable {r m : ℕ}

/-- Alternative characterization: all elements of FS(A) ∪ FP(A) are monochromatic -/
def UnionMonochromatic (χ : ℕ → Fin r) (A : Finset ℕ) : Prop :=
  ∃ c : Fin r, ∀ x ∈ FS A ∪ FP A, χ x = c

/-- A set is m-sized if it has exactly m elements -/
def IsMSized (A : Finset ℕ) (m : ℕ) : Prop := A.card = m

/-- The coloring induces a partition of ℕ into color classes -/
def ColorClass (χ : ℕ → Fin r) (c : Fin r) : Set ℕ :=
  {n | χ n = c}

/-- FS(A) is contained in a single color class -/
def FSMonochromatic (χ : ℕ → Fin r) (A : Finset ℕ) (c : Fin r) : Prop :=
  ∀ s ∈ FS A, χ s = c

/-- FP(A) is contained in a single color class -/
def FPMonochromatic (χ : ℕ → Fin r) (A : Finset ℕ) (c : Fin r) : Prop :=
  ∀ p ∈ FP A, χ p = c

/-- Both FS(A) and FP(A) are in the same color class -/
def JointMonochromatic (χ : ℕ → Fin r) (A : Finset ℕ) (c : Fin r) : Prop :=
  FSMonochromatic χ A c ∧ FPMonochromatic χ A c

lemma union_monochromatic_iff_joint (χ : ℕ → Fin r) (A : Finset ℕ) :
  UnionMonochromatic χ A ↔ ∃ c : Fin r, JointMonochromatic χ A c := by
  simp [UnionMonochromatic, JointMonochromatic, FSMonochromatic, FPMonochromatic, Set.mem_union]

/-- Key lemma: if FS(A) and FP(A) are both nonempty and monochromatic in the same color -/
lemma fs_fp_same_color (χ : ℕ → Fin r) (A : Finset ℕ) (hA : A.Nonempty)
  (c : Fin r) (hc : JointMonochromatic χ A c) :
  ∀ x ∈ FS A ∪ FP A, χ x = c := by
  intro x hx
  cases hx with
  | inl h => exact hc.1 x h
  | inr h => exact hc.2 x h

/-- Pigeonhole principle for colorings:
    Among any r+1 elements, at least two have the same color -/
lemma pigeonhole_coloring (χ : ℕ → Fin r) (L : Finset ℕ) (hL : L.card ≥ r + 1) :
  ∃ a b ∈ L, a ≠ b ∧ χ a = χ b := by
  sorry

/-- Existence of infinite monochromatic subsequence (Infinite Ramsey for 2-colorings) -/
lemma infinite_ramsey_two_color (χ : ℕ → Fin 2) :
  ∃ c : Fin 2, {n | χ n = c}.Infinite := by
  sorry

/-- For each color, infinitely many natural numbers have that color (in the infinite case) -/
lemma infinite_color_class (χ : ℕ → Fin r) (c : Fin r) :
  {n | χ n = c}.Infinite ∨ {n | χ n ≠ c}.Infinite := by
  by_contra h
  push_neg at h
  have : Set.Finite {n | χ n = c} := Set.finite_coe_iff.mp h.1
  have : Set.Finite {n | χ n ≠ c} := Set.finite_coe_iff.mp h.2
  sorry

/-- Elements of FS form a sum structure -/
lemma fs_sum_property (A : Finset ℕ) (s : ℕ) (hs : s ∈ FS A) :
  ∃ I : Finset A, I.Nonempty ∧ s = ∑ i in I, (i : ℕ) := by
  exact hs

/-- Elements of FP form a product structure -/
lemma fp_product_property (A : Finset ℕ) (p : ℕ) (hp : p ∈ FP A) :
  ∃ I : Finset A, I.Nonempty ∧ p = ∏ i in I, (i : ℕ) := by
  exact hp

/-- Monotonicity: larger sets have larger FS and FP -/
lemma fs_monotone {A B : Finset ℕ} (h : A ⊆ B) : FS A ⊆ FS B := by
  intro s ⟨I, hI_ne, heq⟩
  use I.map (Finset.embeddingOfSubset A B h)
  constructor
  · exact Finset.map_nonempty.mpr hI_ne
  · simp [heq]

lemma fp_monotone {A B : Finset ℕ} (h : A ⊆ B) : FP A ⊆ FP B := by
  intro p ⟨I, hI_ne, heq⟩
  use I.map (Finset.embeddingOfSubset A B h)
  constructor
  · exact Finset.map_nonempty.mpr hI_ne
  · simp [heq]

/-- Distinctness in FS: sums from different subsets are equal only in special cases -/
lemma fs_injectivity_condition (A : Finset ℕ) (h_distinct : ∀ i ∈ A, i ≥ 1) :
  ∀ I J : Finset A, I ≠ ∅ → J ≠ ∅ →
  (∑ i in I, (i : ℕ)) = (∑ j in J, (j : ℕ)) → I = J := by
  sorry

end FiniteSumsProducts
