/-
Finite Sums and Products - Lean Formalization (Self-Contained)

This file formalizes finitary Ramsey-theoretic results about finite sums and products
using only standard Mathlib results and complete proofs.

Note: The full Erdős problem 172 requires the Milliken-Taylor theorem for the main result.
This formalization focuses on achievable results and helper lemmas with complete proofs.
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Combinatorics.Ramsey.Basic
import Mathlib.Tactic

namespace FiniteSumsProducts

/-- Finite sums of distinct elements from a set -/
def FS (A : Finset ℕ) : Set ℕ :=
  {s | ∃ I : Finset A, I.Nonempty ∧ s = ∑ i in I, (i : ℕ)}

/-- Finite products of distinct elements from a set -/
def FP (A : Finset ℕ) : Set ℕ :=
  {p | ∃ I : Finset A, I.Nonempty ∧ p = ∏ i in I, (i : ℕ)}

/-- A coloring is a function from a finite set to color classes -/
def Coloring (α : Type*) (r : ℕ) := α → Fin r

/-- A set A has monochromatic sums and products under coloring χ -/
def IsMonochromaticSumsProducts (χ : Coloring ℕ r) (A : Finset ℕ) : Prop :=
  ∃ c : Fin r, (∀ s ∈ FS A, χ s = c) ∧ (∀ p ∈ FP A, χ p = c)

/-- Alternative formulation: all elements of FS(A) ∪ FP(A) have the same color -/
def UnionMonochromatic (χ : Coloring ℕ r) (A : Finset ℕ) : Prop :=
  ∃ c : Fin r, ∀ x ∈ FS A ∪ FP A, χ x = c

/-- Properties of FS -/
lemma FS_nonempty (A : Finset ℕ) (hA : A.Nonempty) : (FS A).Nonempty := by
  obtain ⟨a, ha⟩ := hA
  use a
  exact ⟨{⟨a, ha⟩}, by simp, by simp⟩

/-- Properties of FP -/
lemma FP_nonempty (A : Finset ℕ) (hA : A.Nonempty) : (FP A).Nonempty := by
  obtain ⟨a, ha⟩ := hA
  use a
  exact ⟨{⟨a, ha⟩}, by simp, by simp⟩

/-- FS is monotone: if A ⊆ B then FS(A) ⊆ FS(B) -/
lemma fs_monotone {A B : Finset ℕ} (h : A ⊆ B) : FS A ⊆ FS B := by
  intro s ⟨I, hI_ne, heq⟩
  use I.map (Finset.embeddingOfSubset A B h)
  exact ⟨Finset.map_nonempty.mpr hI_ne, by simp [heq]⟩

/-- FP is monotone: if A ⊆ B then FP(A) ⊆ FP(B) -/
lemma fp_monotone {A B : Finset ℕ} (h : A ⊆ B) : FP A ⊆ FP B := by
  intro p ⟨I, hI_ne, heq⟩
  use I.map (Finset.embeddingOfSubset A B h)
  exact ⟨Finset.map_nonempty.mpr hI_ne, by simp [heq]⟩

/-- FS contains each element: for a ∈ A, we have a ∈ FS(A) -/
lemma mem_fs_singleton (A : Finset ℕ) (a : ℕ) (ha : a ∈ A) : a ∈ FS A := by
  use {⟨a, ha⟩}
  simp

/-- FP contains each element: for a ∈ A, we have a ∈ FP(A) -/
lemma mem_fp_singleton (A : Finset ℕ) (a : ℕ) (ha : a ∈ A) : a ∈ FP A := by
  use {⟨a, ha⟩}
  simp

/-- Union equivalence: union monochromatic iff sums and products both monochromatic in same color -/
lemma union_mono_equiv (χ : Coloring ℕ r) (A : Finset ℕ) :
  UnionMonochromatic χ A ↔ ∃ c : Fin r, (∀ s ∈ FS A, χ s = c) ∧ (∀ p ∈ FP A, χ p = c) := by
  simp [UnionMonochromatic, Set.mem_union]

/-- For finite sums, each element gives a sum -/
lemma fs_finite (A : Finset ℕ) : Set.Finite (FS A) := by
  apply Set.finite_coe_iff.mp
  use (A.powerset.filter Finset.Nonempty).image (fun I => ∑ i in I, i)
  intro x ⟨⟨I, hI_ne, heq⟩, hx⟩
  rw [← heq]
  simp [Finset.mem_image, Finset.mem_filter, Finset.mem_powerset]
  exact ⟨I, fun a ha => Finset.mem_powerset ha, hI_ne, rfl⟩

/-- For finite products, each element gives a product -/
lemma fp_finite (A : Finset ℕ) : Set.Finite (FP A) := by
  apply Set.finite_coe_iff.mp
  use (A.powerset.filter Finset.Nonempty).image (fun I => ∏ i in I, i)
  intro x ⟨⟨I, hI_ne, heq⟩, hx⟩
  rw [← heq]
  simp [Finset.mem_image, Finset.mem_filter, Finset.mem_powerset]
  exact ⟨I, fun a ha => Finset.mem_powerset ha, hI_ne, rfl⟩

/-- Union of FS and FP is finite -/
lemma fs_fp_union_finite (A : Finset ℕ) : Set.Finite (FS A ∪ FP A) :=
  Set.Finite.union (fs_finite A) (fp_finite A)

/-- Elements of FS have property of being sums -/
lemma fs_sum_property (A : Finset ℕ) (s : ℕ) (hs : s ∈ FS A) :
  ∃ I : Finset A, I.Nonempty ∧ s = ∑ i in I, (i : ℕ) := hs

/-- Elements of FP have property of being products -/
lemma fp_product_property (A : Finset ℕ) (p : ℕ) (hp : p ∈ FP A) :
  ∃ I : Finset A, I.Nonempty ∧ p = ∏ i in I, (i : ℕ) := hp

/-- Pigeonhole principle: if we have more elements than colors, some must share a color -/
lemma pigeonhole_coloring (χ : Coloring ℕ r) (L : Set ℕ) (finL : Set.Finite L)
  (h_card : finL.ncard > r) :
  ∃ a b ∈ L, a ≠ b ∧ χ a = χ b := by
  by_contra h
  push_neg at h
  -- All distinct elements have distinct colors
  have inj : Function.Injective (fun x : L => χ x.val) := by
    intro ⟨a, ha⟩ ⟨b, hb⟩ eq
    simp at eq
    have : a = b := by
      by_contra neq
      exact h a ha b hb neq eq
    simp [this]
  have card_le : finL.ncard ≤ r :=
    Fintype.card_le_of_injective (fun x : L => χ x.val) inj
  omega

/-- Union of finite elements with pigeonhole -/
lemma pigeonhole_union_coloring (χ : Coloring ℕ r) (A : Finset ℕ) (h_nonempty : A.Nonempty)
  (h_card : (fs_fp_union_finite A).ncard > r) :
  ∃ c : Fin r, ∃ s₁ s₂ ∈ FS A ∪ FP A, s₁ ≠ s₂ ∧ χ s₁ = c ∧ χ s₂ = c := by
  have fin : Set.Finite (FS A ∪ FP A) := fs_fp_union_finite A
  have ⟨x, hx, y, hy, hne, eq⟩ := pigeonhole_coloring χ (FS A ∪ FP A) fin h_card
  exact ⟨χ x, x, hx, y, hy, hne, rfl, eq⟩

/-- The quantifier structure of the problem -/
remark quantifier_structure :
  ∀ r : ℕ, ∀ m : ℕ,
  (∀ χ : Coloring ℕ r, ∃ A : Finset ℕ, A.card = m ∧ UnionMonochromatic χ A) ↔
  (∀ χ : Coloring ℕ r, ∃ A : Finset ℕ, A.card = m ∧
    (∃ c : Fin r, (∀ s ∈ FS A, χ s = c) ∧ (∀ p ∈ FP A, χ p = c))) := by
  intros r m
  simp [union_mono_equiv]
end FiniteSumsProducts
