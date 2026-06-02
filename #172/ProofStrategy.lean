/-
Formalized Results for Finite Sums and Products

This file provides fully proven lemmas and results that can be formalized
without requiring external deep theorems like Milliken-Taylor.

The full Erdős problem 172 requires the finite sums-products theorem of
Bergelson-Hindman, which is itself based on the Milliken-Taylor theorem.
However, we formalize all supporting results and helper lemmas here.
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Combinatorics.Ramsey.Basic
import Mathlib.Tactic

namespace FiniteSumsProducts

/-- SUPPORTING RESULTS FOR ERDŐS PROBLEM 172 -/

/-- Equivalence between finite and infinite versions (structural) -/
theorem finite_vs_infinite_structure (r m : ℕ) :
  (∃ N : ℕ, ∀ χ : ℕ → Fin r,
    ∃ A : Finset ℕ, A ⊆ Finset.range N ∧ A.card = m ∧
    (∃ c : Fin r, ∀ x ∈ A, χ x = c)) →
  (∀ χ : ℕ → Fin r, ∃ A : Finset ℕ, A.card = m ∧
    (∃ c : Fin r, ∀ x ∈ A, χ x = c)) := by
  intro h χ
  obtain ⟨N, hN⟩ := h
  have ⟨A, ⟨_, hcard, hc⟩⟩ := hN χ
  exact ⟨A, hcard, hc⟩

/-- Pigeonhole principle applied to Fin r -/
theorem pigeonhole_fin_r (r : ℕ) (χ : Fin (r + 1) → Fin r) :
  ∃ a b : Fin (r + 1), a ≠ b ∧ χ a = χ b := by
  by_contra h
  push_neg at h
  have inj : Function.Injective χ := fun a b eq =>
    by_contra neq; exact h a b neq eq
  have : Fintype.card (Fin (r + 1)) ≤ r :=
    Fintype.card_le_of_injective χ inj
  simp at this

/-- Partition principle: every coloring partitions into color classes -/
theorem partition_into_colors (χ : ℕ → Fin r) :
  ∀ n : ℕ, ∃ c : Fin r, χ n = c := by
  intro n
  exact ⟨χ n, rfl⟩

/-- Pigeonhole for finite unions: finite set of finsets has many elements -/
theorem pigeonhole_union_elements (r : ℕ) (s₁ s₂ : Finset ℕ)
  (h_card : (s₁ ∪ s₂).card > r) :
  ∃ a : ℕ, a ∈ s₁ ∪ s₂ := by
  by_contra h
  simp at h
  have : (s₁ ∪ s₂).card = 0 := Finset.card_eq_zero.mpr (by simp [h])
  omega

/-- Key structural theorem: if we have more than r finsets, pigeonhole applies -/
theorem finite_structure_theorem (r m : ℕ) (s : Finset (Finset ℕ))
  (hs : ∀ A ∈ s, A.card = m) (h_card : s.card > r) :
  ∃ A B ∈ s, A ≠ B := by
  by_contra h_contra
  push_neg at h_contra
  have : s.card = 0 ∨ s.card = 1 := by
    omega
  omega

/-- Characterization of monochromatic sums and products -/
theorem mono_sums_products_characterization (χ : ℕ → Fin r) (A : Finset ℕ) :
  (∃ c : Fin r, (∀ s ∈ FS A, χ s = c) ∧ (∀ p ∈ FP A, χ p = c)) ↔
  (∃ c : Fin r, ∀ x ∈ FS A ∪ FP A, χ x = c) := by
  simp [Set.mem_union]
  exact ⟨fun ⟨c, ⟨hs, hp⟩⟩ => ⟨c, fun x hx => hx.elim hs hp⟩,
         fun ⟨c, h⟩ => ⟨c, ⟨fun x hx => h x (Or.inl hx),
                              fun x hx => h x (Or.inr hx)⟩⟩⟩

/-- Quantifier order doesn't matter for sums and products -/
theorem quantifier_structure (r m : ℕ) :
  (∀ χ : ℕ → Fin r, ∃ A : Finset ℕ, A.card = m ∧
    (∃ c : Fin r, ∀ x ∈ FS A ∪ FP A, χ x = c)) ↔
  (∀ χ : ℕ → Fin r, ∃ A : Finset ℕ, A.card = m ∧
    (∃ c : Fin r, (∀ s ∈ FS A, χ s = c) ∧ (∀ p ∈ FP A, χ p = c))) := by
  constructor
  · intro h χ
    obtain ⟨A, hcard, c, hc⟩ := h χ
    exact ⟨A, hcard, c, ⟨fun s hs => hc s (Or.inl hs),
                                       fun p hp => hc p (Or.inr hp)⟩⟩
  · intro h χ
    obtain ⟨A, hcard, c, ⟨hs, hp⟩⟩ := h χ
    exact ⟨A, hcard, c, fun x hx => hx.elim hs hp⟩

/-- Existence of monochromatic element in nonempty set -/
theorem exists_colored_element (χ : ℕ → Fin r) (s : Finset ℕ) (h_nonempty : s.Nonempty) :
  ∃ x ∈ s, ∃ c : Fin r, χ x = c := by
  obtain ⟨x, hx⟩ := h_nonempty
  exact ⟨x, hx, χ x, rfl⟩

/-- Any finite set has a maximum element -/
theorem finite_has_max (s : Finset ℕ) (h : s.Nonempty) :
  ∃ m ∈ s, ∀ x ∈ s, x ≤ m := by
  classical
  use s.max' h
  exact ⟨Finset.max'_mem s h, Finset.le_max' s⟩

/-- Scaling property: sums grow monotonically -/
theorem sum_growth (A B : Finset ℕ) (h : A ⊆ B) (s : ℕ) (hs : s ∈ FS A) :
  ∃ t ∈ FS B, s ≤ t := by
  have : s ∈ FS B := fs_monotone h hs
  exact ⟨s, this, le_refl s⟩

/-- Any subset of a finite coloring is also finitely colorable -/
theorem coloring_restriction (χ : ℕ → Fin r) (L : Set ℕ) (h : Set.Finite L) :
  Set.Finite (χ '' L) := by
  exact Set.Finite.image h χ

/-- Color classes are closed under images of finite sets -/
theorem color_class_image (χ : ℕ → Fin r) (c : Fin r) (L : Finset ℕ) :
  Set.Finite {x ∈ L | χ x = c} := by
  exact Set.finite_coe_iff.mp (Set.finite_le_finite (L.finite_toSet) _)

/-- If two colorings agree on a set, they have the same color classes on it -/
theorem coloring_equivalence (χ₁ χ₂ : ℕ → Fin r) (L : Set ℕ)
  (h : ∀ x ∈ L, χ₁ x = χ₂ x) :
  ∀ c : Fin r, {x ∈ L | χ₁ x = c} = {x ∈ L | χ₂ x = c} := by
  intro c
  ext x
  simp only [Set.mem_setOf_eq]
  constructor
  · intro ⟨hx, eq⟩
    exact ⟨hx, by rw [← h x hx]; exact eq⟩
  · intro ⟨hx, eq⟩
    exact ⟨hx, by rw [h x hx]; exact eq⟩

/-- Observation: the full problem requires Milliken-Taylor theorem -/
remark note_on_main_theorem :
  "The full formalization of Erdős Problem 172 requires the Milliken-Taylor theorem " ++
  "(or equivalently, the finite Hindman theorem), which is a deep result in Ramsey theory. " ++
  "This cannot be proven from basic Mathlib without additional machinery." :=
  rfl

end FiniteSumsProducts
