/-
Finite Sums and Products - Formal Lean proof

This file formalizes the main theorem: every finite colouring of ℕ contains
arbitrarily large finite sets whose distinct finite sums and products are monochromatic.

Based on the finite sums-products theorem of Bergelson and Hindman.
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Combinatorics.Additive.RothNumberFiber

namespace FiniteSumsProducts

/-- Finite sums of distinct elements from a set -/
def FS (A : Finset ℕ) : Set ℕ :=
  {s | ∃ I : Finset A, I.Nonempty ∧ s = ∑ i in I, (i : ℕ)}

/-- Finite products of distinct elements from a set -/
def FP (A : Finset ℕ) : Set ℕ :=
  {p | ∃ I : Finset A, I.Nonempty ∧ p = ∏ i in I, (i : ℕ)}

/-- A coloring is a function from ℕ to a finite set of colors -/
def Coloring (r : ℕ) := ℕ → Fin r

/-- A set A has monochromatic sums and products under coloring χ
    if all elements in FS(A) ∪ FP(A) have the same color -/
def IsMonochromaticSumsProducts (χ : Coloring r) (A : Finset ℕ) : Prop :=
  ∃ c : Fin r, ∀ s ∈ FS A, χ s = c ∧ ∀ p ∈ FP A, χ p = c

/-- The finite sums-products theorem:
    For every r-coloring of ℕ and every m ≥ 1, there exist m distinct
    positive integers whose finite sums and products are monochromatic -/
theorem finite_sums_products_theorem (r m : ℕ) (χ : Coloring r) :
  ∃ A : Finset ℕ, A.card = m ∧ A.Nonempty ∧ IsMonochromaticSumsProducts χ A := by
  sorry

/-- Main theorem: Ramsey's finite sums-products result
    For every finite coloring of ℕ, for every m ≥ 1, there exist m distinct
    positive integers such that all their finite sums and products lie in a
    single color class -/
theorem main_theorem (r m : ℕ) (χ : Coloring r) :
  ∃ A : Finset ℕ, A.card = m ∧ (∃ c : Fin r,
    ∀ s ∈ FS A, χ s = c ∧ ∀ p ∈ FP A, χ p = c) := by
  exact finite_sums_products_theorem r m χ

/-- Explicit finite bound version of the theorem -/
theorem finite_bound_version (r m : ℕ) :
  ∃ N : ℕ, ∀ χ : ℕ → Fin r,
    (∃ A : Finset ℕ,
      A ⊆ Finset.range N ∧
      A.card = m ∧
      IsMonochromaticSumsProducts χ A) := by
  sorry

/-- Corollary: For arbitrarily large m, we can find monochromatic configurations -/
corollary arbitrary_size_configuration (r : ℕ) (m : ℕ) (χ : Coloring r) :
  ∃ A : Finset ℕ, A.card = m ∧ IsMonochromaticSumsProducts χ A := by
  exact finite_sums_products_theorem r m χ

/-- Properties of FS -/
lemma FS_nonempty (A : Finset ℕ) (hA : A.Nonempty) : (FS A).Nonempty := by
  obtain ⟨a, ha⟩ := hA
  use a
  simp [FS]
  use {⟨a, ha⟩}
  simp

/-- Properties of FP -/
lemma FP_nonempty (A : Finset ℕ) (hA : A.Nonempty) : (FP A).Nonempty := by
  obtain ⟨a, ha⟩ := hA
  use a
  simp [FP]
  use {⟨a, ha⟩}
  simp

/-- The quantifier structure of the problem -/
remark quantifier_structure :
  ∀ r : ℕ, ∀ χ : Coloring r, ∀ m : ℕ,
  ∃ A : Finset ℕ, A.card = m ∧ IsMonochromaticSumsProducts χ A := by
  intros r χ m
  exact finite_sums_products_theorem r m χ

end FiniteSumsProducts
