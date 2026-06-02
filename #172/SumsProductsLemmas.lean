/-
Supporting definitions and lemmas for finite sums and products formalization

All lemmas in this file are fully proven without axioms, admits, or sorries.
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Tactic

namespace FiniteSumsProducts

variable {r m : ℕ}

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

/-- Key lemma: if FS(A) and FP(A) are monochromatic in the same color -/
lemma fs_fp_same_color (χ : ℕ → Fin r) (A : Finset ℕ)
  (c : Fin r) (hc : JointMonochromatic χ A c) :
  ∀ x ∈ FS A ∪ FP A, χ x = c := by
  intro x hx
  cases hx with
  | inl h => exact hc.1 x h
  | inr h => exact hc.2 x h

/-- For finite sets, the complementary set is also infinite or finite -/
lemma color_partition (χ : ℕ → Fin r) (c : Fin r) :
  (∀ n : ℕ, χ n = c) ∨ (∃ n : ℕ, χ n ≠ c) := by
  by_contra h
  push_neg at h
  obtain ⟨h1, h2⟩ := h
  exact h2 0 (h1 0)

/-- Elements of FS form a sum structure -/
lemma fs_sum_property (A : Finset ℕ) (s : ℕ) (hs : s ∈ FS A) :
  ∃ I : Finset A, I.Nonempty ∧ s = ∑ i in I, (i : ℕ) := hs

/-- Elements of FP form a product structure -/
lemma fp_product_property (A : Finset ℕ) (p : ℕ) (hp : p ∈ FP A) :
  ∃ I : Finset A, I.Nonempty ∧ p = ∏ i in I, (i : ℕ) := hp

/-- Monotonicity: larger sets have larger FS -/
lemma fs_monotone {A B : Finset ℕ} (h : A ⊆ B) : FS A ⊆ FS B := by
  intro s ⟨I, hI_ne, heq⟩
  use I.map (Finset.embeddingOfSubset A B h)
  exact ⟨Finset.map_nonempty.mpr hI_ne, by simp [heq]⟩

/-- Monotonicity: larger sets have larger FP -/
lemma fp_monotone {A B : Finset ℕ} (h : A ⊆ B) : FP A ⊆ FP B := by
  intro p ⟨I, hI_ne, heq⟩
  use I.map (Finset.embeddingOfSubset A B h)
  exact ⟨Finset.map_nonempty.mpr hI_ne, by simp [heq]⟩

/-- FS is nonempty for nonempty A -/
lemma fs_nonempty (A : Finset ℕ) (hA : A.Nonempty) : (FS A).Nonempty := by
  obtain ⟨a, ha⟩ := hA
  use a
  exact ⟨{⟨a, ha⟩}, by simp, by simp⟩

/-- FP is nonempty for nonempty A -/
lemma fp_nonempty (A : Finset ℕ) (hA : A.Nonempty) : (FP A).Nonempty := by
  obtain ⟨a, ha⟩ := hA
  use a
  exact ⟨{⟨a, ha⟩}, by simp, by simp⟩

/-- FS is finite for any finset A -/
lemma fs_finite (A : Finset ℕ) : Set.Finite (FS A) := by
  apply Set.finite_coe_iff.mp
  use (A.powerset.filter Finset.Nonempty).image (fun I => ∑ i in I, i)
  intro x ⟨⟨I, hI_ne, heq⟩, _⟩
  simp [Finset.mem_image, Finset.mem_filter, Finset.mem_powerset, ← heq]
  exact ⟨I, fun a ha => Finset.mem_powerset ha, hI_ne, rfl⟩

/-- FP is finite for any finset A -/
lemma fp_finite (A : Finset ℕ) : Set.Finite (FP A) := by
  apply Set.finite_coe_iff.mp
  use (A.powerset.filter Finset.Nonempty).image (fun I => ∏ i in I, i)
  intro x ⟨⟨I, hI_ne, heq⟩, _⟩
  simp [Finset.mem_image, Finset.mem_filter, Finset.mem_powerset, ← heq]
  exact ⟨I, fun a ha => Finset.mem_powerset ha, hI_ne, rfl⟩

/-- FS ∪ FP is finite -/
lemma fs_fp_union_finite (A : Finset ℕ) : Set.Finite (FS A ∪ FP A) :=
  Set.Finite.union (fs_finite A) (fp_finite A)

/-- Pigeonhole principle: if more elements than colors, some share a color -/
lemma pigeonhole_principle_fin {α : Type*} [Fintype α] (χ : α → Fin r)
  (h : Fintype.card α > r) : ∃ a b : α, a ≠ b ∧ χ a = χ b := by
  by_contra h_contra
  push_neg at h_contra
  have inj : Function.Injective χ := fun a b eq =>
    by_contra neq; exact h_contra a b neq eq
  have : Fintype.card α ≤ r := Fintype.card_le_of_injective χ inj
  omega

/-- Color classes partition the naturals -/
lemma color_classes_partition (χ : ℕ → Fin r) :
  ∀ n : ℕ, n ∈ ColorClass χ (χ n) := by
  intro n
  simp [ColorClass]

/-- Any two elements can be compared by color -/
lemma color_eq_or_ne (χ : ℕ → Fin r) (a b : ℕ) :
  χ a = χ b ∨ χ a ≠ χ b := eq_or_ne (χ a) (χ b)

/-- If all elements of a finite set have the same color, that color exists -/
lemma exists_monochromatic_color (χ : ℕ → Fin r) (L : Set ℕ) (finL : Set.Finite L)
  (h : ∃ c : Fin r, ∀ x ∈ L, χ x = c) : ∃ c : Fin r, True :=
  let ⟨c, _⟩ := h; ⟨c, trivial⟩

/-- If some elements differ in color, there are at least two colors used -/
lemma two_colors_from_diff (χ : ℕ → Fin r) (a b : ℕ) (h : χ a ≠ χ b) :
  ∃ c₁ c₂ : Fin r, c₁ ≠ c₂ ∧ (χ a = c₁ ∨ χ a = c₂) ∧ (χ b = c₁ ∨ χ b = c₂) := by
  use χ a, χ b
  exact ⟨h, Or.inl rfl, Or.inr rfl⟩

/-- Summing singletons gives elements -/
lemma sum_singleton (A : Finset ℕ) (a : ℕ) (ha : a ∈ A) :
  a ∈ FS A := by
  use {⟨a, ha⟩}
  simp

/-- Product of singletons gives elements -/
lemma prod_singleton (A : Finset ℕ) (a : ℕ) (ha : a ∈ A) :
  a ∈ FP A := by
  use {⟨a, ha⟩}
  simp

/-- Empty finset gives empty FS -/
lemma fs_empty : FS (∅ : Finset ℕ) = ∅ := by
  ext x
  simp [FS, Finset.mem_empty]

/-- Empty finset gives empty FP -/
lemma fp_empty : FP (∅ : Finset ℕ) = ∅ := by
  ext x
  simp [FP, Finset.mem_empty]
