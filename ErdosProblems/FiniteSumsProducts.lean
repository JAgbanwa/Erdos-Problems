import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic

/-!
# Core Definitions for Finite Sums and Products

Key definitions and lemmas for Erdős Problem 172 using Mathlib.
-/

namespace ErdosProblem172

variable {A B : Finset ℕ}

/-! ## Main Definitions -/

/-- Nonempty subsets of a finite set. -/
def nonemptySubsets (A : Finset ℕ) : Finset (Finset ℕ) :=
  A.powerset.erase ∅

/-- Finite sums of distinct elements -/
def FS (A : Finset ℕ) : Finset ℕ :=
  (nonemptySubsets A).image (fun s => s.sum id)

/-- Finite products of distinct elements -/  
def FP (A : Finset ℕ) : Finset ℕ :=
  (nonemptySubsets A).image (fun s => s.prod id)

/-- Coloring with r colors -/
def Coloring (r : ℕ) : Type := ℕ → Fin r

/-- Monochromaticity predicate -/
def IsMonochromatic (χ : Coloring r) (S : Finset ℕ) : Prop :=
  ∃ c : Fin r, ∀ x ∈ S, χ x = c

/-! ## Basic Properties -/

lemma fs_finite (A : Finset ℕ) : Finite (FS A) := by
  exact Finset.finite_toSet _

lemma fp_finite (A : Finset ℕ) : Finite (FP A) := by
  exact Finset.finite_toSet _

lemma mem_nonemptySubsets {s A : Finset ℕ} :
    s ∈ nonemptySubsets A ↔ s ⊆ A ∧ s.Nonempty := by
  rw [nonemptySubsets]
  simp only [Finset.mem_erase, Finset.mem_powerset, Finset.nonempty_iff_ne_empty]
  constructor
  · intro h
    exact ⟨h.2, h.1⟩
  · intro h
    exact ⟨h.2, h.1⟩

lemma nonemptySubsets_card (A : Finset ℕ) :
    (nonemptySubsets A).card = 2 ^ A.card - 1 := by
  simp [nonemptySubsets]

lemma fs_nonempty (h : A.Nonempty) : (FS A).Nonempty := by
  refine ⟨A.sum id, ?_⟩
  exact Finset.mem_image.mpr ⟨A, mem_nonemptySubsets.mpr ⟨fun _ hx => hx, h⟩, rfl⟩

lemma fp_nonempty (h : A.Nonempty) : (FP A).Nonempty := by
  refine ⟨A.prod id, ?_⟩
  exact Finset.mem_image.mpr ⟨A, mem_nonemptySubsets.mpr ⟨fun _ hx => hx, h⟩, rfl⟩

/-! ## Monotonicity -/

lemma fs_mono : A ⊆ B → FS A ⊆ FS B := by
  intro hAB x hx
  rcases Finset.mem_image.mp hx with ⟨s, hs, rfl⟩
  exact Finset.mem_image.mpr
    ⟨s, mem_nonemptySubsets.mpr ⟨fun a ha => hAB ((mem_nonemptySubsets.mp hs).1 ha),
      (mem_nonemptySubsets.mp hs).2⟩, rfl⟩

lemma fp_mono : A ⊆ B → FP A ⊆ FP B := by
  intro hAB x hx
  rcases Finset.mem_image.mp hx with ⟨s, hs, rfl⟩
  exact Finset.mem_image.mpr
    ⟨s, mem_nonemptySubsets.mpr ⟨fun a ha => hAB ((mem_nonemptySubsets.mp hs).1 ha),
      (mem_nonemptySubsets.mp hs).2⟩, rfl⟩

end ErdosProblem172
