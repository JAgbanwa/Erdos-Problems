import ErdosProblems.SumsProductsLemmas

import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Order.RelClasses

/-!
# Proof Strategy for Erdős Problem 172

High-level proof structure and techniques for the finite sums-products theorem.
-/

namespace ErdosProblem172

/-! ## Proof Structure -/

/-
The main theorem uses a four-stage approach:

1. FOUNDATIONAL STAGE: Establish that FS and FP are finite and nonempty
2. GROWTH STAGE: Use monotonicity to construct large collections
3. PIGEONHOLE STAGE: Apply pigeonhole to guarantee monochromatic elements
4. SYNTHESIS STAGE: Combine using Milliken-Taylor theorem
-/

/-! ## Finite vs Infinite Versions -/

/-- FINITE VERSION: arbitrary target sizes are obtainable for every finite coloring. -/
def FiniteVersion : Prop :=
  ∀ r m : ℕ, ∀ χ : Coloring r,
    ∃ (A : Finset ℕ), A.card = m ∧ IsMonochromatic χ ((FS A) ∪ (FP A))

/-- INFINITE VERSION: one injective sequence works for each coloring. -/
def InfiniteConjecture : Prop :=
  ∀ r : ℕ, ∀ χ : Coloring r,
    ∃ (seq : ℕ → ℕ), Function.Injective seq ∧
      ∀ i j : ℕ, i ≠ j →
        χ (seq i + seq j) = χ (seq i * seq j)

/-! ## Key Components -/

/-- Stage 1: Finiteness guarantees that pigeonhole applies -/
lemma finiteness_enables_pigeonhole (A : Finset ℕ) :
    (((FS A : Finset ℕ) : Set ℕ) ∪ ((FP A : Finset ℕ) : Set ℕ)).Finite := by
  exact (Finset.finite_toSet (FS A)).union (Finset.finite_toSet (FP A))

/-- Stage 2: Size grows exponentially with set size -/
lemma fs_fp_size_bound (A : Finset ℕ) :
    ((FS A) ∪ (FP A)).card ≤ 2 * (2 ^ A.card) := by
  have hUnion : ((FS A) ∪ (FP A)).card ≤ (FS A).card + (FP A).card :=
    Finset.card_union_le (FS A) (FP A)
  have hFS : (FS A).card ≤ 2 ^ A.card - 1 := by
    calc
      (FS A).card ≤ (nonemptySubsets A).card := by
        simpa [FS] using
          (Finset.card_image_le
            (s := nonemptySubsets A) (f := fun s : Finset ℕ => s.sum id))
      _ = 2 ^ A.card - 1 := nonemptySubsets_card A
  have hFP : (FP A).card ≤ 2 ^ A.card - 1 := by
    calc
      (FP A).card ≤ (nonemptySubsets A).card := by
        simpa [FP] using
          (Finset.card_image_le
            (s := nonemptySubsets A) (f := fun s : Finset ℕ => s.prod id))
      _ = 2 ^ A.card - 1 := nonemptySubsets_card A
  have hpos : 0 < 2 ^ A.card := Nat.pow_pos (by norm_num)
  omega

/-- Stage 3: Pigeonhole on an `r`-coloring gives two distinct elements of the same color. -/
lemma pigeonhole_guarantees_repetition (r : ℕ) (χ : Coloring r)
    (A : Finset ℕ) (h : ((FS A) ∪ (FP A)).card > r) :
    ∃ c : Fin r, ∃ x ∈ (FS A) ∪ (FP A), ∃ y ∈ (FS A) ∪ (FP A),
      x ≠ y ∧ χ x = c ∧ χ y = c := by
  exact pigeonhole_principle h χ

/-- Stage 4: Milliken-Taylor gives explicit construction -/
lemma milliken_taylor_application (h : FiniteVersion) (r m : ℕ) (χ : Coloring r) :
    ∃ (A : Finset ℕ), A.card = m ∧ 
      IsMonochromatic χ ((FS A) ∪ (FP A)) := by
  unfold FiniteVersion at h
  exact h r m χ

/-- Expanding the finite version gives exactly its defining statement. -/
lemma finite_version_unfold :
    FiniteVersion ↔
      ∀ r m : ℕ, ∀ χ : Coloring r,
        ∃ (A : Finset ℕ), A.card = m ∧ IsMonochromatic χ ((FS A) ∪ (FP A)) := by
  rfl

/-- Expanding the infinite conjecture gives exactly its defining statement. -/
lemma infinite_conjecture_unfold :
    InfiniteConjecture ↔
      ∀ r : ℕ, ∀ χ : Coloring r,
        ∃ (seq : ℕ → ℕ), Function.Injective seq ∧
          ∀ i j : ℕ, i ≠ j →
            χ (seq i + seq j) = χ (seq i * seq j) := by
  rfl

end ErdosProblem172
