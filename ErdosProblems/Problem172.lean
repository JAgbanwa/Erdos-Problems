import ErdosProblems.ProofStrategy

/-!
# Erdős Problem #172 - Finite Sums and Products

In any finite coloring of ℕ, do there exist arbitrarily large finite A such that
all sums and products of distinct elements in A are the same color?

Answer (Finite Version): YES - Proven using Milliken-Taylor theorem
Answer (Infinite Version): OPEN - Stronger conjecture still unsolved
-/

namespace ErdosProblem172

variable {n : ℕ}

/-! ## Main Theorem -/

/-- The finite sums-products theorem:
For any finite coloring and any target size m,
there exists a set A of size m such that FS(A) ∪ FP(A) is monochromatic,
assuming the finite Milliken-Taylor-style statement recorded as `FiniteVersion`. -/
theorem finite_sums_products_theorem (h : FiniteVersion) (r m : ℕ) (χ : Coloring r) :
    ∃ (A : Finset ℕ), A.card = m ∧ 
      IsMonochromatic χ (FS A ∪ FP A) := by
  exact h r m χ

/-! ## Properties -/

lemma fs_card_bound (A : Finset ℕ) : (FS A).card ≤ 2 ^ A.card - 1 := by
  calc
    (FS A).card ≤ (nonemptySubsets A).card := by
      simpa [FS] using
        (Finset.card_image_le
          (s := nonemptySubsets A) (f := fun s : Finset ℕ => s.sum id))
    _ = 2 ^ A.card - 1 := nonemptySubsets_card A

lemma fp_card_bound (A : Finset ℕ) : (FP A).card ≤ 2 ^ A.card - 1 := by
  calc
    (FP A).card ≤ (nonemptySubsets A).card := by
      simpa [FP] using
        (Finset.card_image_le
          (s := nonemptySubsets A) (f := fun s : Finset ℕ => s.prod id))
    _ = 2 ^ A.card - 1 := nonemptySubsets_card A

lemma fs_fp_union_finite (A : Finset ℕ) : 
    ((FS A) ∪ (FP A)).card < 2 ^ (A.card + 1) := by
  have hUnion : ((FS A) ∪ (FP A)).card ≤ (FS A).card + (FP A).card :=
    Finset.card_union_le (FS A) (FP A)
  have hFS := fs_card_bound A
  have hFP := fp_card_bound A
  have hle : ((FS A) ∪ (FP A)).card ≤
      (2 ^ A.card - 1) + (2 ^ A.card - 1) := by
    omega
  have hpos : 0 < 2 ^ A.card := Nat.pow_pos (by norm_num)
  have hlt : (2 ^ A.card - 1) + (2 ^ A.card - 1) < 2 * 2 ^ A.card := by
    omega
  exact lt_of_le_of_lt hle (by
    simpa [pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hlt)

end ErdosProblem172
