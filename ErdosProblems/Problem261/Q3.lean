import ErdosProblems.Problem261.Basic
import ErdosProblems.Problem261.Telescoping
import ErdosProblems.Problem261.Q1

import Mathlib.Data.Finset.Basic
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.Tactic

/-!
# Question 3 — continuum-many infinite representations

Paper Theorems 5.4 and 5.5 (sequence and set readings).  The continuum-cardinality
proofs use binary-expansion disjointness and dominated convergence; they are recorded
here as precise statements with `sorry`.
-/

namespace ErdosProblem261

open scoped BigOperators

/-- Term `n_s / 2^{n_s}` for scales `s ≥ 3`. -/
noncomputable def xStarTerm (s : ℕ) : ℚ :=
  if 3 ≤ s then (nFamily s : ℚ) / (2 ^ nFamily s : ℚ) else 0

/-- Partial sum of `x*` over finitely many scales. -/
noncomputable def xStar (S : Finset ℕ) : ℚ :=
  ∑ s ∈ S, xStarTerm s

/-- Swap block for scale `s`: either `{n_s}` or the Theorem-1 block. -/
def swapBlock (s : ℕ) (useBlock : Bool) : Finset ℕ :=
  if useBlock then familyBlock s else {nFamily s}

lemma swapBlock_sum (s : ℕ) (hs : 3 ≤ s) (b : Bool) :
    fSum (swapBlock s b) = (nFamily s : ℚ) / (2 ^ nFamily s : ℚ) := by
  unfold swapBlock
  split_ifs with h
  · exact (familyRepresentation s hs).2.2
  · simp [fSum, f, nFamily]

/-- A finite set of swap choices indexed by scales `≥ 3`. -/
def swapSet (ε : Finset ℕ) (chooseBlock : ε → Bool) : Finset ℕ :=
  ε.biUnion fun s => swapBlock s (chooseBlock s)

lemma swapSet_sum {ε : Finset ℕ} (hε : ∀ s ∈ ε, 3 ≤ s) (chooseBlock : ε → Bool) :
    fSum (swapSet ε chooseBlock) = ∑ s ∈ ε, (nFamily s : ℚ) / (2 ^ nFamily s : ℚ) := by
  sorry

/-- **Theorem 5.5 (statement).** An explicit irrational target has continuum-many set-solutions. -/
theorem setSolutions_exist :
    ∃ x : ℚ, (2 : Cardinal) ^ Cardinal.aleph0 ≤
      Cardinal.mk { A : Finset ℕ |
        ∃ (ε : Finset ℕ) (chooseBlock : ε → Bool),
          (∀ s ∈ ε, 3 ≤ s) ∧ fSum A = x ∧
          A = swapSet ε chooseBlock } := by
  sorry

/-- Adjacent swap used in the sequence construction (paper Theorem 5.4). -/
def swapAdjacent (ε : ℕ → Bool) (k : ℕ) : ℕ :=
  if 0 < k ∧ ε (k / 2) then
    if Odd k then k + 1 else k - 1
  else k

lemma swapAdjacent_injective (ε : ℕ → Bool) :
    Function.Injective (swapAdjacent ε) := by
  sorry

/-- **Theorem 5.4 (statement).** `x = 2` has continuum-many injective sequence solutions. -/
theorem sequenceSolutions_two :
    (2 : Cardinal) ^ Cardinal.aleph0 ≤
      Cardinal.mk { a : ℕ → ℕ | Function.Injective a ∧
        ∀ N, ∃ M, M ≤ N ∧
          (2 : ℚ) - ∑ k ∈ Finset.Icc 1 M, f (a k) ≤ (1 : ℚ) / (2 : ℚ) ^ N } := by
  sorry

/-- `x = 2` has a unique set-solution `{1,2,…}` (paper Remark 5.7). -/
theorem unique_set_solution_two (A : Finset ℕ) (hpos : ∀ k ∈ A, 0 < k)
    (hsum : fSum A = 2) : A = Finset.Ioi 0 := by
  sorry

/-- Proposition 5.6 (statement): the explicit target `x*` is irrational. -/
theorem xStar_irrational :
    Irrational (∑' s : ℕ, xStarTerm s) := by
  sorry

end ErdosProblem261
