import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

/-!
# Erdős Problem #261 — Basic definitions

Representations using distinct terms `f(k) = k / 2^k`.
-/

namespace ErdosProblem261

open scoped BigOperators

/-- The term `f(k) = k / 2^k` as a rational number. -/
def f (k : ℕ) : ℚ := (k : ℚ) / (2 ^ k : ℚ)

/-- The telescoping companion `G(m) = (m+1) / 2^{m-1}` for `m ≥ 1`. -/
def G (m : ℕ) (_hm : 0 < m) : ℚ := (m + 1 : ℚ) / (2 ^ (m - 1) : ℚ)

/-- Sum of `f` over a finite set of indices. -/
def fSum (S : Finset ℕ) : ℚ := S.sum f

/-- A finite representation of `n / 2^n` by at least two distinct positive indices. -/
def HasFiniteRepresentation (n : ℕ) (S : Finset ℕ) : Prop :=
  2 ≤ S.card ∧
    (∀ k ∈ S, 0 < k) ∧
    fSum S = (n : ℚ) / (2 ^ n : ℚ)

/-- Question (1): there exist at least two distinct indices with the required sum. -/
def Question1 (n : ℕ) : Prop :=
  ∃ S : Finset ℕ, HasFiniteRepresentation n S

/-- The explicit infinite family parameter `n_s = 2^s - s - 1`. -/
def nFamily (s : ℕ) : ℕ := 2 ^ s - s - 1

/-- The block of indices used in Theorem 1: `{n_s+1, …, 2^s - 2}`. -/
def familyBlock (s : ℕ) : Finset ℕ :=
  Finset.Icc (nFamily s + 1) (2 ^ s - 2)

/-- The second-family parameters for odd `E ≥ 5`. -/
def secondFamilyB (E : ℕ) : ℕ := (2 ^ E - 5) / 3 + 1

def secondFamilyA (E : ℕ) : ℕ := secondFamilyB E + 1 - E

/-- The interior `(a+1, …, b-1)` in Remark 2. -/
def secondFamilyInterior (E : ℕ) : Finset ℕ :=
  Finset.Icc (secondFamilyA E + 1) (secondFamilyB E - 1)

lemma fSum_pair {a b : ℕ} (hab : a ≠ b) :
    fSum {a, b} = f a + f b := by
  simp [fSum, Finset.sum_pair hab]

end ErdosProblem261
