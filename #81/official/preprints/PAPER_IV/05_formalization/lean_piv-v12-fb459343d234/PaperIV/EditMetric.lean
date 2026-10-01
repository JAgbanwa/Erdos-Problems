import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Data.Rat.Star
import Mathlib.Tactic.Positivity

/-!
# Edit distance to a fixed finite family (component E3, part A)

The labelled edit distance of the candidate route is the cardinality of a symmetric
difference of edge sets, and the distance to the fixed critical split family is the
minimum of that quantity over the family.  This module fixes those two objects and
proves the one property the contraction argument uses: the family distance is
`1`-Lipschitz for the edit metric.

The ambient type is arbitrary and finite-free: only `DecidableEq` is needed, since
all sets involved are `Finset`s.  In the intended instantiation the ambient type is
`Sym2 V` and the sets are edge sets, but nothing here depends on that.

Design notes:

* the minimum is **attained** (`Finset.inf'` over a nonempty family, with
  `exists_mem_eq_famDist` exhibiting a minimizer); no minimizer is postulated;
* the unnormalized theorem `abs_sub_famDist_le` is proved first, and the normalized
  corollary `abs_sub_famDistNorm_le` is derived from it;
* imports are `Mathlib` only.
-/

namespace PaperIV.EditMetric

open scoped symmDiff

variable {V : Type*} [DecidableEq V]

/-! ## 1. The unnormalized edit metric -/

/-- Unnormalized edit distance: the number of elements in the symmetric difference. -/
def editDist (A B : Finset V) : ℕ := (A ∆ B).card

@[simp] lemma editDist_self (A : Finset V) : editDist A A = 0 := by
  simp [editDist]

lemma editDist_comm (A B : Finset V) : editDist A B = editDist B A := by
  simp [editDist, symmDiff_comm]

@[simp] lemma editDist_eq_zero_iff {A B : Finset V} : editDist A B = 0 ↔ A = B := by
  rw [editDist, Finset.card_eq_zero, Finset.symmDiff_eq_empty]

/-- The edit metric satisfies the triangle inequality. -/
theorem editDist_triangle (A B C : Finset V) :
    editDist A C ≤ editDist A B + editDist B C := by
  have hsub : A ∆ C ⊆ (A ∆ B) ∪ (B ∆ C) := by
    have h := symmDiff_triangle A B C
    simpa [Finset.sup_eq_union] using h
  exact le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)

/-! ## 2. Distance to a fixed nonempty family -/

/-- Distance from `A` to the fixed family `F`: the minimum edit distance to a member
of `F`.  The minimum is taken with `Finset.inf'`, so it is attained by construction. -/
def famDist (F : Finset (Finset V)) (hF : F.Nonempty) (A : Finset V) : ℕ :=
  F.inf' hF fun S => editDist A S

/-- The family distance is attained at an explicit member of the family. -/
theorem exists_mem_eq_famDist (F : Finset (Finset V)) (hF : F.Nonempty) (A : Finset V) :
    ∃ S ∈ F, famDist F hF A = editDist A S :=
  Finset.exists_mem_eq_inf' hF _

/-- Every member of the family bounds the family distance from above. -/
theorem famDist_le (F : Finset (Finset V)) (hF : F.Nonempty) (A : Finset V)
    {S : Finset V} (hS : S ∈ F) : famDist F hF A ≤ editDist A S :=
  Finset.inf'_le _ hS

@[simp] lemma famDist_eq_zero_iff (F : Finset (Finset V)) (hF : F.Nonempty)
    {A : Finset V} : famDist F hF A = 0 ↔ A ∈ F := by
  constructor
  · intro h
    obtain ⟨S, hS, hSA⟩ := exists_mem_eq_famDist F hF A
    rw [h] at hSA
    rwa [← editDist_eq_zero_iff.1 hSA.symm] at hS
  · intro h
    exact Nat.le_zero.1 (le_of_le_of_eq (famDist_le F hF A h) (editDist_self A))

/-! ## 3. The Lipschitz property -/

/-- One-sided Lipschitz bound, in `ℕ` and without subtraction. -/
theorem famDist_le_add (F : Finset (Finset V)) (hF : F.Nonempty) (A B : Finset V) :
    famDist F hF A ≤ famDist F hF B + editDist A B := by
  obtain ⟨S, hS, hSB⟩ := exists_mem_eq_famDist F hF B
  calc famDist F hF A ≤ editDist A S := famDist_le F hF A hS
    _ ≤ editDist A B + editDist B S := editDist_triangle A B S
    _ = famDist F hF B + editDist A B := by rw [hSB]; ring

/-- **The literal 1-Lipschitz inequality** for the distance to a fixed family:
`|d_F(A) - d_F(B)| ≤ |A ∆ B|`.  Stated over `ℚ`, which is where the contraction
argument of the route works. -/
theorem abs_sub_famDist_le (F : Finset (Finset V)) (hF : F.Nonempty) (A B : Finset V) :
    |(famDist F hF A : ℚ) - (famDist F hF B : ℚ)| ≤ (editDist A B : ℚ) := by
  have h₁ : (famDist F hF A : ℚ) ≤ (famDist F hF B : ℚ) + (editDist A B : ℚ) := by
    exact_mod_cast famDist_le_add F hF A B
  have h₂ : (famDist F hF B : ℚ) ≤ (famDist F hF A : ℚ) + (editDist B A : ℚ) := by
    exact_mod_cast famDist_le_add F hF B A
  rw [editDist_comm B A] at h₂
  rw [abs_sub_le_iff]
  constructor <;> linarith

/-! ## 4. Normalized corollary

Only after the unnormalized theorem: dividing both sides by a positive scale. -/

/-- Normalized family distance, for an explicit positive scale `m` (in the route,
`m = n ^ 2`). -/
def famDistNorm (F : Finset (Finset V)) (hF : F.Nonempty) (A : Finset V) (m : ℚ) : ℚ :=
  (famDist F hF A : ℚ) / m

/-- The normalized family distance is `1`-Lipschitz for the normalized edit metric. -/
theorem abs_sub_famDistNorm_le (F : Finset (Finset V)) (hF : F.Nonempty)
    (A B : Finset V) {m : ℚ} (hm : 0 < m) :
    |famDistNorm F hF A m - famDistNorm F hF B m| ≤ (editDist A B : ℚ) / m := by
  have h := abs_sub_famDist_le F hF A B
  rw [famDistNorm, famDistNorm, div_sub_div_same, abs_div, abs_of_pos hm,
    div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right h (le_of_lt (inv_pos.2 hm))

end PaperIV.EditMetric
