import PaperIV.EditFirstEntry

/-!
# From a single-vertex copy budget to the E3 first-entry window

The chordal copy construction will prove the structural fact that one move
changes at most `n - 2` literal edges.  This module discharges the independent
arithmetic and metric consequence: after normalization by `n²`, those moves
have size at most `1/n`, so E3 applies verbatim.
-/

namespace PaperIV.CopyPathWindow

open PaperIV.EditMetric
open PaperIV.EditFirstEntry

theorem copy_step_normalized_le_inv (n : ℕ) (hn : 2 ≤ n) :
    ((n - 2 : ℕ) : ℚ) / (n : ℚ) ^ 2 ≤ 1 / (n : ℚ) := by
  have hnq : (0 : ℚ) < n := by exact_mod_cast (show 0 < n by omega)
  have hsub : ((n - 2 : ℕ) : ℚ) ≤ n := by
    exact_mod_cast (Nat.sub_le n 2)
  calc
    ((n - 2 : ℕ) : ℚ) / (n : ℚ) ^ 2 ≤ (n : ℚ) / (n : ℚ) ^ 2 :=
      div_le_div_of_nonneg_right hsub (by positivity)
    _ = 1 / (n : ℚ) := by field_simp

/-- A step changing at most `c·n` edges has normalized size at most `c/n`.
This is the form consumed by a selector of bounded clone classes. -/
theorem copy_step_normalized_le_c_div (n c : ℕ) (hn : 1 ≤ n) :
    ((c * n : ℕ) : ℚ) / (n : ℚ) ^ 2 ≤ (c : ℚ) / (n : ℚ) := by
  have hnq : (0 : ℚ) < n := by exact_mod_cast (show 0 < n by omega)
  rw [Nat.cast_mul]
  field_simp
  exact le_rfl

variable {V : Type*} [DecidableEq V]
variable {N : ℕ}

theorem exists_window_of_copy_steps
    (n : ℕ) (hn : 2 ≤ n)
    (F : Finset (Finset V)) (hF : F.Nonempty)
    (A : Fin (N + 1) → Finset V) (r : ℚ)
    (h0 : r ≤ famDistNorm F hF (A 0) ((n : ℚ) ^ 2))
    (hlast : famDistNorm F hF (A (Fin.last N)) ((n : ℚ) ^ 2) < r)
    (hstep : ∀ i : Fin N, editDist (A i.succ) (A i.castSucc) ≤ n - 2) :
    ∃ j : Fin (N + 1),
      (∀ i : Fin (N + 1), famDistNorm F hF (A i) ((n : ℚ) ^ 2) < r → j ≤ i) ∧
      r - 1 / (n : ℚ) ≤ famDistNorm F hF (A j) ((n : ℚ) ^ 2) ∧
      famDistNorm F hF (A j) ((n : ℚ) ^ 2) < r := by
  have hnq : (0 : ℚ) < n := by exact_mod_cast (show 0 < n by omega)
  apply exists_window_of_edit_steps F hF A ((n : ℚ) ^ 2) r (1 / (n : ℚ))
    (by positivity) h0 hlast
  intro i
  have hi : (editDist (A i.succ) (A i.castSucc) : ℚ) ≤ (n - 2 : ℕ) := by
    exact_mod_cast hstep i
  calc
    (editDist (A i.succ) (A i.castSucc) : ℚ) / (n : ℚ) ^ 2 ≤
        ((n - 2 : ℕ) : ℚ) / (n : ℚ) ^ 2 :=
      div_le_div_of_nonneg_right hi (by positivity)
    _ ≤ 1 / (n : ℚ) := copy_step_normalized_le_inv n hn

/-- First entry for a copy path whose source class has a uniform cardinality
bound `c`: the crossing window has width `c/n`. -/
theorem exists_window_of_bounded_copy_steps
    (n c : ℕ) (hn : 1 ≤ n)
    (F : Finset (Finset V)) (hF : F.Nonempty)
    (A : Fin (N + 1) → Finset V) (r : ℚ)
    (h0 : r ≤ famDistNorm F hF (A 0) ((n : ℚ) ^ 2))
    (hlast : famDistNorm F hF (A (Fin.last N)) ((n : ℚ) ^ 2) < r)
    (hstep : ∀ i : Fin N, editDist (A i.succ) (A i.castSucc) ≤ c * n) :
    ∃ j : Fin (N + 1),
      (∀ i : Fin (N + 1), famDistNorm F hF (A i) ((n : ℚ) ^ 2) < r → j ≤ i) ∧
      r - (c : ℚ) / (n : ℚ) ≤ famDistNorm F hF (A j) ((n : ℚ) ^ 2) ∧
      famDistNorm F hF (A j) ((n : ℚ) ^ 2) < r := by
  apply exists_window_of_edit_steps F hF A ((n : ℚ) ^ 2) r ((c : ℚ) / (n : ℚ))
    (by positivity) h0 hlast
  intro i
  have hi : (editDist (A i.succ) (A i.castSucc) : ℚ) ≤ ((c * n : ℕ) : ℚ) := by
    exact_mod_cast hstep i
  calc
    (editDist (A i.succ) (A i.castSucc) : ℚ) / (n : ℚ) ^ 2 ≤
        ((c * n : ℕ) : ℚ) / (n : ℚ) ^ 2 :=
      div_le_div_of_nonneg_right hi (by positivity)
    _ ≤ (c : ℚ) / (n : ℚ) := copy_step_normalized_le_c_div n c hn

end PaperIV.CopyPathWindow
