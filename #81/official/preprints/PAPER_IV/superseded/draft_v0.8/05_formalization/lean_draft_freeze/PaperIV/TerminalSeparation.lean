import PaperIV.SharpEnvelope

/-!
# Separation of the non-critical split-terminal branches

For orders at least 100, the second and third split-LP branches lie strictly
below the near-extremal threshold.  Consequently a near-extremal terminal must
come from the critical quadratic branch.  This module is only the scalar part;
the split-LP theorem supplies the branch alternatives separately.
-/

namespace PaperIV

def nearThreshold (n : ℚ) : ℚ := n ^ 2 / 6 - n ^ 2 / 40

/-- The exact positive gap behind the sharp `n ≥ 9` middle-branch cutoff. -/
theorem middle_gap_pos_of_nine (n : ℕ) (hn : 9 ≤ n) :
    0 < (n : ℚ) ^ 2 - 8 * (n : ℚ) - 1 := by
  have hnq : (9 : ℚ) ≤ n := by exact_mod_cast hn
  have hprod : 0 ≤ ((n : ℚ) - 9) * ((n : ℚ) + 1) :=
    mul_nonneg (by linarith) (by positivity)
  nlinarith

theorem middleBranch_lt_nearThreshold (n : ℕ) (hn : 100 ≤ n) :
    (4 * (n : ℚ) + 1) ^ 2 / 120 < nearThreshold n := by
  have hnq : (100 : ℚ) ≤ n := by exact_mod_cast hn
  have hsquare : 0 ≤ ((n : ℚ) - 100) ^ 2 := sq_nonneg _
  unfold nearThreshold
  nlinarith

/-- The middle-branch separation only needs `n ≥ 9`; `100` in the original
route was a convenient common terminal range, not the sharp arithmetic cutoff. -/
theorem middleBranch_lt_nearThreshold_of_nine (n : ℕ) (hn : 9 ≤ n) :
    (4 * (n : ℚ) + 1) ^ 2 / 120 < nearThreshold n := by
  have hgap := middle_gap_pos_of_nine n hn
  unfold nearThreshold
  nlinarith

theorem thirdBranch_lt_nearThreshold (n : ℕ) (hn : 100 ≤ n) :
    (n : ℚ) * ((n : ℚ) - 1) / 12 < nearThreshold n := by
  have hnq : (100 : ℚ) ≤ n := by exact_mod_cast hn
  unfold nearThreshold
  nlinarith

theorem thirdBranch_lt_nearThreshold_of_one (n : ℕ) (hn : 1 ≤ n) :
    (n : ℚ) * ((n : ℚ) - 1) / 12 < nearThreshold n := by
  have hnq : (1 : ℚ) ≤ n := by exact_mod_cast hn
  unfold nearThreshold
  nlinarith

/-- The same two branch exclusions in the sharp-envelope normalization used by
the residual theorem. -/
theorem middleBranch_lt_sharpEnvelope_sub (n : ℕ) (hn : 100 ≤ n) :
    (4 * (n : ℚ) + 1) ^ 2 / 120 < sharpEnvelope n - (n : ℚ) ^ 2 / 40 := by
  have h := middleBranch_lt_nearThreshold n hn
  calc
    (4 * (n : ℚ) + 1) ^ 2 / 120 < nearThreshold n := h
    _ ≤ sharpEnvelope n - (n : ℚ) ^ 2 / 40 := by
      unfold nearThreshold sharpEnvelope
      have hn0 : (0 : ℚ) ≤ n := Nat.cast_nonneg n
      nlinarith

theorem middleBranch_lt_sharpEnvelope_sub_of_nine (n : ℕ) (hn : 9 ≤ n) :
    (4 * (n : ℚ) + 1) ^ 2 / 120 < sharpEnvelope n - (n : ℚ) ^ 2 / 40 := by
  have h := middleBranch_lt_nearThreshold_of_nine n hn
  calc
    (4 * (n : ℚ) + 1) ^ 2 / 120 < nearThreshold n := h
    _ ≤ sharpEnvelope n - (n : ℚ) ^ 2 / 40 := by
      unfold nearThreshold sharpEnvelope
      have hn0 : (0 : ℚ) ≤ n := Nat.cast_nonneg n
      nlinarith

theorem thirdBranch_lt_sharpEnvelope_sub (n : ℕ) (hn : 100 ≤ n) :
    (n : ℚ) * ((n : ℚ) - 1) / 12 < sharpEnvelope n - (n : ℚ) ^ 2 / 40 := by
  have h := thirdBranch_lt_nearThreshold n hn
  calc
    (n : ℚ) * ((n : ℚ) - 1) / 12 < nearThreshold n := h
    _ ≤ sharpEnvelope n - (n : ℚ) ^ 2 / 40 := by
      unfold nearThreshold sharpEnvelope
      have hn0 : (0 : ℚ) ≤ n := Nat.cast_nonneg n
      nlinarith

theorem thirdBranch_lt_sharpEnvelope_sub_of_one (n : ℕ) (hn : 1 ≤ n) :
    (n : ℚ) * ((n : ℚ) - 1) / 12 < sharpEnvelope n - (n : ℚ) ^ 2 / 40 := by
  have h := thirdBranch_lt_nearThreshold_of_one n hn
  calc
    (n : ℚ) * ((n : ℚ) - 1) / 12 < nearThreshold n := h
    _ ≤ sharpEnvelope n - (n : ℚ) ^ 2 / 40 := by
      unfold nearThreshold sharpEnvelope
      have hn0 : (0 : ℚ) ≤ n := Nat.cast_nonneg n
      nlinarith

end PaperIV
