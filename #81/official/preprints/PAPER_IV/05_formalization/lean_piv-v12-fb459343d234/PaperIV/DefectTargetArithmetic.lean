import PaperIV.FarRounding

/-!
The target for fixed rooted simplicial defect `s`, as used by Okechukwu, is
`Q_s(n) = M(n+s) - C(s+1,2)`.  This file contains only the arithmetic
comparison with the chordal target.  It does not assume a theorem about graphs
of defect `s`.
-/

namespace PaperIV.DefectTargetArithmetic

open PaperIV.FarRounding

def defectTarget (s n : ℕ) : ℕ := targetSize (n + s) - Nat.choose (s + 1) 2

/-- On orders larger than the defect, the defect target dominates `M(n)`. -/
theorem targetSize_le_defectTarget (s n : ℕ) (hn : s + 1 ≤ n) :
    targetSize n ≤ defectTarget s n := by
  have hchoose : 2 * Nat.choose (s + 1) 2 = (s + 1) * s := by
    rw [Nat.choose_two_right, Nat.mul_comm 2,
      Nat.div_mul_cancel (Nat.even_mul_pred_self (s + 1)).two_dvd]
    simp
  have hpoly : n * (n + 1) + 6 * Nat.choose (s + 1) 2 ≤
      (n + s) * (n + s + 1) := by
    nlinarith [Nat.mul_le_mul_left (2 * s) hn]
  have hfloor : 6 * targetSize n ≤ n * (n + 1) := by
    unfold targetSize
    omega
  have hmain : targetSize n + Nat.choose (s + 1) 2 ≤ targetSize (n + s) := by
    unfold targetSize at *
    apply (Nat.le_div_iff_mul_le (by norm_num)).2
    omega
  unfold defectTarget
  omega

end PaperIV.DefectTargetArithmetic

