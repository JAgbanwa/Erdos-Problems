import Mathlib

/-!
# Scalar budgets for the new Paper IV

These lemmas are the first verified interface adaptation from the supplied RD09 route. They are intentionally independent of the historical `AlternativeAssembly.NearTerminalInput`, whose `m / 9` coefficient is not available from RD09. The eventual graph-theoretic terminal will instantiate these lemmas with `a = 1/20`, `b = 1/2`, and `K = 20`.
-/

namespace PaperIV.ParametricBudget

theorem defect_sum_bound
    {s a b m A delta K : ℚ}
    (hs : 0 ≤ s) (hm : 0 ≤ m) (hA : 0 ≤ A) (hK : 0 ≤ K)
    (hka : 1 ≤ K * a) (hkb : 1 ≤ K * b)
    (htotal : s + a * m + b * A ≤ delta) :
    m + A ≤ K * delta := by
  have hm' := mul_le_mul_of_nonneg_right hka hm
  have hA' := mul_le_mul_of_nonneg_right hkb hA
  have hsmall : a * m + b * A ≤ delta := by linarith
  have hscaled := mul_le_mul_of_nonneg_left hsmall hK
  nlinarith

theorem rd09_defect_sum_bound
    {s m A delta : ℚ} (hs : 0 ≤ s) (hm : 0 ≤ m) (hA : 0 ≤ A)
    (htotal : s + m / 20 + A / 2 ≤ delta) :
    m + A ≤ 20 * delta := by
  apply defect_sum_bound (a := (1 : ℚ) / 20) (b := (1 : ℚ) / 2)
    hs hm hA (by norm_num) (by norm_num) (by norm_num)
  simpa [div_eq_mul_inv, mul_comm] using htotal

theorem exact_piece_budget
    {L B m A f g : ℚ}
    (hcount : L = B + m - A - 2 * f + 2 * g)
    (hf : (40 : ℚ) / 73 * m - (3 : ℚ) / 40 * A ≤ f)
    (hg : g ≤ (7 : ℚ) / 40 * A + f / 25) :
    L ≤ B - (19 : ℚ) / 365 * m - (253 : ℚ) / 500 * A := by
  linarith

theorem rd09_coefficients :
    (1 : ℚ) / 20 ≤ 19 / 365 ∧ (1 : ℚ) / 2 ≤ 253 / 500 ∧
      (19 : ℚ) / 365 < 1 / 9 := by
  norm_num

theorem first_entry_rational_margin :
    (40 : ℚ) / 10^30 + 2 / 10^15 + 1 / 10^32 < (1 : ℚ) / (4 * 10^12) ∧
      (1 : ℚ) / (4 * 10^12) < 1 / (2 * 10^12) - 1 / 10^32 := by
  norm_num

end PaperIV.ParametricBudget
