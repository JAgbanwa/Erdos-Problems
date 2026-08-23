import Mathlib
open scoped BigOperators
namespace Contrib

/-- Scalar core of the k = r_b centered closure (Tuza-for-split, working doc §8.1/§8.2).
With q_J = r_b (so the reserve u_J = 0 and κ = 1), the robust shifted-center criterion
reduces to this real inequality; together with `A_J+B_J+E_{¬J} ≤ E_R` and the `E_R`
hypothesis it yields the covering bound behind τ₃ ≤ 2 ν₃. Pure real arithmetic. -/
theorem tuza_split_centered_scalar
    (b ρ r_b : ℕ) (AJ A2J BJ EnJ ER : ℝ)
    (hb : 2 ≤ b) (hrb : 1 ≤ r_b)
    (hA2 : 0 ≤ A2J) (hAJ : 0 ≤ AJ) (hBJ : 0 ≤ BJ) (hEnJ : 0 ≤ EnJ)
    (hratio : (r_b : ℝ) ≤ 2 * (b : ℝ) - 1)
    (hsum : AJ + BJ + EnJ ≤ ER)
    (hER : ER ≤ ((r_b : ℝ) / (2 * (b : ℝ) - 1))
                  * ((Nat.choose b 2 : ℝ) + (Nat.choose ρ 2 : ℝ))) :
    ((2 * (b : ℝ) - 1) * AJ - A2J) / (r_b : ℝ) + BJ + EnJ
      ≤ (Nat.choose b 2 : ℝ) + (Nat.choose ρ 2 : ℝ) := by
  have hb1 : (2 : ℝ) * b - 1 > 0 := by linarith [show (b : ℝ) ≥ 2 by norm_cast]
  have hr2 : (r_b : ℝ) > 0 := by linarith [show (r_b : ℝ) ≥ 1 by norm_cast]
  have hAJ_le_ER : AJ ≤ ER := by linarith [hAJ]
  have hterm_le : ((2 * (b : ℝ) - 1) * AJ - A2J) / (r_b : ℝ) ≤ (2 * (b : ℝ) - 1) * AJ / (r_b : ℝ) := by
    rw [sub_div]
    exact sub_le_self _ (div_nonneg hA2 (le_of_lt hr2))
  have hsum2 : BJ + EnJ ≤ ER - AJ := by linarith
  have hgoal_bound : ((2 * (b : ℝ) - 1) * AJ - A2J) / (r_b : ℝ) + BJ + EnJ ≤ (2 * (b : ℝ) - 1) * AJ / r_b + ER - AJ := by linarith
  have h_ratio_ge : (2 * (b : ℝ) - 1) / r_b ≥ 1 := by
    rw [ge_iff_le, le_div_iff₀ hr2]
    linarith
  have h_aj_bound : AJ * ((2 * (b : ℝ) - 1) / r_b - 1) ≤ ER * ((2 * (b : ℝ) - 1) / r_b - 1) := by
    exact mul_le_mul_of_nonneg_right hAJ_le_ER (by linarith)
  have hgoal_bound2 : (2 * (b : ℝ) - 1) * AJ / r_b + ER - AJ ≤ ER * ((2 * (b : ℝ) - 1) / r_b - 1) + ER := by
    have h1 : (2 * (b : ℝ) - 1) * AJ / r_b = AJ * ((2 * (b : ℝ) - 1) / r_b) := by ring
    have h2 : AJ * ((2 * (b : ℝ) - 1) / r_b) + ER - AJ = AJ * ((2 * (b : ℝ) - 1) / r_b - 1) + ER := by ring
    linarith [h_aj_bound]
  have hgoal_bound3 : ER * ((2 * (b : ℝ) - 1) / r_b - 1) + ER ≤ ER * (2 * (b : ℝ) - 1) / r_b := by
    have : ER * ((2 * (b : ℝ) - 1) / r_b - 1) + ER = ER * ((2 * (b : ℝ) - 1) / r_b) := by ring
    rw [this]
    ring_nf
    exact le_refl _
  have hfinal : ER * (2 * (b : ℝ) - 1) / r_b ≤ (Nat.choose b 2 : ℝ) + (Nat.choose ρ 2 : ℝ) := by
    have hER' : ER * (2 * (b : ℝ) - 1) / r_b ≤ (r_b / (2 * (b : ℝ) - 1) * ((Nat.choose b 2 : ℝ) + (Nat.choose ρ 2 : ℝ))) * (2 * (b : ℝ) - 1) / r_b := by
      gcongr
    refine hER'.trans ?_
    field_simp
    ring_nf
    simp
  linarith

end Contrib
