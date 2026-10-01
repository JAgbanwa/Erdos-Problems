import PaperIV.CriticalBranch
import PaperIV.CriticalResidual
import PaperIV.TerminalSeparation

/-!
# Near-terminal synthesis

This module joins the two verified scalar interfaces for a complete-split
terminal.  A three-branch exact LP formula plus strict separation of its
non-critical branches forces the critical branch; sharp-envelope algebra then
localizes the split parameter quantitatively.
-/

namespace PaperIV

theorem near_terminal_residual
    {n k δ value middle third : ℚ}
    (hvalue : value = max (splitBaseline n k) (max middle third))
    (hnear : sharpEnvelope n - δ ≤ value)
    (hmiddle : middle < sharpEnvelope n - δ)
    (hthird : third < sharpEnvelope n - δ) :
    (6 * k - 2 * n - 1) ^ 2 ≤ 24 * δ := by
  have hcritical : value = splitBaseline n k :=
    critical_branch_of_near_max hvalue hnear hmiddle hthird
  exact critical_residual_sq_le_of_value hcritical hnear

/-- Concrete `n ≥ 100` form using the two explicit non-critical split-LP
branch bounds. -/
theorem near_terminal_residual_n100
    {n : ℕ} {k value : ℚ} (hn : 100 ≤ n)
    (hvalue : value = max (splitBaseline n k)
      (max ((4 * (n : ℚ) + 1) ^ 2 / 120)
        ((n : ℚ) * ((n : ℚ) - 1) / 12)))
    (hnear : sharpEnvelope n - (n : ℚ) ^ 2 / 40 ≤ value) :
    (6 * k - 2 * (n : ℚ) - 1) ^ 2 ≤ 24 * ((n : ℚ) ^ 2 / 40) := by
  apply near_terminal_residual hvalue hnear
  · exact middleBranch_lt_sharpEnvelope_sub n hn
  · exact thirdBranch_lt_sharpEnvelope_sub n hn

/-- Arithmetic refinement: the branch separation itself needs only `n ≥ 9`.
The substantially larger first-entry threshold belongs to the global copy-path
argument, not to this terminal calculation. -/
theorem near_terminal_residual_nine
    {n : ℕ} {k value : ℚ} (hn : 9 ≤ n)
    (hvalue : value = max (splitBaseline n k)
      (max ((4 * (n : ℚ) + 1) ^ 2 / 120)
        ((n : ℚ) * ((n : ℚ) - 1) / 12)))
    (hnear : sharpEnvelope n - (n : ℚ) ^ 2 / 40 ≤ value) :
    (6 * k - 2 * (n : ℚ) - 1) ^ 2 ≤ 24 * ((n : ℚ) ^ 2 / 40) := by
  apply near_terminal_residual hvalue hnear
  · exact middleBranch_lt_sharpEnvelope_sub_of_nine n hn
  · exact thirdBranch_lt_sharpEnvelope_sub_of_one n (by omega)

end PaperIV
