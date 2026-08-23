/-
  Part A — arithmetic closing leaf of Dross's route (steps A7–A8).

  At δ = 1/10, inequality (8) of Dross together with the triangle-free edge cap force
  n < 20, contradicting n ≥ 20. This is the scalar contradiction that finishes the
  min-cut argument (the small-n case n < 20 is handled separately: δ ≥ 9n/10 forces the
  graph complete).

  STATUS: PROVED (locally, `nlinarith`). Pure real arithmetic; a scalar lemma taking
  Dross's derived inequalities as hypotheses, to be plugged into the flow/min-cut spine.
-/
import Mathlib

namespace Ax2

/-- **Dross A7–A8 arithmetic contradiction (δ = 1/10).** Dross's inequality (8) and the
triangle-free edge cap are incompatible for `n ≥ 20`. -/
theorem dross_final_contradiction (n : ℕ) (m : ℝ) (hn : (20 : ℝ) ≤ (n : ℝ))
    (h8 : (2 - 12 * (1/10 : ℝ) + 12 * (1/10 : ℝ)^2) * (n : ℝ)^2
            < 2 * m - 6 * (1/10 : ℝ) * (n : ℝ))
    (hcap : 2 * m ≤ (1 - (1/10 : ℝ) + 2 * (1/10 : ℝ)^2) * (n : ℝ)^2
                      + 4 + (n : ℝ) - 6 * (1/10 : ℝ) * (n : ℝ)) :
    False := by
  -- the n² terms have equal coefficient (23/25) on both sides and cancel; what remains is
  -- 0 < 4 − n/5, i.e. n < 20, contradicting hn.
  nlinarith [hn, h8, hcap]

end Ax2
