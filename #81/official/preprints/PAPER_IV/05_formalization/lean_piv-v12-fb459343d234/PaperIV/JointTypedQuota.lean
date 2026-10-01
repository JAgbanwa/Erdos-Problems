import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Rat.Star
import Mathlib.Tactic.Positivity

/-!
# RC01: the exact two-coordinate typed-gain ledger

For `K₃/K₄` pieces the gain decomposes as

`2 * total number of pieces + 3 * number of K₄ pieces`.

Consequently a joint selector need not expose a fully general profit theorem.
It is enough to preserve (with the same factor) the total fractional mass and
the `K₄` fractional mass.  This module isolates that purely algebraic bridge;
it does not assume that the required selector exists.
-/

namespace PaperIV.JointTypedQuota

/-- A total-piece quota together with a `K₄` quota implies preservation of
the mixed `2/5` objective. -/
theorem typed_gain_of_total_and_four_quota
    {β mass3 mass4 out3 out4 : ℝ}
    (htotal : (1 - β) * (mass3 + mass4) ≤ out3 + out4)
    (hfour : (1 - β) * mass4 ≤ out4) :
    (1 - β) * (2 * mass3 + 5 * mass4) ≤ 2 * out3 + 5 * out4 := by
  linarith

/-- The identity behind the quota reduction. -/
theorem typed_gain_decomposition (out3 out4 : ℝ) :
    2 * out3 + 5 * out4 = 2 * (out3 + out4) + 3 * out4 := by
  ring

/-- After pairing two triangles into one six-resource item, it is enough to
preserve the **total** merged mass and the marked `K₄` mass.  Separate control
of the complementary paired-triangle family is not needed for the typed
objective.  The constant `6` is twice the absolute pairing loss `3`. -/
theorem typed_gain_of_paired_total_and_four_quota
    {β triangleMass pairMass fourMass outPairs outFour : ℝ}
    (hβ : β ≤ 1)
    (hpair : (triangleMass - 3) / 2 ≤ pairMass)
    (htotal : (1 - β) * (pairMass + fourMass) ≤ outPairs + outFour)
    (hfour : (1 - β) * fourMass ≤ outFour) :
    (1 - β) * (2 * triangleMass + 5 * fourMass - 6)
      ≤ 4 * outPairs + 5 * outFour := by
  have hβ0 : 0 ≤ 1 - β := by linarith
  have hpair4 : (1 - β) * (2 * triangleMass - 6) ≤
      (1 - β) * (4 * pairMass) := by
    apply mul_le_mul_of_nonneg_left _ hβ0
    linarith
  nlinarith

/-- The additive form actually needed by the asymptotic RC01 route.  A loss
`errTotal` in the total merged quota is charged four times, while a loss
`errFour` in the marked `K₄` quota is charged once.  Thus the probabilistic
input need only provide two `o(|W|)` additive errors; it need not preserve a
tiny marked class multiplicatively. -/
theorem typed_gain_of_paired_total_and_four_quota_additive
    {β triangleMass pairMass fourMass outPairs outFour errTotal errFour : ℝ}
    (hβ : β ≤ 1)
    (hpair : (triangleMass - 3) / 2 ≤ pairMass)
    (htotal : (1 - β) * (pairMass + fourMass) - errTotal
      ≤ outPairs + outFour)
    (hfour : (1 - β) * fourMass - errFour ≤ outFour) :
    (1 - β) * (2 * triangleMass + 5 * fourMass - 6)
        - (4 * errTotal + errFour)
      ≤ 4 * outPairs + 5 * outFour := by
  have hβ0 : 0 ≤ 1 - β := by linarith
  have hpair4 : (1 - β) * (2 * triangleMass - 6) ≤
      (1 - β) * (4 * pairMass) := by
    apply mul_le_mul_of_nonneg_left _ hβ0
    linarith
  nlinarith

/-- Cardinality preservation alone cannot establish typed preservation: the
normalized all-`K₄` input and all-`K₃` output lose `3`. -/
theorem cardinality_only_counterexample :
    let mass3 : ℚ := 0
    let mass4 : ℚ := 1
    let out3 : ℚ := 1
    let out4 : ℚ := 0
    mass3 + mass4 = out3 + out4 ∧
      2 * out3 + 5 * out4 < 2 * mass3 + 5 * mass4 := by
  norm_num

end PaperIV.JointTypedQuota
