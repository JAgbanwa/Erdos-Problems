import PaperIV.SharpEnvelope

/-!
# Quantitative residual on the critical split branch

The sharp-envelope identity turns a near-extremal critical terminal into an
explicit square bound on its split parameter.  This is the algebraic content
of the critical-core localization before any graph distance is considered.
-/

namespace PaperIV

theorem critical_residual_sq_le {n k δ : ℚ}
    (hnear : sharpEnvelope n - δ ≤ splitBaseline n k) :
    (6 * k - 2 * n - 1) ^ 2 ≤ 24 * δ := by
  have hidentity := sharpEnvelope_sub_splitBaseline n k
  nlinarith

theorem critical_residual_sq_le_of_value {n k δ value : ℚ}
    (hvalue : value = splitBaseline n k)
    (hnear : sharpEnvelope n - δ ≤ value) :
    (6 * k - 2 * n - 1) ^ 2 ≤ 24 * δ := by
  rw [hvalue] at hnear
  exact critical_residual_sq_le hnear

end PaperIV
