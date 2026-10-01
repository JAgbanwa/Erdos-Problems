import PaperIV.CleanedLowTriangleBridge

/-!
# RC01: one explicit schedule for the triangle dichotomy

This is the Lean counterpart of the exact Certo certificate in
`certificates/rc01_low_triangle_schedule_core.json`.  It allocates half of the
target error to the cleaned high-mass gate and uses the normalized triangle
threshold `C / n² ≤ ε / 30`.
-/

namespace PaperIV.RC01TriangleSchedule

open MixedRounding

/-- The two terminal inequalities required by the triangle-swap bridge. -/
theorem branch_budget {n C : ℕ} {ε ζ : ℝ}
    (hζ : 2 * ζ ≤ ε)
    (hC : 30 * (C : ℝ) ≤ ε * (n : ℝ) ^ 2) :
    15 * (C : ℝ) ≤ ε * (n : ℝ) ^ 2 ∧
      13 * (C : ℝ) + ζ * (n : ℝ) ^ 2 ≤ ε * (n : ℝ) ^ 2 := by
  have hn : 0 ≤ (n : ℝ) ^ 2 := sq_nonneg (n : ℝ)
  constructor
  · nlinarith
  · have hζn := mul_le_mul_of_nonneg_right hζ hn
    nlinarith

/-- Scheduled form of the low-triangle bridge.  Downstream assembly only has
to prove the cleaned high-mass gate and the single threshold `30 C ≤ ε n²`. -/
theorem lowTriangle_branch_free_scheduled {n : ℕ}
    {Gn : SimpleGraph (Fin n)} [DecidableRel Gn.Adj]
    (y : FracPacking Gn) (C : ℕ) {ε ζ : ℝ}
    (hgate : ∀ z : FracPacking Gn,
      (C : ℝ) ≤ PaperIV.JointTwoQuotaPhysical.triangleMass z →
      ∃ Pk : Packing Gn, ((z.value : ℚ) : ℝ) - (Pk.gain : ℝ) ≤ ζ * (n : ℝ) ^ 2)
    (hζ : 2 * ζ ≤ ε)
    (hC : 30 * (C : ℝ) ≤ ε * (n : ℝ) ^ 2) :
    ∃ Pk : Packing Gn, ((y.value : ℚ) : ℝ) - (Pk.gain : ℝ) ≤ ε * (n : ℝ) ^ 2 := by
  obtain ⟨hempty, hswap⟩ := branch_budget hζ hC
  exact PaperIV.CleanedLowTriangleBridge.lowTriangle_branch_free_real
    y C hgate hempty hswap

end PaperIV.RC01TriangleSchedule
