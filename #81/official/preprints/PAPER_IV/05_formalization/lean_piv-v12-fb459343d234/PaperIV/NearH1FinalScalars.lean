import PaperIV.EquitableEdgeColouring
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Data.Rat.Star

/-! # Scalar closure of the promoted-root H1 gate

This is the exact rational shadow certified by Certo before formalization.
It isolates the arithmetic from the graph-theoretic accounting.
-/

namespace PaperIV.NearH1FinalScalars

/-- The demotion and promotion ledgers imply every scalar inequality consumed
by the literal H1 assembly (apart from the separately bounded colour-class
size and maximum missing column). -/
theorem final_scalar_package
    {a q m A r p₀ q₀ m₁ D h p qf mf Af f : ℚ}
    (ha : 1024 ≤ a)
    (hm : 0 ≤ m) (hr : 0 ≤ r) (hh : 0 ≤ h)
    (hbalanceLower : 127 * a ≤ 64 * q)
    (hdefect : 65536 * (m + A) ≤ a ^ 2)
    (hdemoted : 1024 * r ≤ a)
    (hp₀ : p₀ = a - r) (hq₀ : q₀ = q + r)
    (hm₁ : 400 * m₁ < a ^ 2)
    (hD : 3 * D ≤ a)
    (hpromotion : 7 * p₀ * h ≤ 4 * m₁)
    (hp : p = p₀ + h) (hqf : qf = q₀ - h)
    (hmf : mf ≤ m₁) (hAf : Af ≤ A + h * D) (hf : f ≤ mf) :
    p ≤ qf ∧ 2 ≤ qf ∧
      100 * p ≤ 101 * a ∧
      87947 * a ≤ 44352 * qf ∧
      48 * (2 * p - qf) ≤ a ∧
      2000 * (Af + 2 * f) ≤ 11 * a ^ 2 := by
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  · nlinarith

/-- The equitable class ceiling is at most `a/256` under the literal
post-demotion edge budget.  This is the integer (rounding-safe) form needed
for the phase-I maximum load. -/
theorem classCeiling_le_reference_div
    {a p m c : ℕ} (ha : 1024 ≤ a) (hp : 99 * a ≤ 100 * p)
    (hm : 400 * m < a * a) (hpc : p ≤ c) :
    PaperIV.EquitableEdgeColouring.classCeiling m c ≤ a / 256 := by
  have hpPos : 0 < p := by nlinarith
  have hcPos : 0 < c := lt_of_lt_of_le hpPos hpc
  rw [PaperIV.EquitableEdgeColouring.classCeiling,
    ceilDiv_le_iff_le_mul hcPos]
  have hdivLo : 256 * (a / 256) ≤ a := Nat.mul_div_le a 256
  have hdivHi : a ≤ 256 * (a / 256) + 255 := by omega
  have hd : 4 ≤ a / 256 := by omega
  have hpd : m ≤ p * (a / 256) := by
    nlinarith [mul_nonneg (show 0 ≤ 100 * p - 99 * a by omega)
      (show 0 ≤ a / 256 by omega)]
  simpa [Nat.mul_comm] using
    hpd.trans (Nat.mul_le_mul_right (a / 256) hpc)

end PaperIV.NearH1FinalScalars
