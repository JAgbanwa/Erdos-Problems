import Mathlib
import PaperIV.ParametricBudget

/-!
# Canonical deficit budget

This module formalizes the scalar integration of the two canonical deficits.
It deliberately does not assume a symmetrization tree: a later module must
prove that its terminal law supplies the hypotheses `F ≤ U ≤ M`.
-/

namespace PaperIV.CanonicalBudget

def historicalDeficit (M U : ℚ) : ℚ := M - U

def geometricDeficit (U F : ℚ) : ℚ := U - F

def totalDeficit (M F : ℚ) : ℚ := M - F

theorem total_eq_hist_add_geom (M U F : ℚ) :
    totalDeficit M F = historicalDeficit M U + geometricDeficit U F := by
  simp only [totalDeficit, historicalDeficit, geometricDeficit]
  ring

theorem deficits_nonnegative {M U F : ℚ} (hFU : F ≤ U) (hUM : U ≤ M) :
    0 ≤ historicalDeficit M U ∧ 0 ≤ geometricDeficit U F := by
  constructor <;> simp only [historicalDeficit, geometricDeficit] <;> linarith

/-- A paid physical terminal draws from the same total canonical deficit. -/
theorem paid_terminal_from_total_deficit
    {M U F B m A : ℚ}
    (hpaid : F ≤ B - m / 20 - A / 2) :
    M - B + m / 20 + A / 2 ≤
      historicalDeficit M U + geometricDeficit U F := by
  rw [← total_eq_hist_add_geom]
  simp only [totalDeficit]
  linarith

/-- The physical defects have the advertised factor-20 bound whenever the
root-baseline displacement is nonnegative. -/
theorem physical_defects_le_twenty_total
    {M U F B m A : ℚ}
    (hbase : 0 ≤ M - B)
    (hm : 0 ≤ m) (hA : 0 ≤ A)
    (hpaid : F ≤ B - m / 20 - A / 2) :
    m + A ≤ 20 * (historicalDeficit M U + geometricDeficit U F) := by
  have hbudget := paid_terminal_from_total_deficit (M := M) (U := U) hpaid
  exact ParametricBudget.rd09_defect_sum_bound
    (s := M - B) hbase hm hA (by linarith [hbudget])

end PaperIV.CanonicalBudget
