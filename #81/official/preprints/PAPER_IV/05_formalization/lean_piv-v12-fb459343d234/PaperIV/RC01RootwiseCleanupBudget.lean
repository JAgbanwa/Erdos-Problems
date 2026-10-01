import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Tactic.Positivity

/-!
# RC01: presupuesto de limpieza enraizada por tipo

Las fibras de una raíz tienen escalas distintas: `t` para K3 y `t²` para K4.
Este módulo conserva esa diferencia y prueba las dos desigualdades relativas
certificadas previamente por Certo en
`checks/rc01_rootwise_cleanup_budget.py`.
-/

namespace PaperIV.RC01RootwiseCleanupBudget

/-- Presupuesto relativo de limpieza para una fibra K3. -/
theorem k3_loss_le {delta u t c beta vol v : ℚ}
    (hu : 0 < u) (ht : 0 < t) (hc : 0 < c) (hv : 0 ≤ v)
    (hbad : beta * u ^ 2 * c ^ 2 ≤ 11 * delta * t ^ 2)
    (hvol : c * t ^ 3 ≤ vol)
    (hvchoice : 33 * delta ≤ v * u ^ 2 * c ^ 3) :
    3 * beta * t ≤ v * vol := by
  have hs : 0 < u ^ 2 * c ^ 2 := by positivity
  have hscaled : (u ^ 2 * c ^ 2) * (3 * beta * t)
      ≤ (u ^ 2 * c ^ 2) * (v * vol) := by
    calc
    (u ^ 2 * c ^ 2) * (3 * beta * t)
        = (beta * u ^ 2 * c ^ 2) * (3 * t) := by ring
    _ ≤ (11 * delta * t ^ 2) * (3 * t) :=
      mul_le_mul_of_nonneg_right hbad (by positivity)
    _ = (33 * delta) * t ^ 3 := by ring
    _ ≤ (v * u ^ 2 * c ^ 3) * t ^ 3 :=
      mul_le_mul_of_nonneg_right hvchoice (by positivity)
    _ = (v * u ^ 2 * c ^ 2) * (c * t ^ 3) := by ring
    _ ≤ (v * u ^ 2 * c ^ 2) * vol :=
      mul_le_mul_of_nonneg_left hvol (by positivity)
    _ = (u ^ 2 * c ^ 2) * (v * vol) := by ring
  nlinarith

/-- Presupuesto relativo de limpieza para una fibra K4. -/
theorem k4_loss_le {delta u t c beta vol v : ℚ}
    (hu : 0 < u) (ht : 0 < t) (hc : 0 < c) (hv : 0 ≤ v)
    (hbad : beta * u ^ 2 * c ^ 2 ≤ 23 * delta * t ^ 2)
    (hvol : c * t ^ 4 ≤ vol)
    (hvchoice : 138 * delta ≤ v * u ^ 2 * c ^ 3) :
    6 * beta * t ^ 2 ≤ v * vol := by
  have hs : 0 < u ^ 2 * c ^ 2 := by positivity
  have hscaled : (u ^ 2 * c ^ 2) * (6 * beta * t ^ 2)
      ≤ (u ^ 2 * c ^ 2) * (v * vol) := by
    calc
    (u ^ 2 * c ^ 2) * (6 * beta * t ^ 2)
        = (beta * u ^ 2 * c ^ 2) * (6 * t ^ 2) := by ring
    _ ≤ (23 * delta * t ^ 2) * (6 * t ^ 2) :=
      mul_le_mul_of_nonneg_right hbad (by positivity)
    _ = (138 * delta) * t ^ 4 := by ring
    _ ≤ (v * u ^ 2 * c ^ 3) * t ^ 4 :=
      mul_le_mul_of_nonneg_right hvchoice (by positivity)
    _ = (v * u ^ 2 * c ^ 2) * (c * t ^ 4) := by ring
    _ ≤ (v * u ^ 2 * c ^ 2) * vol :=
      mul_le_mul_of_nonneg_left hvol (by positivity)
    _ = (u ^ 2 * c ^ 2) * (v * vol) := by ring
  nlinarith

end PaperIV.RC01RootwiseCleanupBudget
