import PaperIV.TargetEnvelope
import Mathlib.Data.Int.Star
import Mathlib.Tactic.IntervalCases

/-!
# Aritmética exacta del objetivo `M(n) = ⌊n(n+1)/6⌋`

Este módulo aísla los hechos aritméticos que hacen falta para una **reducción integral
exacta** (la ruta que pretende `b = 0` para todo `n`, en vez de `n ≥ N`).

* `targetSize_formula` — forma cerrada de `M` en función de `n = 6q + k`.
* `targetSize_succ` — **el paso exacto**: `M(n+1) = M(n) + ⌊(n+2)/3⌋`; reescrito,
  `M(n) − M(n−1) = ⌊(n+1)/3⌋`, que es el presupuesto de un borrado de un vértice.
* `six_mul_targetSize_le` / `le_six_mul_targetSize_add_two` — el encuadre
  `n(n+1) − 2 ≤ 6·M(n) ≤ n(n+1)` (el residuo `n(n+1) % 6` vale `0` o `2`).
* `leafShell_budget_lt` — **la comparación decisiva**: si `1 ≤ r ≤ s` y `(r,s) ≠ (1,1)`,
  entonces `M(s+r) + C(r,2) < M(s) + s·r`.  Junto con la cota inferior de coste de
  `ExactReduction.ShellObstruction` esto prueba que la reducción por *una sola* bolsa hoja
  nunca cabe en el presupuesto cuando el separador es al menos tan grande como la parte
  privada.
-/

namespace ExactReduction

open PaperIV

/-- Forma cerrada de `M(6q+k) = ⌊(6q+k)(6q+k+1)/6⌋`. -/
theorem targetSize_formula (q k : ℕ) :
    targetSize (6 * q + k) = 6 * q ^ 2 + q * (2 * k + 1) + k * (k + 1) / 6 := by
  unfold targetSize
  have h : (6 * q + k) * (6 * q + k + 1)
      = 6 * (6 * q ^ 2 + q * (2 * k + 1)) + k * (k + 1) := by ring
  rw [h, Nat.mul_add_div (by norm_num)]

/-- Descomposición estándar `n = 6q + k` con `k < 6`. -/
private theorem exists_six_decomp (n : ℕ) : ∃ q k, k < 6 ∧ n = 6 * q + k :=
  ⟨n / 6, n % 6, Nat.mod_lt _ (by norm_num), by omega⟩

/-- **El paso exacto del objetivo.**  `M(n+1) = M(n) + ⌊(n+2)/3⌋`. -/
theorem targetSize_succ (n : ℕ) : targetSize (n + 1) = targetSize n + (n + 2) / 3 := by
  obtain ⟨q, k, hk, rfl⟩ := exists_six_decomp n
  interval_cases k
  · rw [show 6 * q + 0 + 1 = 6 * q + 1 by ring, targetSize_formula, targetSize_formula]; omega
  · rw [show 6 * q + 1 + 1 = 6 * q + 2 by ring, targetSize_formula, targetSize_formula]; omega
  · rw [show 6 * q + 2 + 1 = 6 * q + 3 by ring, targetSize_formula, targetSize_formula]; omega
  · rw [show 6 * q + 3 + 1 = 6 * q + 4 by ring, targetSize_formula, targetSize_formula]; omega
  · rw [show 6 * q + 4 + 1 = 6 * q + 5 by ring, targetSize_formula, targetSize_formula]; omega
  · rw [show 6 * q + 5 + 1 = 6 * (q + 1) + 0 by ring, targetSize_formula, targetSize_formula]
    ring_nf
    omega

/-- El coste exacto de borrar un vértice: `M(n) = M(n−1) + ⌊(n+1)/3⌋` para `n ≥ 1`. -/
theorem targetSize_sub_one (n : ℕ) (hn : 1 ≤ n) :
    targetSize n = targetSize (n - 1) + (n + 1) / 3 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simpa using targetSize_succ m

theorem targetSize_mono : Monotone targetSize := by
  intro a b hab
  exact Nat.div_le_div_right (Nat.mul_le_mul hab (by omega))

theorem six_mul_targetSize_le (n : ℕ) : 6 * targetSize n ≤ n * (n + 1) := by
  unfold targetSize
  rw [Nat.mul_comm]
  exact Nat.div_mul_le_self _ _

theorem le_six_mul_targetSize_add_two (n : ℕ) : n * (n + 1) ≤ 6 * targetSize n + 2 := by
  obtain ⟨q, k, hk, rfl⟩ := exists_six_decomp n
  rw [targetSize_formula]
  have h : (6 * q + k) * (6 * q + k + 1)
      = 6 * (6 * q ^ 2 + q * (2 * k + 1)) + k * (k + 1) := by ring
  rw [h]
  interval_cases k <;> omega

theorem two_mul_choose_two (r : ℕ) : 2 * r.choose 2 = r * (r - 1) := by
  cases r with
  | zero => simp
  | succ m =>
    obtain ⟨t, ht⟩ : Even (m * (m + 1)) := Nat.even_mul_succ_self m
    rw [Nat.choose_two_right]
    simp only [Nat.add_sub_cancel]
    rw [show (m + 1) * m = m * (m + 1) by ring, ht]
    omega

/-- **La comparación decisiva para la reducción por una bolsa hoja.**

Si el separador `S` es al menos tan grande como la parte privada `R` (y no estamos en el
caso trivial `|S| = |R| = 1`), entonces el presupuesto `M(s+r) − M(s)` es *estrictamente
menor* que `s·r − C(r,2)`, el coste mínimo de cualquier cubrimiento de la cáscara
(`ExactReduction.ShellObstruction.shellCover_card_ge`).  Enunciado sin restas de naturales. -/
theorem leafShell_budget_lt {s r : ℕ} (hr : 1 ≤ r) (hrs : r ≤ s) (hnt : 2 ≤ r ∨ 2 ≤ s) :
    targetSize (s + r) + r.choose 2 < targetSize s + s * r := by
  have h1 : 6 * targetSize (s + r) ≤ (s + r) * (s + r + 1) := six_mul_targetSize_le _
  have h2 : s * (s + 1) ≤ 6 * targetSize s + 2 := le_six_mul_targetSize_add_two _
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
  have h3 : 2 * (m + 1).choose 2 = (m + 1) * m := by
    have := two_mul_choose_two (m + 1); simpa using this
  have hexp : (s + (m + 1)) * (s + (m + 1) + 1)
      = s * (s + 1) + 2 * s * (m + 1) + (m + 1) * (m + 2) := by ring
  have hms : m + 1 ≤ s := hrs
  have key : 6 * (targetSize (s + (m + 1)) + (m + 1).choose 2)
      < 6 * (targetSize s + s * (m + 1)) := by
    rcases hnt with hm | hs
    · have hm1 : 1 ≤ m := by omega
      nlinarith [h1, h2, h3, hexp, hms, hm1]
    · have hs2 : 2 ≤ s := hs
      nlinarith [h1, h2, h3, hexp, hms, hs2]
  omega

end ExactReduction
