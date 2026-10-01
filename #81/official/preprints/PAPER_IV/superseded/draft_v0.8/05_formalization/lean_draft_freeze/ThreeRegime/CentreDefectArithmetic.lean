import PaperIV.TargetEnvelope
import Mathlib.Tactic

/-!
# Aritmética de la reserva exacta de defecto central

`centerDefect n k` es la distancia del tamaño de raíz `k` a los maximizadores
enteros de la parábola completo-split, y `targetSize (centerDefect n k)` es la
reserva exacta que la ruta extrema exporta (identidad
`M(n) = coste_split(n,k) + M(centerDefect n k)`).

Aquí se demuestra la comparación aritmética que usa el módulo
`ThreeRegime.CompleteStateExtreme`: en la banda equilibrada `k ≤ n - k`, esa
reserva es **estrictamente menor** que `C(n-k, 2)`, el número de aristas que
hay que añadir a un completo-split para llegar al grafo completo.
-/

namespace ThreeRegime

open PaperIV

/-- Distancia a los dos maximizadores enteros de la parábola completo-split. -/
def centerDefect (n k : ℕ) : ℕ :=
  if 3 * k ≤ n then n - 3 * k else 3 * k - n - 1

theorem targetSize_mono {a b : ℕ} (h : a ≤ b) : targetSize a ≤ targetSize b :=
  Nat.div_le_div_right (Nat.mul_le_mul h (Nat.succ_le_succ h))

/-- En la banda equilibrada el defecto central nunca supera el tamaño del lado
independiente. -/
theorem centerDefect_le_outside (n k : ℕ) (hk : 1 ≤ k) (hband : k ≤ n - k) :
    centerDefect n k ≤ n - k := by
  have hkn : k ≤ n := by omega
  unfold centerDefect
  split <;> omega

/-- `C(m,2)` en forma explícita. -/
theorem choose_two_eq (m : ℕ) : Nat.choose m 2 = m * (m - 1) / 2 :=
  Nat.choose_two_right m

theorem two_mul_choose_two (m : ℕ) : 2 * Nat.choose m 2 = m * (m - 1) := by
  rw [Nat.choose_two_right, Nat.mul_comm 2,
    Nat.div_mul_cancel (Nat.even_mul_pred_self m).two_dvd]

theorem six_mul_choose_two (m : ℕ) : 6 * Nat.choose m 2 = 3 * (m * (m - 1)) := by
  have := two_mul_choose_two m
  omega

/-- Para `m ≥ 3` el presupuesto agudo de `m` es estrictamente menor que el
número de aristas de `K_m`. -/
theorem targetSize_lt_choose_two {m : ℕ} (hm : 3 ≤ m) :
    targetSize m < Nat.choose m 2 := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 3 := ⟨m - 3, by omega⟩
  rw [targetSize, Nat.div_lt_iff_lt_mul (by norm_num)]
  have h6 : 6 * Nat.choose (j + 3) 2 = 3 * ((j + 3) * (j + 2)) := by
    have := six_mul_choose_two (j + 3)
    simpa using this
  nlinarith [h6]

/-- **La reserva exacta de la ruta extrema no paga el arreglo en un estado
completo.**  En la banda equilibrada `1 ≤ k ≤ n - k` con `n ≥ 4`, la reserva
`M(centerDefect n k)` es estrictamente menor que `C(n-k,2)`. -/
theorem reserve_lt_missing (n k : ℕ) (hk : 1 ≤ k) (hband : k ≤ n - k)
    (hn : 4 ≤ n) :
    targetSize (centerDefect n k) < Nat.choose (n - k) 2 := by
  have hkn : k ≤ n := by omega
  by_cases hm : 3 ≤ n - k
  · exact lt_of_le_of_lt
      (targetSize_mono (centerDefect_le_outside n k hk hband))
      (targetSize_lt_choose_two hm)
  · -- forzosamente `n = 4`, `k = 2`
    have hk2 : k = 2 := by omega
    have hn4 : n = 4 := by omega
    subst hk2; subst hn4
    norm_num [centerDefect, targetSize]

end ThreeRegime
