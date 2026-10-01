import PaperIV.FarRounding
import ThreeRegime.CentreDefectArithmetic
import Mathlib.Tactic.IntervalCases

/-!
# La obligación que queda en un estado completo

Los módulos `CompleteStateExtreme` y `CompleteStateSeparator` muestran que en
un estado completo `K_n` las rutas extrema y del separador no están
disponibles.  Toda la carga recae entonces sobre la ruta del centro, y aquí se
reduce esa carga a un enunciado **puramente de diseño combinatorio**, sin
ninguna circularidad de contabilidad:

* `centre_closes_of_packing_gain`: la contabilidad ya está hecha; basta un
  empaquetamiento físico mixto con ganancia suficiente.
* `centre_closes_of_triangle_packing`: en forma de recuento, basta un
  empaquetamiento de triángulos arista-disjuntos de `K_n` con al menos
  `n(n-2)/6` triángulos.

Esa cantidad es exactamente la que producen los sistemas de ternas parciales
máximos de `K_n` (descomposiciones triangulares con *leave* de a lo sumo `n/2`
aristas).  Formalizar esa familia de construcciones (tipo Bose/Skolem) es la
obligación abierta para los estados completos; no se afirma aquí.
-/

namespace ThreeRegime

open Finset PaperIV PaperIV.FarRounding SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Contabilidad del centro en un estado completo.**  Un empaquetamiento
físico mixto con ganancia suficiente cierra la ruta del centro. -/
theorem centre_closes_of_packing_gain (P : Packing (⊤ : SimpleGraph V))
    (hgain : 6 * Nat.choose (Fintype.card V) 2 ≤
      6 * P.gain + Fintype.card V * (Fintype.card V + 1)) :
    ∃ Q : CliquePartition (⊤ : SimpleGraph V),
      Q.OrderAtMost 4 ∧ Q.size ≤ PaperIV.targetSize (Fintype.card V) := by
  obtain ⟨Q, hQ4, hQsize⟩ := exists_cliquePartition_of_packing P
  refine ⟨Q, hQ4, ?_⟩
  have hedges : (⊤ : SimpleGraph V).edgeFinset.card =
      Nat.choose (Fintype.card V) 2 :=
    SimpleGraph.card_edgeFinset_top_eq_card_choose_two
  rw [hedges] at hQsize
  rw [PaperIV.targetSize, Nat.le_div_iff_mul_le (by norm_num)]
  omega

/-- La ganancia de un empaquetamiento de triángulos es el doble del número de
triángulos. -/
theorem gain_of_all_triangles (P : Packing (⊤ : SimpleGraph V))
    (htri : ∀ K ∈ P.pieces, K.card = 3) :
    P.gain = 2 * P.pieces.card := by
  rw [Packing.gain, Finset.sum_congr rfl (fun K hK => gainOf_of_card_eq_three (htri K hK))]
  simp [Nat.mul_comm]

/-- Aritmética del recuento de triángulos. -/
theorem triangle_count_arith (n t : ℕ) (h : n * (n - 2) ≤ 6 * t) :
    6 * Nat.choose n 2 ≤ 6 * (2 * t) + n * (n + 1) := by
  have hchoose : 6 * Nat.choose n 2 = 3 * (n * (n - 1)) := six_mul_choose_two n
  rcases Nat.lt_or_ge n 2 with hs | hb
  · interval_cases n <;> simp_all
  · obtain ⟨j, rfl⟩ : ∃ j, n = j + 2 := ⟨n - 2, by omega⟩
    simp only [Nat.add_sub_cancel] at h hchoose
    have hj : j + 2 - 1 = j + 1 := by omega
    rw [hchoose, hj]
    nlinarith [h]

/-- **Forma de recuento de la obligación abierta.**  Un empaquetamiento de
triángulos arista-disjuntos de `K_n` con al menos `n(n-2)/6` triángulos cierra
la ruta del centro con presupuesto agudo. -/
theorem centre_closes_of_triangle_packing (P : Packing (⊤ : SimpleGraph V))
    (htri : ∀ K ∈ P.pieces, K.card = 3)
    (hcount : Fintype.card V * (Fintype.card V - 2) ≤ 6 * P.pieces.card) :
    ∃ Q : CliquePartition (⊤ : SimpleGraph V),
      Q.OrderAtMost 4 ∧ Q.size ≤ PaperIV.targetSize (Fintype.card V) := by
  refine centre_closes_of_packing_gain P ?_
  rw [gain_of_all_triangles P htri]
  exact triangle_count_arith _ _ hcount

/-- **Estabilidad del recuento bajo el paso tripartito.**  Si `K_m` admite un
empaquetamiento con `t` triángulos que cumple el recuento, entonces el
recuento para `K_{3m}` se cumple con `m² + 3t` triángulos: exactamente lo que
produce un cuadrado latino de orden `m` sobre las aristas cruzadas de tres
grupos de tamaño `m`, más la recursión dentro de cada grupo.  La identidad es
ajustada, sin holgura sobrante. -/
theorem triangle_count_tripartite_step (m t : ℕ) (h : m * (m - 2) ≤ 6 * t) :
    (3 * m) * (3 * m - 2) ≤ 6 * (m * m + 3 * t) := by
  rcases Nat.lt_or_ge m 2 with hs | hb
  · interval_cases m <;> omega
  · obtain ⟨j, rfl⟩ : ∃ j, m = j + 2 := ⟨m - 2, by omega⟩
    simp only [Nat.add_sub_cancel] at h
    have h3 : 3 * (j + 2) - 2 = 3 * j + 4 := by omega
    rw [h3]
    nlinarith [h]

end ThreeRegime
