import PaperIV.PaperTheorems
import PaperIV.Erdos81AllOrders

set_option maxHeartbeats 1000000

/-!
# La constante cuadrática `1/6` es óptima

`PaperIV.Erdos81AllOrders.erdos81_all_orders` da, para **todos** los órdenes, una
partición en cliques de tamaño `≤ n²/6 + C·n`.  Lo que el árbol no decía es que
el `1/6` no se puede bajar: eso requiere una familia cordal que **ninguna**
partición en cliques —sin restricción de orden— pueda cubrir con menos de
`M(n) = ⌊n(n+1)/6⌋` piezas, y esa familia ya existe en el árbol
(`PaperIV.PaperTheorems.exists_chordal_extremal_witness`, el completo-split
crítico, válido para todo `n ≥ 6`).

Este módulo junta las dos mitades:

* `erdos81_quadratic_constant_optimal` — si una cota `c·n² + C·n` vale para todos
  los cordales de orden grande, entonces `1/6 ≤ c`.  Vale incluso permitiendo
  particiones con piezas de orden arbitrario, y sin pedir `C ≥ 0`;
* `erdos81_quadratic_constant_isLeast` — `1/6` es el **mínimo** del conjunto de
  constantes cuadráticas admisibles.  La pertenencia es el teorema de todos los
  órdenes; la minimalidad es el punto anterior.

La demostración de la optimalidad es la comparación en un solo orden bien
elegido: si `c < 1/6`, el defecto `(1/6 − c)·n²` crece más deprisa que el término
lineal `C·n`, así que basta tomar `n` arquimedianamente grande y evaluar la cota
en el testigo extremal.
-/

namespace PaperIV.SharpConstantOptimality

open PaperIV.FarRounding

/-- El objetivo entero pierde a lo sumo `1` frente al racional `n(n+1)/6`. -/
theorem targetSize_ge (n : ℕ) :
    ((n : ℚ) ^ 2 + (n : ℚ)) / 6 - 1 ≤ (PaperIV.targetSize n : ℚ) := by
  have hdiv : n * (n + 1) < 6 * (PaperIV.targetSize n) + 6 := by
    have h := Nat.div_add_mod (n * (n + 1)) 6
    have hlt : n * (n + 1) % 6 < 6 := Nat.mod_lt _ (by norm_num)
    unfold PaperIV.targetSize
    omega
  have hQ : ((n * (n + 1) : ℕ) : ℚ) < 6 * (PaperIV.targetSize n : ℚ) + 6 := by
    exact_mod_cast hdiv
  push_cast at hQ
  nlinarith [hQ]

/-- **La constante cuadrática no puede bajar de `1/6`.**  Si toda familia cordal
de orden al menos `N` admite una partición en cliques de tamaño `≤ c·n² + C·n`,
entonces `1/6 ≤ c`.  No se pide nada sobre el orden de las piezas. -/
theorem erdos81_quadratic_constant_optimal {c C : ℚ} {N : ℕ}
    (h : ∀ n : ℕ, N ≤ n → ∀ (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj),
      SimpleGraph.IsChordal G → ∃ Q : CliquePartition G, (Q.size : ℚ) ≤ c * (n : ℚ) ^ 2 +
        C * (n : ℚ)) :
    1 / 6 ≤ c := by
  by_contra hc
  push_neg at hc
  set d : ℚ := 1 / 6 - c with hd
  have hd0 : 0 < d := by simp only [hd]; linarith
  obtain ⟨m, hm⟩ := exists_nat_gt ((6 * (|C| + 1)) / d)
  set n : ℕ := max m (max N 6) with hn
  have hnm : (m : ℚ) ≤ (n : ℚ) := by exact_mod_cast le_max_left m (max N 6)
  have hnN : N ≤ n := le_trans (le_max_left N 6) (le_max_right m _)
  have hn6 : 6 ≤ n := le_trans (le_max_right N 6) (le_max_right m _)
  have hnBig : (6 * (|C| + 1)) / d < (n : ℚ) := lt_of_lt_of_le hm hnm
  have hnQ6 : (6 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn6
  have hkey : 6 * (|C| + 1) < d * (n : ℚ) := by
    rw [div_lt_iff₀ hd0] at hnBig
    linarith [hnBig]
  -- el testigo extremal del orden elegido
  obtain ⟨G, hGdec, hGchordal, Q₀, -, hQ₀size, hQ₀opt⟩ :=
    PaperIV.PaperTheorems.exists_chordal_extremal_witness hn6
  obtain ⟨Q, hQ⟩ := h n hnN G hGdec hGchordal
  have hlow : (PaperIV.targetSize n : ℚ) ≤ (Q.size : ℚ) := by
    have := hQ₀opt Q
    rw [hQ₀size] at this
    exact_mod_cast this
  have htarget := targetSize_ge n
  have hn0 : (0 : ℚ) < (n : ℚ) := by linarith
  have habs : C * (n : ℚ) ≤ |C| * (n : ℚ) :=
    mul_le_mul_of_nonneg_right (le_abs_self C) (le_of_lt hn0)
  -- contradicción: el defecto cuadrático supera al término lineal
  have hcontra : d * (n : ℚ) ^ 2 ≤ |C| * (n : ℚ) + 1 := by
    have h1 : ((n : ℚ) ^ 2 + (n : ℚ)) / 6 - 1 ≤ c * (n : ℚ) ^ 2 + C * (n : ℚ) :=
      le_trans htarget (le_trans hlow hQ)
    simp only [hd]
    linarith
  nlinarith [hkey, hn0, hnQ6, abs_nonneg C]

/-- **`1/6` es la menor constante cuadrática admisible.**  Pertenece al conjunto
—es el teorema de todos los órdenes— y lo minora —es el punto anterior—. -/
theorem erdos81_quadratic_constant_isLeast :
    IsLeast {c : ℚ | ∃ (C : ℚ) (N : ℕ), ∀ n : ℕ, N ≤ n →
      ∀ (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj), SimpleGraph.IsChordal G →
        ∃ Q : CliquePartition G, (Q.size : ℚ) ≤ c * (n : ℚ) ^ 2 + C * (n : ℚ)}
      (1 / 6) := by
  constructor
  · obtain ⟨C, -, hC⟩ := PaperIV.Erdos81AllOrders.erdos81_all_orders
    refine ⟨C, 0, ?_⟩
    intro n _ G hGdec hG
    letI := hGdec
    obtain ⟨Q, -, hQ⟩ := hC n G hG
    exact ⟨Q, by linarith [hQ]⟩
  · rintro c ⟨C, N, hc⟩
    exact erdos81_quadratic_constant_optimal hc

end PaperIV.SharpConstantOptimality
