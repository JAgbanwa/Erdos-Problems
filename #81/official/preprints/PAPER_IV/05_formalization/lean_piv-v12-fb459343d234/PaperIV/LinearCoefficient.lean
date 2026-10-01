import PaperIV.PaperTheorems

/-!
# BP-05 — el coeficiente lineal `1/6` es óptimo

La cota eventual dice `cp₄(G) ≤ n²/6 + n/6` para todo cordal grande. Este módulo demuestra que el
`1/6` del término lineal **no se puede bajar**, ni siquiera admitiendo una constante aditiva
arbitraria.

```text
∀ c < 1/6, ∀ B, ∃ N, ∀ n ≥ N, existe un cordal de orden `n` en el que
   toda partición en cliques tiene más de  n²/6 + c·n + B  piezas.
```

La suficiencia ya está (`PaperTheorems.erdos81_hybrid_linear_form`). Lo que se añade aquí es la
**necesidad**, y sale del mismo testigo extremal: el completo-split crítico alcanza `targetSize n`,
que difiere de `n²/6 + n/6` en menos de una unidad por ser un suelo. Cualquier coeficiente menor
que `1/6` queda por debajo en cuanto `n` crece, porque la diferencia `(1/6 − c)·n` es lineal y la
holgura que hay que superar —`B` más el error de suelo— es constante.

## Alcance

Esto es un **corolario de empaquetado**, no un teorema principal: no aporta matemática nueva sobre
el problema, sólo fija que el par `(1/6, 1/6)` es óptimo en su segundo término. Tampoco dice nada
sobre la menor constante válida para órdenes pequeños, que es una pregunta distinta.

La cota inferior vale sobre **todas** las particiones en cliques, sin restricción de orden, porque
es la que hereda de `SplitCompleteSharpValue`.
-/

namespace PaperIV.LinearCoefficient

open PaperIV.FarRounding

/-- El suelo `targetSize n` se queda a menos de una unidad de `n(n+1)/6`. -/
private theorem targetSize_ge (n : ℕ) :
    ((n : ℚ) ^ 2) / 6 + (n : ℚ) / 6 - 1 ≤ (PaperIV.targetSize n : ℚ) := by
  have h : n * (n + 1) < 6 * PaperIV.targetSize n + 6 := by
    unfold PaperIV.targetSize; omega
  have hQ : ((n : ℚ)) * ((n : ℚ) + 1) < 6 * (PaperIV.targetSize n : ℚ) + 6 := by
    exact_mod_cast h
  nlinarith [hQ]

/-- **BP-05.  El coeficiente lineal `1/6` es el menor admisible.**

Para cualquier `c < 1/6` y cualquier constante aditiva `B`, en todos los órdenes suficientemente
grandes existe un grafo cordal en el que **ninguna** partición en cliques baja de
`n²/6 + c·n + B`. -/
theorem linear_coefficient_optimal (c B : ℚ) (hc : c < 1 / 6) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj),
        SimpleGraph.IsChordal G ∧
        ∀ Q : CliquePartition G, (n : ℚ) ^ 2 / 6 + c * (n : ℚ) + B < (Q.size : ℚ) := by
  classical
  have hpos : 0 < 1 / 6 - c := by linarith
  -- basta que `(1/6 − c)·n` supere la holgura constante `B + 1`
  obtain ⟨M, hM⟩ := exists_nat_gt ((B + 1) / (1 / 6 - c))
  refine ⟨max M 6, ?_⟩
  intro n hn
  have hn6 : 6 ≤ n := le_trans (le_max_right M 6) hn
  have hnM : M ≤ n := le_trans (le_max_left M 6) hn
  obtain ⟨G, hdec, hchord, Q, -, hQsize, hQopt⟩ :=
    PaperIV.PaperTheorems.exists_chordal_extremal_witness hn6
  refine ⟨G, hdec, hchord, ?_⟩
  intro R
  -- toda partición tiene al menos `targetSize n` piezas
  have hRge : PaperIV.targetSize n ≤ R.size := by
    have := hQopt R
    omega
  have hRgeQ : ((PaperIV.targetSize n : ℕ) : ℚ) ≤ (R.size : ℚ) := by exact_mod_cast hRge
  have hfloor := targetSize_ge n
  -- y `n` es lo bastante grande para absorber `B` y el error de suelo
  have hnQ : (B + 1) / (1 / 6 - c) < (n : ℚ) := by
    have : ((M : ℚ)) ≤ (n : ℚ) := by exact_mod_cast hnM
    linarith
  have hkey : B + 1 < (1 / 6 - c) * (n : ℚ) := by
    have h := mul_lt_mul_of_pos_right hnQ hpos
    rw [div_mul_cancel₀] at h
    · linarith
    · exact ne_of_gt hpos
  linarith

end PaperIV.LinearCoefficient
