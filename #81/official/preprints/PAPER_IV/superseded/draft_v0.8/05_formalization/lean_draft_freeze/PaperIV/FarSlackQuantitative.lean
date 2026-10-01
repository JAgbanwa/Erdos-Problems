import PaperIV.RC01FarAssembly
import PaperIV.TargetEnvelope

/-!
# La rama lejana, conservando el margen

`PaperIV.RC01FarAssembly.farRegime_cliquePartition` cierra la rama lejana con la conclusión
`Q.size ≤ targetSize n`.  Esa conclusión es la que necesita el teorema principal, pero
**pierde** el margen: la demostración interna obtiene primero

```text
Q.size < n²/6 − η n²/2
```

y luego redondea hacia `targetSize n`.  Para un enunciado de estabilidad con déficit `δ`
variable ese redondeo es fatal: de `Q.size ≤ targetSize n` no se deduce nada que contradiga
`c₄(G) ≥ targetSize n − δ`.

Este módulo vuelve a montar la rama lejana **sin** el paso de redondeo, a partir de la misma
entrada `FarRoundingAt η` que ya está demostrada incondicionalmente en `RC01FarAssembly`.  No
se modifica ningún enunciado existente: se añade la variante cuantitativa.

El margen que se conserva es `η n²/2`, exactamente la mitad de la holgura cuadrática que
define la rama lejana.  Es lo que fija la constante `γ` de BP-01.
-/

namespace PaperIV.FarSlackQuantitative

open PaperIV.FarRounding

/-- **Rama lejana cuantitativa.**  En el régimen con holgura cuadrática `η n²`, la partición
en cliques producida por el redondeo mixto no sólo cabe en `targetSize n`: queda por debajo
de `n²/6` con margen `η n²/2`. -/
theorem farRegime_cliquePartition_slack (η : ℚ) (hη : 0 < η) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      IsChordal G → ∀ w : ℚ, CertifiedFractionalOptimum G w →
        (G.edgeFinset.card : ℚ) - w < (n : ℚ) ^ 2 / 6 - η * (n : ℚ) ^ 2 →
          ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧
            (Q.size : ℚ) < (n : ℚ) ^ 2 / 6 - η * (n : ℚ) ^ 2 / 2 := by
  obtain ⟨T, hT⟩ := PaperIV.RC01FarAssembly.farRoundingAt η hη
  refine ⟨T, ?_⟩
  intro n hn G _ hG w hw hfar
  obtain ⟨P, hP⟩ := hT n hn G hG w hw hfar
  obtain ⟨Q, hQ4, hQsize⟩ := exists_cliquePartition_of_packing P
  refine ⟨Q, hQ4, ?_⟩
  have hsize : (Q.size : ℚ) + (P.gain : ℚ) = (G.edgeFinset.card : ℚ) := by
    exact_mod_cast hQsize
  linarith

/-- El objetivo entero domina a `n²/6` en cuanto `n ≥ 5`: `targetSize n = ⌊n(n+1)/6⌋` y el
término lineal `n/6` absorbe la pérdida de la parte entera. -/
theorem sq_div_six_le_targetSize {n : ℕ} (hn : 5 ≤ n) :
    (n : ℚ) ^ 2 / 6 ≤ (PaperIV.targetSize n : ℚ) := by
  have hdiv := Nat.div_add_mod (n * (n + 1)) 6
  have hmod : (n * (n + 1)) % 6 < 6 := Nat.mod_lt _ (by norm_num)
  have hnat : n * n + n ≤ 6 * PaperIV.targetSize n + 5 := by
    have : n * (n + 1) ≤ 6 * PaperIV.targetSize n + 5 := by
      rw [PaperIV.targetSize]; omega
    nlinarith [this]
  have hQ : ((n : ℚ) * (n : ℚ) + (n : ℚ)) ≤ 6 * (PaperIV.targetSize n : ℚ) + 5 := by
    have h := (Nat.cast_le (α := ℚ)).mpr hnat
    push_cast at h
    linarith
  have hn5 : (5 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
  nlinarith

end PaperIV.FarSlackQuantitative
