import PaperIV.FarRounding
import PaperIV.TargetEnvelope

/-!
# El Contrato D de Paper VI (NB08) **es** la entrada lejana de Paper IV

Puente entre la ruta candidata R2/R3 de Paper VI y la formalización de Paper IV.

## Qué dice el contrato de Paper VI

> **Contrato D — NB08.** Para cada `ε > 0` fijo existe un umbral uniforme `N_NB(ε)` tal que todo
> packing fraccional mixto factible en un grafo suficientemente grande se redondea a un packing
> físico perdiendo menos de `ε n²` de ganancia.

Es, literalmente, un `def : Prop` con esa forma.  Aquí se enuncia en los tipos de Paper IV
como `UniformRoundingAt`.

## Qué se demuestra

* `uniformTransferAt_of_uniformRoundingAt` — NB08 implica `FarRounding.UniformTransferAt`;
* `uniformRoundingAt_of_uniformTransferAt` — y al revés, si todo grafo tiene óptimo certificado.

Es decir: **son la misma obligación**, no dos entradas distintas.

**Estado, con la distinción que importa.**  *En Lean* los dos lados son `def : Prop` sin nada
que los concluya, allí y aquí.  *Matemáticamente* el handoff R2 §12.3 afirma que «existe una
prueba matemática autocontenida NB08» y clasifica el punto como **gate de formalización**, no
como problema abierto.  Esa prueba no está auditada aquí.  Si se sostiene, lo que falta es
formalizarla — y formalizarla **descarga las dos arquitecturas a la vez**, que es justamente
lo que este módulo deja comprobado por máquina.

* `farRegime_of_uniformRounding` — y NB08 basta para toda la conclusión lejana ya formalizada
  (`FarRounding.farRegime_cliquePartition`): partición en cliques de orden `≤ 4` con
  `size ≤ M(n)`.

## Consecuencia para la comparación de rutas

La rama lejana de Paper VI y la de Paper IV **no son alternativas**: consumen el mismo teorema.
Por tanto el programa RP01 —adaptador de regularidad, conteo de patrón, momentos, limpieza— es
el camino para descargar el Contrato D, no un competidor suyo.

Lo que Paper VI **sí** evita es el rodeo por el *gap* de integralidad cordal: va de NB08 a `cp`
directamente, con la misma aritmética de `farRegime_cliquePartition`.  La equivalencia
`AssignmentEquivalence.assignmentLossOwnAt_iff_gap` deja de ser necesaria para el cierre.
-/

namespace PaperIV.NB08Interface

open Finset
open PaperIV.FarRounding

/-- **Contrato D (NB08)** en la forma «redondeo numérico»: *todo* packing fraccional se redondea
perdiendo a lo sumo `ζ n²`.  Nótese que no menciona óptimos ni duales. -/
def UniformRoundingAt (ζ : ℚ) : Prop :=
  ∃ T : ℕ, ∀ n : ℕ, T ≤ n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : FracPacking G ℚ), ∃ P : Packing G, x.value - (P.gain : ℚ) ≤ ζ * (n : ℚ) ^ 2

/-- **NB08 ⟹ la entrada lejana de Paper IV.**  Un óptimo certificado trae su testigo primal, y
redondearlo es exactamente lo que `UniformTransferAt` pide. -/
theorem uniformTransferAt_of_uniformRoundingAt {ζ : ℚ} (h : UniformRoundingAt ζ) :
    UniformTransferAt ζ := by
  obtain ⟨T, hT⟩ := h
  refine ⟨T, ?_⟩
  intro n hn G _ w hw
  obtain ⟨x, -, hx, -⟩ := id hw
  obtain ⟨P, hP⟩ := hT n hn G x
  exact ⟨P, by rw [← hx]; exact hP⟩

/-- **Y al revés**, si todo grafo tiene un óptimo fraccional certificado: cualquier packing
fraccional está por debajo del óptimo, así que redondear el óptimo basta.

La hipótesis `hcert` es el `AllCertificates` del export de la ruta alternativa. -/
theorem uniformRoundingAt_of_uniformTransferAt {ζ : ℚ}
    (hcert : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj),
      ∃ w : ℚ, CertifiedFractionalOptimum G w)
    (h : UniformTransferAt ζ) : UniformRoundingAt ζ := by
  obtain ⟨T, hT⟩ := h
  refine ⟨T, ?_⟩
  intro n hn G inst x
  obtain ⟨w, hw⟩ := hcert n G inst
  obtain ⟨P, hP⟩ := hT n hn G w hw
  refine ⟨P, ?_⟩
  have hle : x.value ≤ w := certified_isOptimum hw x
  linarith

/-- **NB08 cierra la rama lejana, tal cual.**  Encadenando con lo ya formalizado:
`UniformRoundingAt → UniformTransferAt → FarRoundingAt → farRegime_cliquePartition`.

Es, salvo el nombre de los parámetros, la rama lejana de la ruta R3 de Paper VI. -/
theorem farRegime_of_uniformRounding {η : ℚ} (hη : 0 ≤ η) (h : UniformRoundingAt (η / 2)) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      IsChordal G → ∀ w : ℚ, CertifiedFractionalOptimum G w →
        (G.edgeFinset.card : ℚ) - w < (n : ℚ) ^ 2 / 6 - η * (n : ℚ) ^ 2 →
          ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size ≤ targetSize n :=
  farRegime_cliquePartition hη
    (farRoundingAt_of_uniformTransferAt (uniformTransferAt_of_uniformRoundingAt h))

/-! ## El objetivo `M(n)` **es** Erdős #81 con error lineal explícito -/

/-- **Orden lineal.**  De `cp≤4(G) ≤ M(n) + B` se sigue

```
cp(G) ≤ n²/6 + (1/6 + B)·n
```

para todo `n ≥ 1`, con `B` una constante absoluta.  Es decir, la conclusión de la ruta R3 no
es `n²/6 + o(n²)` sino la forma (1.1) del problema, con constante explícita `C = 1/6 + B`. -/
theorem erdos81_linear_of_target {n : ℕ} (hn : 1 ≤ n) {c B : ℚ} (hB : 0 ≤ B)
    (h : c ≤ ((PaperIV.targetSize n : ℕ) : ℚ) + B) :
    c ≤ (n : ℚ) ^ 2 / 6 + (1 / 6 + B) * (n : ℚ) := by
  have h1 : ((PaperIV.targetSize n : ℕ) : ℚ) ≤ (n : ℚ) * ((n : ℚ) + 1) / 6 :=
    PaperIV.targetSize_cast_le_continuous n
  have hn1 : (1 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
  nlinarith [h, h1, hn1, hB]

end PaperIV.NB08Interface
