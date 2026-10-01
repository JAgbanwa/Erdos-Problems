import PaperIV.DenseBagClosure

/-!
# (A) es *equivalente* al gap de integralidad cordal

`ChordalBridge.assignmentLossOwnAt_of_integralityGap` demuestra una dirección: si el gap
de integralidad de los cordales es `≤ ζn²`, entonces `AssignmentLossOwnAt ζ`. Aquí se
demuestra **la recíproca**, y por tanto la equivalencia.

## El enunciado

```
AssignmentLossOwnAt ζ   ⟺   ∀ cordal grande, ∃ packing entero a distancia ≤ ζn² del óptimo fraccional
```

## Qué significa, y es una mala noticia que conviene tener por escrito

La descomposición (A) + (B1) + (B2) **no debilita la hipótesis**. No es que repartir
aristas entre bolsas sea un problema más fácil que redondear globalmente: es *el mismo
problema*, reescrito. Ninguna regla de asignación, por ingeniosa que sea, puede cerrar (A)
sin cerrar de paso el gap de integralidad cordal completo.

Eso explica de golpe las tres vías que probé y descarté:

* **Donación por emparejamientos** (`DonationBudget`): tope `(2/3)e`, pierde `e/6`.
* **Cota local por `(5/6)e`** (`DenseBagClosure`): su hipótesis sólo vale para grafos que
  son casi una única clique.
* **`R1` canónica vs `R5` guiada por LP** (`E01_BRIDGE_STATUS.md` §11.3): `R1` produce
  **sólo** bolsas split —que `SplitBagExact` redondea *exactamente*, pérdida cero— pero su
  pérdida de asignación es `Θ(n²)`; `R5` tiene pérdida pequeña pero produce bolsas que no
  son ni split ni clique. **La equivalencia dice por qué no se puede tener las dos cosas:**
  la suma de ambas pérdidas *es* el gap, y ninguna redistribución entre los dos sumandos lo
  hace desaparecer.

## Entonces, ¿cómo se cierra (A)?

No con una regla de asignación. La equivalencia deja una única vía: **demostrar el gap**,
y la descomposición sólo sirve para elegir *dónde* pagarlo. La ruta concreta que sí
sobrevive es:

1. una asignación cuyas bolsas sean **todas** split o **densas** dentro de su clique;
2. `SplitBagExact.split_bag_exact` para las split (pérdida **cero**, demostrado);
3. `DenseBagClosure.DenseBagNibbleAt` para las densas — que es la instancia `r = 6` del
   nibble ponderado **ya demostrado** en Paper III
   (`Nibble.fracNibbleWeighted_nearPerfect`).

El único hueco de esa ruta es (1), y por la equivalencia (1) no es un problema de conteo
sino **estructural**: exhibir, para todo cordal, un reparto de aristas en el que cada
bolsa quede split o densa. Es una pregunta sobre árboles de cliques, no sobre LPs, y es
donde conviene poner el esfuerzo.
-/

namespace PaperIV.AssignmentEquivalence

open Finset
open PaperIV.FarRounding
open PaperIV.AssignmentLemma

/-- El gap de integralidad de los grafos cordales, en la forma que usa la ruta. -/
def ChordalIntegralityGapAt (ζ : ℚ) : Prop :=
  ∃ T : ℕ, ∀ n : ℕ, T ≤ n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    IsChordal G → ∀ w : ℚ, CertifiedFractionalOptimum G w →
      ∃ P : Packing G, w - (P.gain : ℚ) ≤ ζ * (n : ℚ) ^ 2

/-- **La recíproca.**  Una asignación con pérdida `ζn²` produce, ensamblando, un packing
entero a distancia `ζn²` del óptimo fraccional: es decir, acota el gap de integralidad.

La prueba es `AssignmentLemma.exists_packing_of_ownership` aplicada a los packings por
bolsa que la hipótesis entrega. -/
theorem chordalIntegralityGapAt_of_assignmentLossOwnAt {ζ : ℚ}
    (h : AssignmentLossOwnAt ζ) : ChordalIntegralityGapAt ζ := by
  obtain ⟨T, hT⟩ := h
  refine ⟨T, ?_⟩
  intro n hn G _ hchord w hw
  obtain ⟨Bs, own, P, hsupp, hloss⟩ := hT n hn G hchord w hw
  obtain ⟨Q, hQ⟩ := exists_packing_of_ownership Bs own P hsupp
  refine ⟨Q, ?_⟩
  have hcast : (Q.gain : ℚ) = ∑ b ∈ Bs, ((P b).gain : ℚ) := by
    rw [hQ]; push_cast; ring
  rw [hcast]
  exact hloss

/-- **La equivalencia.**  `AssignmentLossOwnAt ζ` y el gap de integralidad cordal `≤ ζn²`
son el mismo enunciado.

Consecuencia, dicha sin adornos: **ninguna regla de asignación puede cerrar (A) sin
demostrar el gap**.  La descomposición por bolsas elige dónde pagar la pérdida; no la
reduce. -/
theorem assignmentLossOwnAt_iff_gap {ζ : ℚ} :
    AssignmentLossOwnAt ζ ↔ ChordalIntegralityGapAt ζ :=
  ⟨chordalIntegralityGapAt_of_assignmentLossOwnAt,
   PaperIV.ChordalBridge.assignmentLossOwnAt_of_integralityGap⟩

/-- El corolario operativo: el redondeo lejano se sigue del gap cordal, y **sólo** de él.
Encadena `assignmentLossOwnAt_iff_gap` con
`AssignmentLemma.farRoundingAt_of_assignmentLossOwn`. -/
theorem farRoundingAt_of_chordalGap {η : ℚ} (h : ChordalIntegralityGapAt (η / 2)) :
    FarRoundingAt η :=
  farRoundingAt_of_assignmentLossOwn (assignmentLossOwnAt_iff_gap.2 h)

end PaperIV.AssignmentEquivalence
