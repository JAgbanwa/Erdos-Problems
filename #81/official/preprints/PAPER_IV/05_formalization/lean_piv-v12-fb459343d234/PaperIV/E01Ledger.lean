import PaperIV.TwoRegimeAccounting

/-!
# El libro mayor de E01: la cadena completa, y exactamente lo que falta

Este módulo existe para responder a una pregunta concreta —*¿está resuelto E01?*— sin
prosa: encadena todo lo demostrado hasta `FarRounding.FarRoundingAt η` y deja el residuo
como **una sola definición**, `TwoRegimeRouteAt`, cuyas cláusulas son literalmente lo que
queda por probar.

## La cadena

```
TwoRegimeRouteAt (η/2)                     ← ÚNICA hipótesis restante
    ⟹ AssignmentLemma.AssignmentLossOwnAt (η/2)     (aquí)
    ⟹ FarRounding.FarRoundingAt η                    (AssignmentLemma)
    ⟹ partición en ≤ n²/6 + O(n) piezas              (FarRounding.farRegime_cliquePartition)
```

Todo lo anterior está demostrado. `TwoRegimeRouteAt` **no**.

## Qué contiene `TwoRegimeRouteAt ζ`, cláusula por cláusula

Para todo cordal grande y todo óptimo fraccional certificado, existe un reparto de aristas
`own` y una partición de las bolsas en `Bs` (split) y `Bd` (densas) tales que:

1. **soporte** — cada packing por bolsa vive en las aristas de su bolsa.
   *Barato*: lo produce cualquier construcción; `AssignmentLemma.exists_packing_of_ownership`
   lo consume directamente.
2. **pérdida de asignación** `w - Σ bagVal_b ≤ (ζ/2)·n²`.
   **ABIERTO.** Es (A). Medido con `R5`: `0` exacto en la familia split y `≈ 0.84·n` en
   escalada adversarial hasta `n = 68`. Sin demostración.
3. **bolsas split exactas** `bagVal_b ≤ gain(P_b)` para `b ∈ Bs`.
   **DEMOSTRADO**: `SplitBagExact.split_bag_exact` con `bagVal_b = W*(H_b)`.
4. **bolsas densas** `Σ_{b ∈ Bd} (bagVal_b - gain(P_b)) ≤ (ζ/2)·n²`.
   **REDUCIDO**, no demostrado: es `DenseBagClosure.DenseBagNibbleAt`, la instancia `r = 6`
   del nibble ponderado que Paper III **ya demostró**
   (`Nibble.fracNibbleWeighted_nearPerfect`, `r`-genérico, sin `sorry`). Falta el porte, y
   falta verificar las hipótesis del nibble para `δ > 0` con el mismo rigor con que se
   verificaron para `δ = 0`.

## La respuesta a «¿esto resuelve E01?»

**No.** Quedan las cláusulas 2 y 4. La cláusula 4 está a un **porte** de distancia; la
cláusula 2 está a una **demostración** de distancia, y es la misma dificultad que el gap de
integralidad cordal por `AssignmentEquivalence.assignmentLossOwnAt_iff_gap`.

Lo que sí cambió con la contabilidad en dos regímenes (`TwoRegimeAccounting`) es que las
cláusulas 3 y 4 **no se estorban**: la `β` del nibble multiplica sólo a `Bd`, y las bolsas
split no la ven. Antes, con una `β` global, la peor bolsa forzaba `β → 1` y la cota se
vaciaba. En la familia split —la extremal de Erdős #81— la cota pasó de `0.22·n²` a cero.

## La obligación estructural que no es una desigualdad

Hay un quinto requisito que `TwoRegimeRouteAt` **esconde** y conviene decir en voz alta:
la partición `Bs ∪ Bd` tiene que ser *exhaustiva y honesta* — cada bolsa debe ser
realmente split (para que valga 3) o realmente densa (para que valga 4). Medido
(`E01_BRIDGE_STATUS.md` §11.3), la regla canónica produce **sólo** bolsas split pero
incumple 2, y `R5` cumple 2 pero produce bolsas que no son ni una cosa ni la otra
(densidad `0.60`–`0.80`). **Exhibir una regla que satisfaga 2 y produzca sólo bolsas de los
dos tipos es el trabajo pendiente**, y es una pregunta sobre árboles de cliques, no sobre
LPs.
-/

namespace PaperIV.E01Ledger

open Finset
open PaperIV.FarRounding
open PaperIV.AssignmentLemma
open PaperIV.TwoRegimeAccounting

/-- **El residuo de E01.**  Las cuatro cláusulas del docstring, en una sola `Prop`.
No se demuestra aquí: es lo que falta. -/
def TwoRegimeRouteAt (ζ : ℚ) : Prop :=
  ∃ T : ℕ, ∀ n : ℕ, T ≤ n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    IsChordal G → ∀ w : ℚ, CertifiedFractionalOptimum G w →
      ∃ (Bs Bd : Finset ℕ) (own : Sym2 (Fin n) → ℕ) (bagVal : ℕ → ℚ) (P : ℕ → Packing G),
        Disjoint Bs Bd ∧
        -- 1. soporte
        (∀ b ∈ Bs ∪ Bd, ∀ K ∈ (P b).pieces, ∀ e ∈ pairs K, own e = b) ∧
        -- 2. pérdida de asignación  (ABIERTO: es (A))
        w - ∑ b ∈ Bs ∪ Bd, bagVal b ≤ (ζ / 2) * (n : ℚ) ^ 2 ∧
        -- 3. bolsas split, exactas  (DEMOSTRADO: split_bag_exact)
        (∀ b ∈ Bs, bagVal b ≤ ((P b).gain : ℚ)) ∧
        -- 4. bolsas densas, nibble r = 6  (REDUCIDO a Paper III)
        ∑ b ∈ Bd, (bagVal b - ((P b).gain : ℚ)) ≤ (ζ / 2) * (n : ℚ) ^ 2

/-- La ruta en dos regímenes implica la hipótesis de asignación.  Es
`TwoRegimeAccounting.loss_le_two_regimes` instanciada y ensamblada. -/
theorem assignmentLossOwnAt_of_twoRegimeRoute {ζ : ℚ} (h : TwoRegimeRouteAt ζ) :
    AssignmentLossOwnAt ζ := by
  classical
  obtain ⟨T, hT⟩ := h
  refine ⟨T, ?_⟩
  intro n hn G _ hchord w hw
  obtain ⟨Bs, Bd, own, bagVal, P, hdisj, hsupp, hassign, hexact, hround⟩ :=
    hT n hn G hchord w hw
  refine ⟨Bs ∪ Bd, own, P, hsupp, ?_⟩
  have hsplitS : ∑ b ∈ Bs ∪ Bd, bagVal b = ∑ b ∈ Bs, bagVal b + ∑ b ∈ Bd, bagVal b :=
    Finset.sum_union hdisj
  have hsplitG : ∑ b ∈ Bs ∪ Bd, ((P b).gain : ℚ)
      = ∑ b ∈ Bs, ((P b).gain : ℚ) + ∑ b ∈ Bd, ((P b).gain : ℚ) :=
    Finset.sum_union hdisj
  have hS : ∑ b ∈ Bs, bagVal b ≤ ∑ b ∈ Bs, ((P b).gain : ℚ) := Finset.sum_le_sum hexact
  have hD : ∑ b ∈ Bd, bagVal b - ∑ b ∈ Bd, ((P b).gain : ℚ) ≤ (ζ / 2) * (n : ℚ) ^ 2 := by
    rw [← Finset.sum_sub_distrib]; exact hround
  rw [hsplitG]
  rw [hsplitS] at hassign
  linarith

/-- **La cadena completa de E01.**  La ruta en dos regímenes con presupuesto `η/2` da el
redondeo lejano `FarRoundingAt η`, y por `FarRounding.farRegime_cliquePartition` la
partición en `≤ n²/6 + O(n)` piezas.

Todas las implicaciones están demostradas.  La hipótesis `TwoRegimeRouteAt (η/2)` **no**:
sus cláusulas 2 y 4 son el residuo exacto de E01. -/
theorem farRoundingAt_of_twoRegimeRoute {η : ℚ} (h : TwoRegimeRouteAt (η / 2)) :
    FarRoundingAt η :=
  farRoundingAt_of_assignmentLossOwn (assignmentLossOwnAt_of_twoRegimeRoute h)

/-- La cláusula 3 no es una hipótesis: para las bolsas split se cumple con
`bagVal_b = W*(H_b)` por `SplitBagExact.split_bag_exact`.  Aquí queda registrado el patrón
de uso: si el packing de la bolsa alcanza su `bagVal`, la cláusula sale. -/
theorem clause3_of_exact_bags {ι : Type*} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (Bs : Finset ι) (bagVal : ι → ℚ) (P : ι → Packing G)
    (hb : ∀ b ∈ Bs, bagVal b = ((P b).gain : ℚ)) :
    ∀ b ∈ Bs, bagVal b ≤ ((P b).gain : ℚ) :=
  fun b hbmem => le_of_eq (hb b hbmem)

end PaperIV.E01Ledger
