import PaperIV.ChordalBridge

/-!
# (2) Bolsas densas, y por qué la cota local NO cierra (A)

Dos piezas encadenadas.

**(2)** `CliqueBagNibble.CliqueBagNibbleAt` exigía que la bolsa fuera una clique
**completa**. Bajo cualquier regla de asignación que no sea la canónica, las bolsas son
subgrafos *propios* de su clique (medido en `E01_BRIDGE_STATUS.md` §11.3), así que esa
hipótesis no se aplica. `DenseBagNibbleAt` la reemplaza por una condición de **densidad**,
y la clique completa queda como el caso `δ = 0`.

**(A)** `loss_le_of_local_fraction` es un teorema **sin LP**: si cada bolsa extrae una
fracción `1-β` de la cota `(5/6)·|E(H_b)|`, la pérdida total es `≤ β·(5/6)·e(G)`, sin
comparación fraccional bolsa a bolsa. **Pero su hipótesis, medida, sólo se cumple cuando
el grafo es casi una única clique: NO cierra (A).** Ver el alcance más abajo.

## La observación que lo hace funcionar

`CliqueBagNibble.certified_le_five_sixths` da `w ≤ (5/6)·e(G)` para todo grafo. Si las
`H_b` **parten** las aristas de `G`, entonces `∑_b |E(H_b)| = e(G)`, y por tanto

```
w - ∑_b gain(P_b)  ≤  (5/6)·e  -  (1-β)·(5/6)·∑_b |E(H_b)|  =  β·(5/6)·e.
```

No interviene `W*(H_b)`. La condición es **local, combinatoria y verificable bolsa a
bolsa**, y esto es exactamente lo que le faltaba a (A): la regla `R5` requería resolver el
LP para guiarse, y su análisis exigía acotar `W*(G) - ∑_b W*(H_b)`, que nadie sabe hacer.

## Alcance de `loss_le_of_local_fraction`: MEDIDO, y es restrictivo

Escribí este teorema esperando que cerrara (A) en el «régimen de cliques». Medí su
hipótesis y **no lo hace**; lo dejo con el alcance real, que es mucho menor.

La condición local `gain(P_b) ≥ (1-β)(5/6)|E(H_b)|` sólo puede cumplirse si
`W*(H_b) ≥ (1-β)(5/6)|E(H_b)|` para **toda** bolsa. Midiendo
`r_b = W*(H_b) / ((5/6)|E(H_b)|)` y tomando el mínimo sobre bolsas
(`checks/a_local_cond.py`):

| familia | `r_min` con R1 | `r_min` con R5 | `β` mínima forzada |
|---|---|---|---|
| `K₉`, una sola bolsa | 1.000 | 1.000 | **0** |
| estrella de cliques | 0.600 | 0.831 | 0.17 |
| cadena, separador 4 | 0.267 | 0.600 | 0.40 |
| split `K₄ ∨ Ī₈` | 0.000 | 0.000 | 1 (vacía) |

`β` es un parámetro de la hipótesis, no del teorema: si `r_min` está acotado lejos de `1`,
**no se puede hacer `β → 0`**, y la conclusión `β·(5/6)·e` deja de ser `o(n²)`.

**El defecto es de la contabilidad, no de la ruta.**  Aquí **todas** las bolsas se miden
con la misma cota `(5/6)|E_b|` y con una **única** `β`, forzada por la peor bolsa; como las
split tienen `W*(H_b) = 2·C(p,2)` ≪ `(5/6)|E_b|`, esa `β` se va a `1` y la cota se vacía.

`TwoRegimeAccounting.loss_le_two_regimes` lo arregla: cada bolsa recibe **su** `bagVal`
—`W*(H_b)` en las split, donde `SplitBagExact.split_bag_exact` da redondeo **exacto**;
`(5/6)|E_b|` en las densas, donde aplica el nibble— y la `β` multiplica **sólo** a las
densas.  Medido (`checks/a_dos_casos.py`), en la familia split con `R5` la cota pasa de
`0.22·n²` a **exactamente cero**, y la `β` forzada de `1.000` a `0.000`.

Este teorema queda, pues, como el caso particular «todas las bolsas en el régimen denso».

## Rango de densidad medido (`checks/b2_dense.py`)

En `K_m` menos una fracción `δ` de aristas, con borrado **aleatorio** (peor que el
concentrado, que sólo vacía vértices y deja una clique menor):

| `δ` | `W*/((5/6)|E|)` | conjunto excepcional |
|---|---|---|
| 0.00 | 1.000 | 0 % |
| 0.05 | 1.000 | 0 % |
| 0.10 | 0.985–1.000 | 7–12 % |
| 0.20 | 0.878–0.989 | 47–70 % |

**Advertencia, y va en contra de lo que yo esperaba:** las bolsas que produjo `R5` en
§11.3 tenían densidad `0.60`–`0.80`, o sea `δ = 0.20`–`0.40`, **fuera** del rango donde
esta generalización se comporta bien. Que `DenseBagNibbleAt` exista no implica que cubra
las bolsas de `R5`; hace falta además una regla que mantenga `δ` pequeño.
-/

namespace PaperIV.DenseBagClosure

open Finset
open PaperIV.FarRounding
open PaperIV.CliqueBagNibble

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable {ι : Type*} [DecidableEq ι]

/-! ## 1. (A) en el régimen de cliques: la cota local, sin LP -/

/-- **El cierre local de (A).**  Si las bolsas **parten** las aristas de `G` y cada una
extrae al menos una fracción `1-β` de su propia cota `(5/6)·|E(H_b)|`, entonces la pérdida
total respecto del óptimo fraccional es a lo sumo `β·(5/6)·e(G)`.

Ninguna hipótesis sobre `W*(H_b)`: la comparación fraccional bolsa a bolsa —lo que hacía
falta para analizar `R5`— **no aparece**.  Sólo se usa `w ≤ (5/6)·e` y que las partes
suman `e`. -/
theorem loss_le_of_local_fraction {β : ℚ} (hβ : 0 ≤ β) {w : ℚ}
    (hw : CertifiedFractionalOptimum G w)
    (Bs : Finset ι) (part : ι → Finset (Sym2 V)) (P : ι → Packing G)
    (hcover : ∑ b ∈ Bs, ((part b).card : ℚ) = (G.edgeFinset.card : ℚ))
    (hlocal : ∀ b ∈ Bs, (1 - β) * ((5 / 6 : ℚ) * ((part b).card : ℚ)) ≤ ((P b).gain : ℚ)) :
    w - ∑ b ∈ Bs, ((P b).gain : ℚ) ≤ β * ((5 / 6 : ℚ) * (G.edgeFinset.card : ℚ)) := by
  have hub : w ≤ (5 / 6 : ℚ) * (G.edgeFinset.card : ℚ) := certified_le_five_sixths hw
  have hsum : (1 - β) * ((5 / 6 : ℚ) * (G.edgeFinset.card : ℚ))
      ≤ ∑ b ∈ Bs, ((P b).gain : ℚ) := by
    calc (1 - β) * ((5 / 6 : ℚ) * (G.edgeFinset.card : ℚ))
        = ∑ b ∈ Bs, (1 - β) * ((5 / 6 : ℚ) * ((part b).card : ℚ)) := by
          rw [← Finset.mul_sum, ← Finset.mul_sum, hcover]
      _ ≤ ∑ b ∈ Bs, ((P b).gain : ℚ) := Finset.sum_le_sum hlocal
  linarith

/-- La misma cota, expresada contra `n²`: con `e ≤ n²/2` la pérdida es `≤ (5β/12)·n²`,
que es la forma que pide `AssignmentLemma.AssignmentLossOwnAt`. -/
theorem loss_le_of_local_fraction_sq {β : ℚ} (hβ : 0 ≤ β) {w : ℚ}
    (hw : CertifiedFractionalOptimum G w)
    (Bs : Finset ι) (part : ι → Finset (Sym2 V)) (P : ι → Packing G)
    (hcover : ∑ b ∈ Bs, ((part b).card : ℚ) = (G.edgeFinset.card : ℚ))
    (hlocal : ∀ b ∈ Bs, (1 - β) * ((5 / 6 : ℚ) * ((part b).card : ℚ)) ≤ ((P b).gain : ℚ))
    (hedges : (G.edgeFinset.card : ℚ) ≤ (Fintype.card V : ℚ) ^ 2 / 2) :
    w - ∑ b ∈ Bs, ((P b).gain : ℚ) ≤ (5 * β / 12) * (Fintype.card V : ℚ) ^ 2 := by
  have h := loss_le_of_local_fraction hβ hw Bs part P hcover hlocal
  nlinarith [h, hedges, hβ]

/-! ## 2. (2) La hipótesis de bolsa densa -/

/-- **El nibble a `r = 6` para bolsas densas.**  Generaliza
`CliqueBagNibble.CliqueBagNibbleAt` sustituyendo «la bolsa es una clique completa» por
«la bolsa tiene al menos una fracción `1-δ` de las aristas de su clique».

La clique completa es el caso `δ = 0`: `cliqueBagNibbleAt_of_dense`. -/
def DenseBagNibbleAt (δ β : ℚ) : Prop :=
  ∃ m₀ : ℕ, ∀ (m : ℕ), m₀ ≤ m → ∀ (G : SimpleGraph (Fin m)) [DecidableRel G.Adj],
    (1 - δ) * ((m.choose 2 : ℕ) : ℚ) ≤ (G.edgeFinset.card : ℚ) →
      ∃ P : Packing G,
        (1 - β) * ((5 / 6 : ℚ) * (G.edgeFinset.card : ℚ)) ≤ (P.gain : ℚ)

/-- **La bolsa densa da la cota de pérdida**, exactamente como en el caso completo. -/
theorem dense_bag_loss_of_nibble {δ β : ℚ} (h : DenseBagNibbleAt δ β) :
    ∃ m₀ : ℕ, ∀ (m : ℕ), m₀ ≤ m → ∀ (G : SimpleGraph (Fin m)) [DecidableRel G.Adj],
      (1 - δ) * ((m.choose 2 : ℕ) : ℚ) ≤ (G.edgeFinset.card : ℚ) →
        ∀ w : ℚ, CertifiedFractionalOptimum G w →
          ∃ P : Packing G,
            w - (P.gain : ℚ) ≤ β * ((5 / 6 : ℚ) * (G.edgeFinset.card : ℚ)) := by
  obtain ⟨m₀, hm₀⟩ := h
  refine ⟨m₀, ?_⟩
  intro m hm G _ hdense w hw
  obtain ⟨P, hP⟩ := hm₀ m hm G hdense
  refine ⟨P, ?_⟩
  have hub := certified_le_five_sixths hw
  nlinarith [hub, hP]

/-- Una clique sobre `Fin m` tiene exactamente `C(m,2)` aristas. -/
theorem complete_card_edgeFinset {m : ℕ} (G : SimpleGraph (Fin m)) [DecidableRel G.Adj]
    (hG : ∀ a b : Fin m, a ≠ b → G.Adj a b) :
    G.edgeFinset.card = m.choose 2 := by
  classical
  have htop : G = ⊤ := by
    ext a b
    exact ⟨fun h => G.ne_of_adj h, fun h => hG a b h⟩
  have hset : G.edgeFinset = (⊤ : SimpleGraph (Fin m)).edgeFinset := by
    ext e; simp only [SimpleGraph.mem_edgeFinset, htop]
  rw [hset, SimpleGraph.card_edgeFinset_top_eq_card_choose_two, Fintype.card_fin]

/-- **La clique completa es el caso `δ = 0`.**  Recupera `CliqueBagNibbleAt` a partir de
`DenseBagNibbleAt` para todo `δ ≥ 0`, sin hipótesis adicionales. -/
theorem cliqueBagNibbleAt_of_dense {δ β : ℚ} (hδ : 0 ≤ δ) (h : DenseBagNibbleAt δ β) :
    CliqueBagNibbleAt β := by
  obtain ⟨m₀, hm₀⟩ := h
  refine ⟨m₀, ?_⟩
  intro m hm G _ hG
  refine hm₀ m hm G ?_
  have hcard : ((m.choose 2 : ℕ) : ℚ) = (G.edgeFinset.card : ℚ) := by
    rw [complete_card_edgeFinset G hG]
  have hnn : (0 : ℚ) ≤ ((m.choose 2 : ℕ) : ℚ) := by positivity
  nlinarith [hcard, hnn, hδ]

end PaperIV.DenseBagClosure
