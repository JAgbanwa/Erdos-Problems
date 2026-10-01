import PaperIV.CliqueBagNibble

/-!
# (A) El presupuesto de aristas: por qué los triángulos no bastan, como teorema

`CliqueBagNibble.certified_le_five_sixths` acota el óptimo **fraccional** por `(5/6)·e`
usando dualidad. Este módulo demuestra la cota **integral** correspondiente, y su
refinamiento para packings de un solo tipo, directamente por conteo de aristas —sin
dualidad y sin hipótesis externa alguna.

La consecuencia es el enunciado que hasta ahora en esta ruta sólo estaba **medido**:
*los triángulos solos no alcanzan*. Ahora es un teorema.

## Contenido

* `six_mul_gain_le_five_mul_edges` — para **todo** packing, `6·gain(P) ≤ 5·e(G)`.
  Ajustado: un `K₄` da `6·5 = 30 = 5·6`.
* `three_mul_gain_le_two_mul_edges` — si el packing usa **sólo triángulos**,
  `3·gain(P) ≤ 2·e(G)`, es decir `gain ≤ (2/3)·e`.
* `triangles_lose_sixth_of_edges` — en un grafo cuyo óptimo fraccional alcanza la cota
  `(5/6)·e` (las cliques lo hacen), todo packing de triángulos pierde al menos `e/6`.

## Por qué importa para (A)

La regla de asignación natural sobre un orden de eliminación perfecto (PEO) es: al
eliminar el vértice simplicial `v`, su vecindad `N(v)` es una **clique**; la bolsa de `v`
se queda con la estrella `{vx : x ∈ N(v)}` y recibe *donadas* aristas internas de `N(v)`.

* Si lo donado es un **emparejamiento**, cada triángulo `{v,x,y}` consume `2` aristas de
  estrella y `1` donada: `3` aristas por ganancia `2`. Sumando sobre todas las bolsas,
  `gain ≤ (2/3)·e`. Es `three_mul_gain_le_two_mul_edges`.
* Si lo donado es un **triángulo**, cada `K₄ = {v} ∪ T` consume `3` de estrella y `3`
  donadas: `6` aristas por ganancia `5`. Sumando, `gain ≤ (5/6)·e`.

Y en una clique `W* = (5/6)·e` exactamente (verificado por LP exacto, `m = 4..11`,
`checks/a_peo_budget.py`). Luego:

* el esquema con donación de **triángulos** es **exactamente ajustado** — puede en
  principio alcanzar el óptimo, pero sin ninguna holgura: desperdiciar una fracción
  constante de aristas cuesta `Θ(n²)`;
* el esquema con donación de **emparejamientos** pierde `≥ e/6 = Θ(n²)` en cliques,
  **cualquiera que sea la regla**. Queda descartado de raíz.

Esto cierra por tercera vía independiente —tras la medición con el arnés y la cuenta
`W* - 2ν₃* = e/6` de `docs/B2_NIBBLE_PAPER_III.md` §2— que `K₄` es obligatorio.
`DonatedMatchings.exists_packing_of_donatedMatchings`, que dona emparejamientos, **no
puede** ser la regla de (A): sirve para bolsas concretas, no como regla global.
-/

namespace PaperIV.DonationBudget

open Finset
open PaperIV.FarRounding

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Las aristas realmente ocupadas por un packing no superan a las de `G`. -/
theorem sum_card_pairs_le_edges (P : Packing G) :
    ∑ K ∈ P.pieces, (pairs K).card ≤ G.edgeFinset.card := by
  classical
  have hbu : (P.pieces.biUnion pairs).card = ∑ K ∈ P.pieces, (pairs K).card :=
    Finset.card_biUnion (fun K hK L hL hKL => P.edgeDisjoint K hK L hL hKL)
  rw [← hbu]
  exact Finset.card_le_card P.biUnion_subset_edgeFinset

/-- **El presupuesto mixto.**  Para todo packing, `6·gain(P) ≤ 5·e(G)`.  Es ajustado:
un `K₄` gasta `6` aristas por ganancia `5`.  No usa dualidad. -/
theorem six_mul_gain_le_five_mul_edges (P : Packing G) :
    6 * P.gain ≤ 5 * G.edgeFinset.card := by
  classical
  have e32 : Nat.choose 3 2 = 3 := by decide
  have e42 : Nat.choose 4 2 = 6 := by decide
  have hstep : ∀ K ∈ P.pieces, 6 * gainOf K ≤ 5 * (pairs K).card := by
    intro K hK
    rcases (P.isItem K hK).2 with h3 | h4
    · rw [gainOf_of_card_eq_three h3, card_pairs, h3, e32]; norm_num
    · rw [gainOf_of_card_eq_four h4, card_pairs, h4, e42]
  calc 6 * P.gain = ∑ K ∈ P.pieces, 6 * gainOf K := by
        rw [Packing.gain, Finset.mul_sum]
    _ ≤ ∑ K ∈ P.pieces, 5 * (pairs K).card := Finset.sum_le_sum hstep
    _ = 5 * ∑ K ∈ P.pieces, (pairs K).card := by rw [Finset.mul_sum]
    _ ≤ 5 * G.edgeFinset.card := Nat.mul_le_mul_left 5 (sum_card_pairs_le_edges P)

/-- **El presupuesto de sólo triángulos.**  Un packing cuyas piezas son todas `K₃`
cumple `3·gain(P) ≤ 2·e(G)`, es decir `gain ≤ (2/3)·e`.  Estrictamente peor que `5/6`. -/
theorem three_mul_gain_le_two_mul_edges (P : Packing G)
    (htri : ∀ K ∈ P.pieces, K.card = 3) :
    3 * P.gain ≤ 2 * G.edgeFinset.card := by
  classical
  have e32 : Nat.choose 3 2 = 3 := by decide
  have hstep : ∀ K ∈ P.pieces, 3 * gainOf K ≤ 2 * (pairs K).card := by
    intro K hK
    rw [gainOf_of_card_eq_three (htri K hK), card_pairs, htri K hK, e32]
  calc 3 * P.gain = ∑ K ∈ P.pieces, 3 * gainOf K := by
        rw [Packing.gain, Finset.mul_sum]
    _ ≤ ∑ K ∈ P.pieces, 2 * (pairs K).card := Finset.sum_le_sum hstep
    _ = 2 * ∑ K ∈ P.pieces, (pairs K).card := by rw [Finset.mul_sum]
    _ ≤ 2 * G.edgeFinset.card := Nat.mul_le_mul_left 2 (sum_card_pairs_le_edges P)

/-- **Los triángulos solos pierden `e/6`.**  Si el óptimo fraccional alcanza la cota
`(5/6)·e` —lo que ocurre en toda clique— entonces **todo** packing de triángulos, sea
cual sea la regla que lo construya, deja una pérdida de al menos `e/6`.

En una clique de tamaño `m` eso es `Θ(m²)`: el esquema de donación por emparejamientos
queda descartado como regla global para (A). -/
theorem triangles_lose_sixth_of_edges {w : ℚ} (hw : w = (5 / 6 : ℚ) * (G.edgeFinset.card : ℚ))
    (P : Packing G) (htri : ∀ K ∈ P.pieces, K.card = 3) :
    (1 / 6 : ℚ) * (G.edgeFinset.card : ℚ) ≤ w - (P.gain : ℚ) := by
  have hb := three_mul_gain_le_two_mul_edges P htri
  have hb' : (3 : ℚ) * (P.gain : ℚ) ≤ 2 * (G.edgeFinset.card : ℚ) := by exact_mod_cast hb
  rw [hw]; linarith

end PaperIV.DonationBudget
