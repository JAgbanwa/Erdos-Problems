import PaperIV.FarRounding

/-!
# La cota superior universal del LP mixto: `W*(G) ≤ (5/6)·e(G)`

Pieza **incondicional** —sin hipótesis externas, sin `Prop` importado— para la ruta que
demuestra `UniformRoundingTarget` desde cero en vez de citarla.

## El certificado

El dual constante `price e = 5/6` es factible:

* `K₃` aporta `gainF = 2` y tiene `C(3,2) = 3` aristas: `3·(5/6) = 5/2 ≥ 2`;
* `K₄` aporta `gainF = 5` y tiene `C(4,2) = 6` aristas: `6·(5/6) = 5 ≥ 5`, **ajustado**.

El `K₄` es el caso de igualdad, que es exactamente por qué `5/6` es el precio correcto y no uno
menor: es el mejor precio uniforme posible para esta familia.

Por dualidad débil (`FarRounding.weak_duality`), **todo** empaquetamiento fraccional cumple
`x.value ≤ (5/6)·e(G)`.

## Para qué sirve

Es la mitad superior del sándwich que cierra el redondeo mixto sin citar nada:

```
x.value  ≤  (5/6)·e(G)                          ← aquí
gain(P)  ≥  (1−β)·(5/6)·|κ|·μ·e(G)              ← TrimPackingEdge.exists_packing_of_schedule_edge
⟹  x.value − gain(P)  ≤  (5/6)·e(G)·[1 − (1−β)(1−u)·|κ|/(|κ|+1)]
```

y el corchete tiende a `0` al crecer `|κ|`, con `e(G) ≤ n²/2`. Lo que falta para cerrar es
instanciar las hipótesis de conteo del calendario sobre el pool canónico.
-/

namespace PaperIV.UniformDual

open Finset
open PaperIV.FarRounding

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- **El dual uniforme**: precio `5/6` en toda arista.  Factible para la familia `{K₃, K₄}`,
con igualdad en `K₄`. -/
def uniformDual (G : SimpleGraph V) [DecidableRel G.Adj] : DualCover G ℚ where
  price := fun _ => 5 / 6
  price_nonneg := by intro _; norm_num
  covers := by
    intro K hK
    have hitem := mem_items.1 hK
    rw [Finset.sum_const, card_pairs, nsmul_eq_mul, gainF]
    rcases hitem.2 with h | h <;> rw [h] <;> norm_num [Nat.choose_two_right]

theorem uniformDual_value (G : SimpleGraph V) [DecidableRel G.Adj] :
    (uniformDual G).value = (5 / 6 : ℚ) * (G.edgeFinset.card : ℚ) := by
  show (∑ _e ∈ G.edgeFinset, (5 / 6 : ℚ)) = _
  rw [Finset.sum_const, nsmul_eq_mul]
  ring

/-- **La cota superior universal.**  Todo empaquetamiento fraccional mixto de `G` tiene valor a
lo sumo `(5/6)·e(G)`.

Incondicional: es dualidad débil contra un dual explícito. -/
theorem value_le_five_sixths (x : FracPacking G ℚ) :
    x.value ≤ (5 / 6 : ℚ) * (G.edgeFinset.card : ℚ) := by
  rw [← uniformDual_value G]
  exact weak_duality x (uniformDual G)

/-- La misma cota en términos de `n`, usando `e(G) ≤ C(n,2) ≤ n²/2`. -/
theorem value_le_of_card {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (x : FracPacking G ℚ) :
    x.value ≤ (5 / 12 : ℚ) * (n : ℚ) ^ 2 := by
  have hn0 : (0 : ℚ) ≤ (n : ℚ) := by positivity
  have hchoose : ((n.choose 2 : ℕ) : ℚ) ≤ (n : ℚ) ^ 2 / 2 := by
    rw [Nat.cast_choose_two]
    nlinarith [hn0]
  have hcard : (G.edgeFinset.card : ℚ) ≤ (n : ℚ) ^ 2 / 2 := by
    have h := G.card_edgeFinset_le_card_choose_two
    have hn : (G.edgeFinset.card : ℚ) ≤ (((Fintype.card (Fin n)).choose 2 : ℕ) : ℚ) := by
      exact_mod_cast h
    rw [Fintype.card_fin] at hn
    exact hn.trans hchoose
  calc x.value ≤ (5 / 6 : ℚ) * (G.edgeFinset.card : ℚ) := value_le_five_sixths x
    _ ≤ (5 / 6 : ℚ) * ((n : ℚ) ^ 2 / 2) :=
        mul_le_mul_of_nonneg_left hcard (by norm_num)
    _ = (5 / 12 : ℚ) * (n : ℚ) ^ 2 := by ring

end PaperIV.UniformDual
