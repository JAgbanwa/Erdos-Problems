import PaperIV.SplitMixedGap
import PaperIV.Erdos81Unconditional
import PaperIV.Erdos81AllOrders

/-!
# El presupuesto de pérdida, sin restricción de orden

La identidad (1.3) del manuscrito —«pérdida ≤ margen»— se presenta allí dentro del modelo mixto
de triángulos y `K₄`. Este módulo demuestra que **no depende del modelo**: vale para cualquier
partición en cliques, con piezas de cualquier orden, y por tanto es una interfaz común a
cualquier demostración del objetivo, use la familia de piezas que use.

## La identidad

Para **toda** partición en cliques `Q`, sin restricción de orden,

```text
∑ g(K) + |Q| = e(G),        g(K) = C(|K|,2) ∸ 1,
```

que es `SplitMixedGap.sum_gainOf_add_size`: cada pieza cubre `C(|K|,2)` aristas y cuesta una,
luego ahorra `C(|K|,2) − 1` frente a cubrirlas sueltas. De ahí,

```text
|Q| ≤ T   ↔   e(G) ≤ ∑ g(K) + T.
```

Eso es exactamente el presupuesto: **lo que hay que producir es ganancia suficiente**, y la
identidad traduce el objetivo de partición en un objetivo de ganancia sin perder nada. No se usa
en ningún punto que las piezas sean triángulos o `K₄`.

## Por qué importa para el encuadre

Tres demostraciones del mismo objetivo instancian esta interfaz con familias distintas:

* con `{K₃, K₄}` —ganancias `2` y `5`— se obtiene una cota para `c₄`;
* con `{K₃, …, K_L}` se obtiene una cota para el valor `L`-acotado;
* sin restricción, para `cp`.

Y las tres cotas **no** son equivalentes. Cuantas más órdenes se permiten, más ganancia hay
disponible, más margen deja el óptimo fraccional y **más fácil** es el objetivo. El caso
`{K₃, K₄}` es el que menos margen concede.

Por eso `erdos81_cp_form` de abajo es una consecuencia inmediata del teorema principal y no al
revés: acotar `c₄` es estrictamente más fuerte que acotar `cp`. Y el ejemplo que lo separa es el
más simple posible: `cp(K_n) = 1`, mientras que `c₄(K_n)` crece como `n²`.
-/

namespace PaperIV.LossBudget

open Finset PaperIV PaperIV.FarRounding

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## 1. El presupuesto, para cualquier familia de piezas -/

/-- **El presupuesto de pérdida.**  Para toda partición en cliques —de cualquier orden—, cumplir
el objetivo equivale a que la ganancia total cubra la diferencia.

La restricción de orden no interviene: es una identidad sobre la cobertura exacta de aristas. -/
theorem budget_iff {G : SimpleGraph V} [DecidableRel G.Adj] (Q : CliquePartition G) (T : ℕ) :
    Q.size ≤ T ↔ G.edgeFinset.card ≤ ∑ K ∈ Q.pieces, FarRounding.gainOf K + T := by
  have h := PaperIV.SplitMixedGap.sum_gainOf_add_size Q
  omega

/-- La misma identidad, en la forma en que la usa el manuscrito: el coste de completar con
aristas sueltas es exactamente `e(G)` menos la ganancia. -/
theorem size_add_gain_eq {G : SimpleGraph V} [DecidableRel G.Adj] (Q : CliquePartition G) :
    Q.size + ∑ K ∈ Q.pieces, FarRounding.gainOf K = G.edgeFinset.card := by
  have h := PaperIV.SplitMixedGap.sum_gainOf_add_size Q
  omega

/-- Permitir piezas más grandes sólo añade testigos: la restricción de orden es monótona. -/
theorem orderAtMost_mono {G : SimpleGraph V} [DecidableRel G.Adj] {Q : CliquePartition G}
    {r r' : ℕ} (h : r ≤ r') (hQ : Q.OrderAtMost r) : Q.OrderAtMost r' :=
  fun K hK => le_trans (hQ K hK) h

/-! ## 2. La forma `cp`, que es la que pide el problema original

Erdős, Ordman y Zalcstein preguntan por `cp`, sin restricción de orden de pieza.  Nuestros
teoremas dan la forma `c₄`, que es estrictamente más fuerte; las dos consecuencias siguientes
hacen explícito el paso, que es olvidar una conjunción. -/

/-- **Forma `cp` del teorema agudo.**  Consecuencia inmediata de `erdos81_cliquePartition`: basta
olvidar la restricción de orden.

El recíproco es falso: una cota para `cp` no produce una cota para `c₄`. -/
theorem erdos81_cp_form :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      PaperIV.FarRounding.IsChordal G →
        ∃ Q : CliquePartition G, Q.size ≤ PaperIV.targetSize n := by
  obtain ⟨N, hN⟩ := PaperIV.Erdos81Unconditional.erdos81_cliquePartition
  refine ⟨N, fun n hn G _ hG => ?_⟩
  obtain ⟨Q, -, hsize⟩ := hN n hn G hG
  exact ⟨Q, hsize⟩

/-- **Forma `cp` para todos los órdenes.**  Es la respuesta literal al enunciado de Erdős,
Ordman y Zalcstein; nuestro Teorema A la implica y dice además que las piezas pueden tomarse de
orden a lo sumo cuatro. -/
theorem erdos81_cp_form_all_orders :
    ∃ b : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      PaperIV.FarRounding.IsChordal G →
        ∃ Q : CliquePartition G, Q.size ≤ PaperIV.targetSize n + b := by
  obtain ⟨b, hb⟩ := PaperIV.Erdos81AllOrders.erdos81_all_orders_additive
  refine ⟨b, fun n G _ hG => ?_⟩
  obtain ⟨Q, -, hsize⟩ := hb n G hG
  exact ⟨Q, hsize⟩

end PaperIV.LossBudget
