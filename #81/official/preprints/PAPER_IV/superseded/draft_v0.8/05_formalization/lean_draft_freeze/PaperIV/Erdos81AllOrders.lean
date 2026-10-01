import PaperIV.Erdos81Unconditional

/-!
# La respuesta al problema, para **todos** los órdenes

`Erdos81Unconditional.erdos81_cliquePartition` da la cota **aguda** `M(n) = ⌊n(n+1)/6⌋`, pero
sólo para `n ≥ N`. La pregunta de Erdős, Ordman y Zalcstein es otra, y más débil:

```text
cp(G) ≤ n²/6 + O(n)   para todo grafo cordal
```

Este módulo demuestra esa forma **sin excepciones de orden**. La reducción es la evidente y por
eso conviene tenerla escrita: por debajo del umbral se cubre cada arista con su propia pieza
`K₂`, lo que cuesta `e(G) ≤ C(n,2) ≤ n²/2` piezas, y como el umbral es **fijo** ese exceso se
absorbe en la constante lineal.

## Los dos enunciados, y qué dice cada uno

* `erdos81_all_orders` — **la respuesta al problema**: vale para todo `n`, con una constante
  lineal explícita a partir del umbral.
* `Erdos81Unconditional.erdos81_cliquePartition` — la forma **aguda**, sólo para `n ≥ N`, junto
  con `PaperTheorems.erdos81_max_eq`, que además la alcanza.

No son el mismo resultado y conviene no confundirlos: para `n` pequeño **no** afirmamos la cota
aguda. Probablemente sea cierta; aquí no está demostrada.

## Sobre la constante

`C` sale del umbral `N`, que es astronómico. **No se afirma óptima**, ni de lejos. El problema
pide `O(n)`, no una constante buena, y la distinción entre «existe una constante» y «esta es la
mejor constante» es justo la que separa este enunciado del coeficiente asintótico `1/6` de
`LinearCoefficient.linear_coefficient_optimal`, que sí es óptimo.
-/

namespace PaperIV.Erdos81AllOrders

open PaperIV.FarRounding

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## 1. La partición trivial -/

/-- Cubrir cada arista con su propia pieza `K₂` es una partición en cliques de orden a lo sumo
cuatro, de tamaño exactamente `e(G)`.  Es el packing vacío, completado. -/
theorem exists_trivial_cliquePartition (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size = G.edgeFinset.card := by
  classical
  obtain ⟨Q, hQ4, hQsize⟩ :=
    exists_cliquePartition_of_packing (G := G) ⟨∅, by simp, by simp⟩
  refine ⟨Q, hQ4, ?_⟩
  simpa [Packing.gain] using hQsize

/-- Y su tamaño no llega a `n²/2`. -/
private theorem card_edgeFinset_le (G : SimpleGraph V) [DecidableRel G.Adj] :
    2 * G.edgeFinset.card ≤ Fintype.card V * Fintype.card V := by
  classical
  have h1 : G.edgeFinset.card ≤ (Fintype.card V).choose 2 :=
    SimpleGraph.card_edgeFinset_le_card_choose_two
  have h2 : (Fintype.card V) * (Fintype.card V - 1) = 2 * (Fintype.card V).choose 2 :=
    PaperIV.SplitUniformIncidence.mul_pred_eq_two_mul_choose_two _
  have h3 : (Fintype.card V) * (Fintype.card V - 1) ≤ Fintype.card V * Fintype.card V :=
    Nat.mul_le_mul_left _ (by omega)
  omega

/-! ## 2. La respuesta al problema -/

/-- **La cota `n²/6 + O(n)` para todo grafo cordal y todo orden.**

Esta es la forma en que Erdős, Ordman y Zalcstein plantean la pregunta, y aquí queda demostrada
sin excepciones de orden.  Por encima del umbral se usa la cota aguda; por debajo, la partición
trivial, cuyo exceso cabe en la constante porque el umbral es fijo. -/
theorem erdos81_all_orders :
    ∃ C : ℚ, 0 ≤ C ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        PaperIV.FarRounding.IsChordal G →
          ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧
            (Q.size : ℚ) ≤ (n : ℚ) ^ 2 / 6 + C * (n : ℚ) := by
  classical
  obtain ⟨N, hN⟩ := PaperIV.Erdos81Unconditional.erdos81_cliquePartition
  refine ⟨(N : ℚ) + 1, by positivity, ?_⟩
  intro n G _ hG
  rcases Nat.lt_or_ge n N with hsmall | hbig
  · -- por debajo del umbral: una pieza por arista
    obtain ⟨Q, hQ4, hQsize⟩ := exists_trivial_cliquePartition G
    refine ⟨Q, hQ4, ?_⟩
    have hcard : 2 * G.edgeFinset.card ≤ n * n := by
      have := card_edgeFinset_le G
      simpa using this
    have hQ : 2 * Q.size ≤ n * n := by rw [hQsize]; exact hcard
    have hQZ : 2 * (Q.size : ℚ) ≤ (n : ℚ) * (n : ℚ) := by exact_mod_cast hQ
    have hnN : (n : ℚ) ≤ (N : ℚ) := by exact_mod_cast le_of_lt hsmall
    have hn0 : (0 : ℚ) ≤ (n : ℚ) := by positivity
    nlinarith [hQZ, hnN, hn0]
  · -- por encima: la cota aguda, y `targetSize n ≤ n²/6 + n/6`
    obtain ⟨Q, hQ4, hQsize⟩ := hN n hbig G hG
    refine ⟨Q, hQ4, ?_⟩
    have h1 : (Q.size : ℚ) ≤ ((PaperIV.targetSize n : ℕ) : ℚ) := by exact_mod_cast hQsize
    have h2 : ((PaperIV.targetSize n : ℕ) : ℚ) ≤ (n : ℚ) * ((n : ℚ) + 1) / 6 :=
      PaperIV.targetSize_cast_le_continuous n
    have hn0 : (0 : ℚ) ≤ (n : ℚ) := by positivity
    have hN0 : (0 : ℚ) ≤ (N : ℚ) := by positivity
    nlinarith [h1, h2, hn0, hN0]

/-! ## 3. La forma aditiva: `M(n) + b` para todo orden

La forma `n²/6 + C·n` del teorema anterior tiene un término lineal con constante mala.  Hay un
enunciado **más limpio y más fuerte**: la cota aguda más una constante **aditiva**, válida sin
excepciones de orden.

```text
cp₄(G) ≤ M(n) + b        para todo n, todo cordal G
```

Es más fuerte porque `M(n) + b = n²/6 + n/6 + b`: el coeficiente lineal es el óptimo `1/6`
—`LinearCoefficient.linear_coefficient_optimal` dice que no se puede bajar— y todo el exceso
queda en una constante.

La demostración es la misma partición en dos rangos, pero como el rango pequeño es **finito**,
su exceso es una constante y no hace falta gastarlo en el término lineal. -/

/-- **`cp₄(G) ≤ M(n) + b` para todo orden.**

Más limpio que `erdos81_all_orders`: el coeficiente lineal queda en su valor óptimo `1/6` y el
exceso del rango pequeño se concentra en una constante aditiva.

## Sobre `b`, con precisión

`b = N²`, donde `N` es el umbral de `erdos81_cliquePartition`.  **Ese `N` no es `10¹⁴`.**  El
ensamblaje `RC01FarAssembly.chordalTargetAt_of_nearRegimeAt` toma `max Nfar Nnear`: `10¹⁴` es sólo
`Nnear`, el de la construcción cercana, y `Nfar` —el de la transferencia uniforme de RC01, que
descansa en regularidad— lo domina por completo y no admite valor numérico.  Bajar `Nnear` mejora
el enunciado de la rama cercana, pero **no mueve `N` ni `b`**.

Así que no se escribe ningún número para `b`, igual que la solución publicada no escribe ninguno
para su `T(η/2)`.

La verificación exhaustiva sugiere que la verdad es `b = 0`: para `n ≤ 9` la cota aguda se cumple
sin excepción y además se alcanza en cada orden.  Demostrar `b = 0` en el rango intermedio queda
abierto. -/
theorem erdos81_all_orders_additive :
    ∃ b : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      PaperIV.FarRounding.IsChordal G →
        ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size ≤ PaperIV.targetSize n + b := by
  classical
  obtain ⟨N, hN⟩ := PaperIV.Erdos81Unconditional.erdos81_cliquePartition
  refine ⟨N * N, ?_⟩
  intro n G _ hG
  rcases Nat.lt_or_ge n N with hsmall | hbig
  · -- rango pequeño: una pieza por arista, y `e(G) ≤ n²/2 ≤ N²`
    obtain ⟨Q, hQ4, hQsize⟩ := exists_trivial_cliquePartition G
    refine ⟨Q, hQ4, ?_⟩
    have hcard : 2 * G.edgeFinset.card ≤ n * n := by simpa using card_edgeFinset_le G
    have hnn : n * n ≤ N * N := Nat.mul_le_mul (le_of_lt hsmall) (le_of_lt hsmall)
    omega
  · -- rango grande: la cota aguda, que ya es mejor
    obtain ⟨Q, hQ4, hQsize⟩ := hN n hbig G hG
    exact ⟨Q, hQ4, by omega⟩

end PaperIV.Erdos81AllOrders
