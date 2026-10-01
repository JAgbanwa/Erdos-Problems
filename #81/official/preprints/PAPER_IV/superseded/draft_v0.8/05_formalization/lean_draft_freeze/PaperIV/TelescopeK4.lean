import PaperIV.TelescopeK3Full

/-!
# El telescopado para `K₄`: fibras sobre una arista, y el primer paso

Séptima pieza de **GAP-RP01**.  Sube la construcción de `K₃` un nivel.

## La idea

En `K₃` se fijaba **un** vértice `c` y los triángulos con ese `c` eran las aristas del
rectángulo `(N(c)∩A, N(c)∩B)`.  En `K₄` se fijan **dos** vértices `c, d` —que además deben
ser **adyacentes**, porque `cd` es una de las seis parejas— y los `K₄` con esos dos son las
aristas del rectángulo

```
( N(c) ∩ N(d) ∩ A ,  N(c) ∩ N(d) ∩ B ).
```

El índice de la suma deja de ser `C` y pasa a ser `E(C,D)`: **las fibras van sobre una arista,
no sobre un vértice**.  Ésa es toda la diferencia estructural, y es la razón de que el mismo
`OneStepEstimate.interedges_approx` siga sirviendo.

## Contenido

* `nbrs2` — la vecindad común de un par.
* `k4Count_eq_sum` — **la descomposición en fibras**:
  `#K₄ transversales = ∑_{q ∈ E(C,D)} #E(N²(q)∩A, N²(q)∩B)`.
* `step_one_K4` — **el primer paso**:
  ```
  | #K₄ − d_AB·∑_{q∈E(C,D)} |N²(q)∩A|·|N²(q)∩B| |  ≤  |C|·|D|·ε·|A|·|B|.
  ```

## Cuántos pasos cuesta `K₄`

Seis parejas, pero el último paso es **exacto** por la misma razón que en `K₃`
(`TelescopeK3.last_step_free`): al quedar un solo indicador, su suma **es** la densidad por
los tamaños.  Luego `K₄` cuesta **cinco** pasos y el error es `5ε|A||B||C||D|`, no
`6ε|A||B||C||D|` como presupone GAP-RP01.

## Lo que falta

Los pasos **2 a 5**.  Cada uno necesita, como en `K₃`, su propia identidad de fibras dobles
—el análogo del conteo de cerezas— que engrane la salida de un paso con la entrada del
siguiente.  El primero, que es donde entra la regularidad por primera vez y donde estaba la
novedad estructural (fibras sobre arista), queda demostrado aquí.
-/

namespace PaperIV.TelescopeK4

open Finset

variable {α : Type*} [DecidableEq α] {G : SimpleGraph α} [DecidableRel G.Adj]

/-- La **vecindad común** de un par `q = (c,d)` dentro de `A`. -/
def nbrs2 (G : SimpleGraph α) [DecidableRel G.Adj] (A : Finset α) (q : α × α) : Finset α :=
  A.filter fun a => G.Adj a q.1 ∧ G.Adj a q.2

theorem mem_nbrs2 {A : Finset α} {q : α × α} {a : α} :
    a ∈ nbrs2 G A q ↔ a ∈ A ∧ G.Adj a q.1 ∧ G.Adj a q.2 := by
  simp [nbrs2]

/-- El predicado de `K₄` transversal sobre una cuádrupla `(a,b,c,d)`. -/
def isK4 (G : SimpleGraph α) (p : α × α × α × α) : Prop :=
  G.Adj p.1 p.2.1 ∧ G.Adj p.1 p.2.2.1 ∧ G.Adj p.1 p.2.2.2 ∧
    G.Adj p.2.1 p.2.2.1 ∧ G.Adj p.2.1 p.2.2.2 ∧ G.Adj p.2.2.1 p.2.2.2

instance : DecidablePred (isK4 G) := by unfold isK4; infer_instance

/-- Las cuádruplas transversales que forman un `K₄`. -/
def k4s (G : SimpleGraph α) [DecidableRel G.Adj] (A B C D : Finset α) :
    Finset (α × α × α × α) :=
  (A ×ˢ B ×ˢ C ×ˢ D).filter (isK4 G)

/-- Pertenencia a `k4s`, desplegada. -/
theorem mem_k4s {A B C D : Finset α} (p : α × α × α × α) :
    p ∈ k4s G A B C D ↔
      (p.1 ∈ A ∧ p.2.1 ∈ B ∧ p.2.2.1 ∈ C ∧ p.2.2.2 ∈ D) ∧ isK4 G p := by
  simp only [k4s, Finset.mem_filter, Finset.mem_product]

/-- Los `K₄` con los dos últimos vértices fijos en `q = (c,d)` son las aristas del rectángulo
`(N²(q)∩A, N²(q)∩B)`. -/
theorem card_fiber_K4 (A B C D : Finset α) (q : α × α) (hq : q.1 ∈ C) (hq2 : q.2 ∈ D)
    (hcd : G.Adj q.1 q.2) :
    ((k4s G A B C D).filter fun p => (p.2.2.1, p.2.2.2) = q).card
      = (G.interedges (nbrs2 G A q) (nbrs2 G B q)).card := by
  classical
  apply Finset.card_bij (fun p _ => (p.1, p.2.1))
  · intro p hp
    rw [Finset.mem_filter, mem_k4s] at hp
    obtain ⟨⟨⟨ha, hb, -, -⟩, hab, hac, had, hbc, hbd, -⟩, hpq⟩ := hp
    have hc : p.2.2.1 = q.1 := congrArg Prod.fst hpq
    have hd : p.2.2.2 = q.2 := congrArg Prod.snd hpq
    rw [SimpleGraph.mk_mem_interedges_iff]
    exact ⟨mem_nbrs2.2 ⟨ha, hc ▸ hac, hd ▸ had⟩,
           mem_nbrs2.2 ⟨hb, hc ▸ hbc, hd ▸ hbd⟩, hab⟩
  · intro p hp p2 hp2 hpp
    rw [Finset.mem_filter] at hp hp2
    simp only [Prod.mk.injEq] at hpp
    have h1 : p.2.2.1 = p2.2.2.1 := by
      rw [congrArg Prod.fst hp.2, congrArg Prod.fst hp2.2]
    have h2 : p.2.2.2 = p2.2.2.2 := by
      rw [congrArg Prod.snd hp.2, congrArg Prod.snd hp2.2]
    exact Prod.ext hpp.1 (Prod.ext hpp.2 (Prod.ext h1 h2))
  · intro r hr
    rw [SimpleGraph.mk_mem_interedges_iff, mem_nbrs2, mem_nbrs2] at hr
    obtain ⟨⟨ha, hac, had⟩, ⟨hb, hbc, hbd⟩, hab⟩ := hr
    refine ⟨(r.1, r.2, q.1, q.2), ?_, rfl⟩
    rw [Finset.mem_filter, mem_k4s]
    exact ⟨⟨⟨ha, hb, hq, hq2⟩, hab, hac, had, hbc, hbd, hcd⟩, rfl⟩

/-- **La descomposición en fibras para `K₄`.**  El conteo de `K₄` transversales es la suma,
**sobre las aristas de `(C,D)`**, de los conteos de aristas en el rectángulo de sus vecindades
comunes.

Nótese el cambio respecto de `K₃`: el índice es `E(C,D)`, no `C`. -/
theorem k4Count_eq_sum (A B C D : Finset α) :
    (k4s G A B C D).card
      = ∑ q ∈ G.interedges C D, (G.interedges (nbrs2 G A q) (nbrs2 G B q)).card := by
  classical
  have hmem : ∀ p ∈ k4s G A B C D, (p.2.2.1, p.2.2.2) ∈ G.interedges C D := by
    intro p hp
    rw [mem_k4s] at hp
    rw [SimpleGraph.mk_mem_interedges_iff]
    exact ⟨hp.1.2.2.1, hp.1.2.2.2, hp.2.2.2.2.2.2⟩
  rw [Finset.card_eq_sum_card_fiberwise hmem]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [SimpleGraph.mem_interedges_iff] at hq
  exact card_fiber_K4 A B C D q hq.1 hq.2.1 hq.2.2

/-! ## El primer paso -/

/-- **Primer paso para `K₄`.**  Sustituir el indicador de la pareja `(A,B)` por su densidad
cuesta a lo sumo `|C|·|D|·ε·|A|·|B|`.

La demostración es `OneStepEstimate.interedges_approx` aplicada en cada fibra —donde el
objeto **es** un rectángulo por `k4Count_eq_sum`— sumada sobre `E(C,D)`, y acotando
`#E(C,D) ≤ |C|·|D|`. -/
theorem step_one_K4 {ε : ℚ} (hε : 0 ≤ ε) {A B C D : Finset α}
    (h : OneStepEstimate.DiscrepAt G ε (G.edgeDensity A B) A B) :
    |((k4s G A B C D).card : ℚ)
        - G.edgeDensity A B
            * ∑ q ∈ G.interedges C D, ((nbrs2 G A q).card : ℚ) * ((nbrs2 G B q).card : ℚ)|
      ≤ (C.card : ℚ) * (D.card : ℚ) * (ε * A.card * B.card) := by
  classical
  have hsum : ((k4s G A B C D).card : ℚ)
      = ∑ q ∈ G.interedges C D, ((G.interedges (nbrs2 G A q) (nbrs2 G B q)).card : ℚ) := by
    rw [← Nat.cast_sum, ← k4Count_eq_sum]
  rw [hsum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hstep : ∀ q ∈ G.interedges C D,
      |((G.interedges (nbrs2 G A q) (nbrs2 G B q)).card : ℚ)
        - G.edgeDensity A B * (((nbrs2 G A q).card : ℚ) * ((nbrs2 G B q).card : ℚ))|
      ≤ ε * A.card * B.card := by
    intro q _
    have hsub : nbrs2 G A q ⊆ A := Finset.filter_subset _ _
    have htub : nbrs2 G B q ⊆ B := Finset.filter_subset _ _
    have hkey := h _ hsub _ htub
    have hfac : G.edgeDensity A B * (((nbrs2 G A q).card : ℚ) * ((nbrs2 G B q).card : ℚ))
        = G.edgeDensity A B * ((nbrs2 G A q).card : ℚ) * ((nbrs2 G B q).card : ℚ) := by ring
    rw [hfac]
    exact hkey
  have hbound : ∑ q ∈ G.interedges C D,
      |((G.interedges (nbrs2 G A q) (nbrs2 G B q)).card : ℚ)
        - G.edgeDensity A B * (((nbrs2 G A q).card : ℚ) * ((nbrs2 G B q).card : ℚ))|
      ≤ ((G.interedges C D).card : ℚ) * (ε * A.card * B.card) := by
    calc _ ≤ ∑ _q ∈ G.interedges C D, ε * A.card * B.card := Finset.sum_le_sum hstep
      _ = ((G.interedges C D).card : ℚ) * (ε * A.card * B.card) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  refine le_trans hbound ?_
  have hcd : ((G.interedges C D).card : ℚ) ≤ (C.card : ℚ) * (D.card : ℚ) := by
    have hnat := G.card_interedges_le_mul C D
    exact_mod_cast hnat
  have hpos : (0 : ℚ) ≤ ε * A.card * B.card := by positivity
  calc ((G.interedges C D).card : ℚ) * (ε * A.card * B.card)
      ≤ ((C.card : ℚ) * (D.card : ℚ)) * (ε * A.card * B.card) :=
        mul_le_mul_of_nonneg_right hcd hpos
    _ = (C.card : ℚ) * (D.card : ℚ) * (ε * A.card * B.card) := by ring

end PaperIV.TelescopeK4
