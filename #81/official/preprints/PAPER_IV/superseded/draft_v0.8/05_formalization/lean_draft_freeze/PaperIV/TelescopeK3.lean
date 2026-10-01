import PaperIV.OneStepEstimate

/-!
# El telescopado para `K₃`: la construcción

Quinta pieza de **GAP-RP01**.  Construye la sucesión híbrida del telescopado para el patrón
`K₃` y demuestra el primer paso, que es donde entra la regularidad.

## La idea, en una línea

Fijado el tercer vértice `c`, los triángulos con ese `c` **son exactamente las aristas del
rectángulo `(N(c) ∩ A, N(c) ∩ B)`**.  Por eso el paso encaja en
`OneStepEstimate.interedges_approx`, que es una estimación sobre rectángulos.

## La sucesión híbrida

Con `A, B, C` las tres partes y densidades `d_AB, d_AC, d_BC`:

```
f₀ = ∑_{a,b,c} 1[ab]·1[ac]·1[bc]          (el conteo real)
f₁ = ∑_{a,b,c} d_AB ·1[ac]·1[bc]
f₂ = ∑_{a,b,c} d_AB · d_AC ·1[bc]
f₃ = d_AB · d_AC · d_BC · |A|·|B|·|C|      (el conteo ideal)
```

**El tercer paso es gratis:** `f₂ = f₃` *exactamente*, porque
`∑_{b,c} 1[bc] = #E(B,C) = d_BC·|B|·|C|` por definición de densidad
(`OneStepEstimate.card_interedges_eq`).  Así que el telescopado cuesta **dos** pasos, no
tres, y el error total es `2ε|A||B||C|` en lugar de `3ε|A||B||C|`.

## Lo que se demuestra aquí

* `triangleCount_eq_sum` — **la descomposición en fibras**: el conteo de triángulos
  transversales es `∑_{c ∈ C} #E(N(c)∩A, N(c)∩B)`.  Es la identidad que convierte el
  problema en rectángulos.
* `step_one` — **el primer paso del telescopado**:
  ```
  | f₀ − d_AB · ∑_{c∈C} |N(c)∩A|·|N(c)∩B| |  ≤  |C| · ε · |A| · |B|.
  ```
  Sale de `interedges_approx` sumado sobre `c`, sin condiciones de tamaño y sin casos.
* `last_step_free` — **`f₂ = f₃` exactamente**.

## Lo que falta

El **segundo** paso (`f₁ → f₂`, sustituir `1[ac]` por `d_AC`), cuya fibra es sobre `b` y
cuyo rectángulo es `(A, N(b)∩C)`.  Es estructuralmente idéntico al primero pero con las
partes permutadas, y requiere la identidad de fibras análoga.  Con él, el telescopado de
`K₃` queda completo con error `2ε|A||B||C|`.
-/

namespace PaperIV.TelescopeK3

open Finset

variable {α : Type*} [DecidableEq α] {G : SimpleGraph α} [DecidableRel G.Adj]

/-- Los vecinos de `c` dentro de `A`. -/
def nbrs (G : SimpleGraph α) [DecidableRel G.Adj] (A : Finset α) (c : α) : Finset α :=
  A.filter fun a => G.Adj a c

theorem mem_nbrs {A : Finset α} {c a : α} : a ∈ nbrs G A c ↔ a ∈ A ∧ G.Adj a c := by
  simp [nbrs]

/-- Los triángulos transversales con tercer vértice `c` son exactamente las aristas del
rectángulo `(N(c) ∩ A, N(c) ∩ B)`. -/
theorem card_fiber_eq (A B : Finset α) (c : α) :
    (((A ×ˢ B ×ˢ ({c} : Finset α)).filter
        fun p => G.Adj p.1 p.2.1 ∧ G.Adj p.1 p.2.2 ∧ G.Adj p.2.1 p.2.2).card)
      = (G.interedges (nbrs G A c) (nbrs G B c)).card := by
  classical
  apply Finset.card_bij (fun p _ => (p.1, p.2.1))
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_singleton] at hp
    obtain ⟨⟨ha, hb, hc⟩, hab, hac, hbc⟩ := hp
    rw [SimpleGraph.mk_mem_interedges_iff]
    exact ⟨mem_nbrs.2 ⟨ha, hc ▸ hac⟩, mem_nbrs.2 ⟨hb, hc ▸ hbc⟩, hab⟩
  · intro p hp q hq hpq
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_singleton] at hp hq
    obtain ⟨h1, h2⟩ := Prod.mk.injEq .. ▸ hpq
    exact Prod.ext h1 (Prod.ext h2 (hp.1.2.2.trans hq.1.2.2.symm))
  · intro q hq
    rw [SimpleGraph.mk_mem_interedges_iff] at hq
    obtain ⟨hqa, hqb, hab⟩ := hq
    rw [mem_nbrs] at hqa hqb
    refine ⟨(q.1, q.2, c), ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_singleton]
    exact ⟨⟨hqa.1, hqb.1, trivial⟩, hab, hqa.2, hqb.2⟩

/-- **La descomposición en fibras.**  El conteo de triángulos transversales es la suma, sobre
el tercer vértice, de los conteos de aristas en el rectángulo de sus vecinos. -/
theorem triangleCount_eq_sum (A B C : Finset α) :
    ((A ×ˢ B ×ˢ C).filter
        fun p => G.Adj p.1 p.2.1 ∧ G.Adj p.1 p.2.2 ∧ G.Adj p.2.1 p.2.2).card
      = ∑ c ∈ C, (G.interedges (nbrs G A c) (nbrs G B c)).card := by
  classical
  have hmem : ∀ p ∈ (A ×ˢ B ×ˢ C).filter
      (fun p => G.Adj p.1 p.2.1 ∧ G.Adj p.1 p.2.2 ∧ G.Adj p.2.1 p.2.2), p.2.2 ∈ C := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_product] at hp
    exact hp.1.2.2
  rw [Finset.card_eq_sum_card_fiberwise hmem]
  refine Finset.sum_congr rfl fun c hcC => ?_
  rw [← card_fiber_eq A B c]
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨⟨ha, hb, -⟩, hadj⟩, hc⟩
    exact ⟨⟨ha, hb, hc⟩, hadj⟩
  · rintro ⟨⟨ha, hb, hc⟩, hadj⟩
    exact ⟨⟨⟨ha, hb, hc ▸ hcC⟩, hadj⟩, hc⟩

/-! ## El primer paso del telescopado -/

/-- **Primer paso.**  Sustituir el indicador de la pareja `(A,B)` por su densidad cuesta a lo
sumo `|C|·ε·|A|·|B|`.

La demostración es `OneStepEstimate.interedges_approx` aplicada en cada fibra —donde el
objeto **es** un rectángulo por `triangleCount_eq_sum`— y sumada sobre `C`. -/
theorem step_one {ε : ℚ} (_hε : 0 ≤ ε) {A B C : Finset α}
    (h : OneStepEstimate.DiscrepAt G ε (G.edgeDensity A B) A B) :
    |((((A ×ˢ B ×ˢ C).filter
          fun p => G.Adj p.1 p.2.1 ∧ G.Adj p.1 p.2.2 ∧ G.Adj p.2.1 p.2.2).card : ℚ))
        - G.edgeDensity A B * ∑ c ∈ C, ((nbrs G A c).card : ℚ) * ((nbrs G B c).card : ℚ)|
      ≤ (C.card : ℚ) * (ε * A.card * B.card) := by
  classical
  have hsum : ((((A ×ˢ B ×ˢ C).filter
      fun p => G.Adj p.1 p.2.1 ∧ G.Adj p.1 p.2.2 ∧ G.Adj p.2.1 p.2.2).card : ℚ))
      = ∑ c ∈ C, ((G.interedges (nbrs G A c) (nbrs G B c)).card : ℚ) := by
    rw [← Nat.cast_sum, ← triangleCount_eq_sum]
  rw [hsum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum (fun c _ => ?_))
    (le_of_eq (by rw [Finset.sum_const, nsmul_eq_mul]))
  have hsub : nbrs G A c ⊆ A := Finset.filter_subset _ _
  have htub : nbrs G B c ⊆ B := Finset.filter_subset _ _
  have hkey := h _ hsub _ htub
  have hfac : G.edgeDensity A B * (((nbrs G A c).card : ℚ) * ((nbrs G B c).card : ℚ))
      = G.edgeDensity A B * ((nbrs G A c).card : ℚ) * ((nbrs G B c).card : ℚ) := by ring
  rw [hfac]
  exact hkey

/-! ## El último paso es gratis -/

/-- **`f₂ = f₃` exactamente.**  Sustituir el último indicador no cuesta nada, porque
`∑_{b,c} 1[bc]` **es** `d_BC·|B|·|C|` por definición de densidad.  Por eso el telescopado de
`K₃` cuesta dos pasos y no tres. -/
theorem last_step_free (B C : Finset α) :
    ((G.interedges B C).card : ℚ) = G.edgeDensity B C * B.card * C.card :=
  OneStepEstimate.card_interedges_eq B C

end PaperIV.TelescopeK3
