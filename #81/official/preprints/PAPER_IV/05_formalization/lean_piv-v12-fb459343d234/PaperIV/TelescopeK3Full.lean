import PaperIV.TelescopeK3

/-!
# El telescopado para `K₃`, completo

Sexta pieza de **GAP-RP01**.  Cierra el lema de conteo para `K₃`:

```
| #triángulos transversales  −  d_AB · d_AC · d_BC · |A|·|B|·|C| |  ≤  2·ε·|A|·|B|·|C|.
```

**Dos pasos, no tres**, porque el último es exacto (`TelescopeK3.last_step_free`).

## La pieza central: el conteo de cerezas

El objeto que une los dos pasos es el **conteo de cerezas** — los caminos `a − c − b` con
`a ∈ A`, `b ∈ B`, `c ∈ C` — que admite **dos descomposiciones en fibras**:

```
cherryCount  =  ∑_{c ∈ C} |N(c)∩A| · |N(c)∩B|        (fibra sobre c)
             =  ∑_{b ∈ B} #E(A, N(b)∩C)              (fibra sobre b)
```

La primera es la salida de `TelescopeK3.step_one`; la segunda es la entrada de `step_two`,
donde el rectángulo es `(A, N(b)∩C)`.  **Que ambas cuenten lo mismo es lo que engrana los dos
pasos**, y es la única pieza que no aparece explícita en GAP-RP01.

## Contenido

* `cherryCount_eq_sum_c`, `cherryCount_eq_sum_b` — las dos descomposiciones.
* `sum_nbrs_card_eq` — `∑_{b∈B} |N(b)∩C| = #E(B,C)`.
* `step_two` — el segundo paso, con rectángulo `(A, N(b)∩C)`.
* `counting_lemma_K3` — **el lema de conteo para `K₃`**, con constante `2`.
-/

namespace PaperIV.TelescopeK3Full

open Finset
open PaperIV.TelescopeK3

variable {α : Type*} [DecidableEq α] {G : SimpleGraph α} [DecidableRel G.Adj]

/-- Las **cerezas**: caminos `a − c − b` con `a ∈ A`, `b ∈ B`, `c ∈ C`.  No se pide `a ~ b`. -/
def cherries (G : SimpleGraph α) [DecidableRel G.Adj] (A B C : Finset α) :
    Finset (α × α × α) :=
  (A ×ˢ B ×ˢ C).filter fun p => G.Adj p.1 p.2.2 ∧ G.Adj p.2.1 p.2.2

/-! ## Las dos descomposiciones en fibras -/

/-- Fibra sobre `c`: las cerezas con centro `c` son el producto `(N(c)∩A) × (N(c)∩B)`. -/
theorem cherryCount_eq_sum_c (A B C : Finset α) :
    (cherries G A B C).card = ∑ c ∈ C, (nbrs G A c).card * (nbrs G B c).card := by
  classical
  have hmem : ∀ p ∈ cherries G A B C, p.2.2 ∈ C := by
    intro p hp
    simp only [cherries, Finset.mem_filter, Finset.mem_product] at hp
    exact hp.1.2.2
  rw [Finset.card_eq_sum_card_fiberwise hmem]
  refine Finset.sum_congr rfl fun c hcC => ?_
  rw [← Finset.card_product]
  apply Finset.card_bij (fun p _ => (p.1, p.2.1))
  · intro p hp
    simp only [cherries, Finset.mem_filter, Finset.mem_product] at hp
    obtain ⟨⟨⟨ha, hb, -⟩, hac, hbc⟩, hc⟩ := hp
    exact Finset.mem_product.2 ⟨mem_nbrs.2 ⟨ha, hc ▸ hac⟩, mem_nbrs.2 ⟨hb, hc ▸ hbc⟩⟩
  · intro p hp q hq hpq
    simp only [cherries, Finset.mem_filter, Finset.mem_product] at hp hq
    simp only [Prod.mk.injEq] at hpq
    exact Prod.ext hpq.1 (Prod.ext hpq.2 (hp.2.trans hq.2.symm))
  · intro q hq
    rw [Finset.mem_product, mem_nbrs, mem_nbrs] at hq
    refine ⟨(q.1, q.2, c), ?_, rfl⟩
    simp only [cherries, Finset.mem_filter, Finset.mem_product]
    exact ⟨⟨⟨hq.1.1, hq.2.1, hcC⟩, hq.1.2, hq.2.2⟩, trivial⟩

/-- Fibra sobre `b`: las cerezas con extremo `b` son las aristas del rectángulo
`(A, N(b)∩C)`. -/
theorem cherryCount_eq_sum_b (A B C : Finset α) :
    (cherries G A B C).card = ∑ b ∈ B, (G.interedges A (nbrs G C b)).card := by
  classical
  have hmem : ∀ p ∈ cherries G A B C, p.2.1 ∈ B := by
    intro p hp
    simp only [cherries, Finset.mem_filter, Finset.mem_product] at hp
    exact hp.1.2.1
  rw [Finset.card_eq_sum_card_fiberwise hmem]
  refine Finset.sum_congr rfl fun b hbB => ?_
  apply Finset.card_bij (fun p _ => (p.1, p.2.2))
  · intro p hp
    simp only [cherries, Finset.mem_filter, Finset.mem_product] at hp
    obtain ⟨⟨⟨ha, -, hc⟩, hac, hbc⟩, hb⟩ := hp
    rw [SimpleGraph.mk_mem_interedges_iff]
    exact ⟨ha, mem_nbrs.2 ⟨hc, (hb ▸ hbc).symm⟩, hac⟩
  · intro p hp q hq hpq
    simp only [cherries, Finset.mem_filter, Finset.mem_product] at hp hq
    simp only [Prod.mk.injEq] at hpq
    exact Prod.ext hpq.1 (Prod.ext (hp.2.trans hq.2.symm) hpq.2)
  · intro q hq
    rw [SimpleGraph.mk_mem_interedges_iff, mem_nbrs] at hq
    obtain ⟨ha, ⟨hc, hcb⟩, hac⟩ := hq
    refine ⟨(q.1, b, q.2), ?_, rfl⟩
    simp only [cherries, Finset.mem_filter, Finset.mem_product]
    exact ⟨⟨⟨ha, hbB, hc⟩, hac, hcb.symm⟩, trivial⟩

/-- `∑_{b∈B} |N(b)∩C| = #E(B,C)`: sumar los grados hacia `C` cuenta las aristas. -/
theorem sum_nbrs_card_eq (B C : Finset α) :
    ∑ b ∈ B, (nbrs G C b).card = (G.interedges B C).card := by
  classical
  have hmem : ∀ p ∈ G.interedges B C, p.1 ∈ B := by
    intro p hp
    rw [SimpleGraph.mem_interedges_iff] at hp
    exact hp.1
  rw [Finset.card_eq_sum_card_fiberwise hmem]
  refine Finset.sum_congr rfl fun b hbB => ?_
  apply Finset.card_bij (fun c _ => (b, c))
  · intro c hc
    rw [mem_nbrs] at hc
    simp only [Finset.mem_filter, SimpleGraph.mem_interedges_iff]
    exact ⟨⟨hbB, hc.1, hc.2.symm⟩, trivial⟩
  · intro c _ c' _ h
    simpa using h
  · intro q hq
    simp only [Finset.mem_filter, SimpleGraph.mem_interedges_iff] at hq
    obtain ⟨⟨-, hc, hadj⟩, hb⟩ := hq
    refine ⟨q.2, mem_nbrs.2 ⟨hc, hb ▸ hadj.symm⟩, ?_⟩
    rw [← hb]

/-! ## El segundo paso -/

/-- **Segundo paso.**  Sustituir el indicador de la pareja `(A,C)` por su densidad cuesta a lo
sumo `|B|·ε·|A|·|C|`.  El rectángulo de cada fibra es `(A, N(b)∩C)`. -/
theorem step_two {ε : ℚ} (_hε : 0 ≤ ε) {A B C : Finset α}
    (h : OneStepEstimate.DiscrepAt G ε (G.edgeDensity A C) A C) :
    |((cherries G A B C).card : ℚ)
        - G.edgeDensity A C * (A.card : ℚ) * ((G.interedges B C).card : ℚ)|
      ≤ (B.card : ℚ) * (ε * A.card * C.card) := by
  classical
  have hsum : ((cherries G A B C).card : ℚ)
      = ∑ b ∈ B, ((G.interedges A (nbrs G C b)).card : ℚ) := by
    rw [← Nat.cast_sum, ← cherryCount_eq_sum_b]
  have hdeg : ((G.interedges B C).card : ℚ) = ∑ b ∈ B, ((nbrs G C b).card : ℚ) := by
    rw [← Nat.cast_sum, sum_nbrs_card_eq]
  rw [hsum, hdeg, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum (fun b _ => ?_))
    (le_of_eq (by rw [Finset.sum_const, nsmul_eq_mul]))
  have hsub : (A : Finset α) ⊆ A := Finset.Subset.refl A
  have htub : nbrs G C b ⊆ C := Finset.filter_subset _ _
  have hkey := h _ hsub _ htub
  exact hkey

/-! ## El lema de conteo para `K₃` -/

/-- **El lema de conteo para `K₃`.**  Con las tres parejas `ε`-uniformes,
```
| #triángulos transversales − d_AB·d_AC·d_BC·|A|·|B|·|C| |  ≤  2·ε·|A|·|B|·|C|.
```
Constante `2` y no `3`: el último paso es exacto (`TelescopeK3.last_step_free`). -/
theorem counting_lemma_K3 {ε : ℚ} (hε : 0 ≤ ε) {A B C : Finset α}
    (hAB : OneStepEstimate.DiscrepAt G ε (G.edgeDensity A B) A B)
    (hAC : OneStepEstimate.DiscrepAt G ε (G.edgeDensity A C) A C) :
    |((((A ×ˢ B ×ˢ C).filter
          fun p => G.Adj p.1 p.2.1 ∧ G.Adj p.1 p.2.2 ∧ G.Adj p.2.1 p.2.2).card : ℚ))
        - G.edgeDensity A B * G.edgeDensity A C * G.edgeDensity B C
            * A.card * B.card * C.card|
      ≤ 2 * (ε * A.card * B.card * C.card) := by
  classical
  -- paso 1: del conteo de triángulos al conteo de cerezas
  have h1 := TelescopeK3.step_one (G := G) hε hAB (A := A) (B := B) (C := C)
  have hch : ∑ c ∈ C, ((nbrs G A c).card : ℚ) * ((nbrs G B c).card : ℚ)
      = ((cherries G A B C).card : ℚ) := by
    rw [cherryCount_eq_sum_c]
    push_cast
    ring
  rw [hch] at h1
  -- paso 2: del conteo de cerezas a las densidades
  have h2 := step_two (G := G) hε hAC (A := A) (B := B) (C := C)
  -- el último paso es exacto
  have h3 : ((G.interedges B C).card : ℚ) = G.edgeDensity B C * B.card * C.card :=
    TelescopeK3.last_step_free B C
  -- cotas auxiliares
  have hd0 : (0 : ℚ) ≤ G.edgeDensity A B := G.edgeDensity_nonneg A B
  have hd1 : G.edgeDensity A B ≤ 1 := G.edgeDensity_le_one A B
  have hA0 : (0 : ℚ) ≤ A.card := by positivity
  have hB0 : (0 : ℚ) ≤ B.card := by positivity
  have hC0 : (0 : ℚ) ≤ C.card := by positivity
  -- combinación
  obtain ⟨hl1, hu1⟩ := abs_le.1 h1
  obtain ⟨hl2, hu2⟩ := abs_le.1 h2
  rw [h3] at hl2 hu2
  rw [abs_le]
  constructor <;> nlinarith [hl1, hu1, hl2, hu2, hε, hd0, hd1, hA0, hB0, hC0]

end PaperIV.TelescopeK3Full
