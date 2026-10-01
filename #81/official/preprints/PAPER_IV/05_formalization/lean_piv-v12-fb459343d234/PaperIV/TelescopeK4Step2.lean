import PaperIV.TelescopeK4

/-!
# `K₄`, paso 2: y la estructura recursiva que ahorra dos pasos

Octava pieza de **GAP-RP01**.

## El hallazgo estructural

`K₄` tiene seis parejas.  Pero **quitando las tres incidentes a `A`** (`AB`, `AC`, `AD`) lo
que queda es

```
∑_{a,b,c,d} 1[bc]·1[bd]·1[cd]  =  |A| · #K₃(B,C,D),
```

es decir **el conteo de `K₃` sobre las otras tres partes**, que ya está demostrado
(`TelescopeK3Full.counting_lemma_K3`).  Luego

```
K₄  =  3 pasos de rectángulo  +  el lema K₃,
```

y no cinco pasos independientes.  La contabilidad del error:

```
3 pasos × ε|A||B||C||D|                    = 3ε|A||B||C||D|
|A| × (error de K₃ sobre B,C,D) = |A|·2ε|B||C||D| = 2ε|A||B||C||D|
──────────────────────────────────────────────────────────────
TOTAL                                        = 5ε|A||B||C||D|
```

Coincide con la predicción de `E01_BRIDGE_STATUS.md` §26.3 —cinco pasos, no seis— y además
**reutiliza** `counting_lemma_K3` en vez de rehacer dos pasos.

## Los tres rectángulos

| paso | quita | fibra sobre | rectángulo |
|---|---|---|---|
| 1 | `AB` | `(c,d) ∈ E(C,D)` | `(N(c)∩N(d)∩A , N(c)∩N(d)∩B)` |
| **2** | `AC` | `(b,d) ∈ E(B,D)` | `(N(d)∩A , N(b)∩N(d)∩C)` |
| 3 | `AD` | `(b,c) ∈ E(B,C)` | `(A , N(b)∩N(c)∩D)` |

Obsérvese que el rectángulo **se va simplificando**: en el paso 3 el lado izquierdo es ya
`A` entero.

## Contenido

* `books` — los `K₄` **menos la arista `AB`**: el objeto que sale del paso 1.
* `books_eq_sum_cd` — su fibra sobre `E(C,D)`: es la salida del paso 1.
* `books_eq_sum_bd` — su fibra sobre `E(B,D)`: es la entrada del paso 2.
* `step_two_K4` — **el segundo paso**, con rectángulo `(N(d)∩A , N(b)∩N(d)∩C)`.

Que `books` admita **las dos** descomposiciones es lo que engrana el paso 1 con el 2, igual
que el conteo de cerezas engranaba los dos pasos de `K₃`.
-/

namespace PaperIV.TelescopeK4Step2

open Finset
open PaperIV.TelescopeK3 (nbrs mem_nbrs)
open PaperIV.TelescopeK4 (nbrs2 mem_nbrs2)

variable {α : Type*} [DecidableEq α] {G : SimpleGraph α} [DecidableRel G.Adj]

/-- El predicado de «libro»: un `K₄` **menos** la arista `AB`. -/
def isBook (G : SimpleGraph α) (p : α × α × α × α) : Prop :=
  G.Adj p.1 p.2.2.1 ∧ G.Adj p.1 p.2.2.2 ∧
    G.Adj p.2.1 p.2.2.1 ∧ G.Adj p.2.1 p.2.2.2 ∧ G.Adj p.2.2.1 p.2.2.2

instance : DecidablePred (isBook G) := by unfold isBook; infer_instance

/-- Las cuádruplas transversales que forman un libro. -/
def books (G : SimpleGraph α) [DecidableRel G.Adj] (A B C D : Finset α) :
    Finset (α × α × α × α) :=
  (A ×ˢ B ×ˢ C ×ˢ D).filter (isBook G)

theorem mem_books {A B C D : Finset α} (p : α × α × α × α) :
    p ∈ books G A B C D ↔
      (p.1 ∈ A ∧ p.2.1 ∈ B ∧ p.2.2.1 ∈ C ∧ p.2.2.2 ∈ D) ∧ isBook G p := by
  simp only [books, Finset.mem_filter, Finset.mem_product]

/-! ## Fibra sobre `E(C,D)`: la salida del paso 1 -/

/-- Los libros con `(c,d)` fijo son el **producto** `(N²(q)∩A) × (N²(q)∩B)`: sin condición
entre `a` y `b`, que es justo la arista que se ha quitado. -/
theorem books_eq_sum_cd (A B C D : Finset α) :
    (books G A B C D).card
      = ∑ q ∈ G.interedges C D, (nbrs2 G A q).card * (nbrs2 G B q).card := by
  classical
  have hmem : ∀ p ∈ books G A B C D, (p.2.2.1, p.2.2.2) ∈ G.interedges C D := by
    intro p hp
    rw [mem_books] at hp
    rw [SimpleGraph.mk_mem_interedges_iff]
    exact ⟨hp.1.2.2.1, hp.1.2.2.2, hp.2.2.2.2.2⟩
  rw [Finset.card_eq_sum_card_fiberwise hmem]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [SimpleGraph.mem_interedges_iff] at hq
  obtain ⟨hqC, hqD, hqcd⟩ := hq
  rw [← Finset.card_product]
  apply Finset.card_bij (fun p _ => (p.1, p.2.1))
  · intro p hp
    rw [Finset.mem_filter, mem_books] at hp
    obtain ⟨⟨⟨ha, hb, -, -⟩, hac, had, hbc, hbd, -⟩, hpq⟩ := hp
    have hc : p.2.2.1 = q.1 := by rw [← hpq]
    have hd : p.2.2.2 = q.2 := by rw [← hpq]
    exact Finset.mem_product.2
      ⟨mem_nbrs2.2 ⟨ha, hc ▸ hac, hd ▸ had⟩, mem_nbrs2.2 ⟨hb, hc ▸ hbc, hd ▸ hbd⟩⟩
  · intro p hp p2 hp2 hpp
    rw [Finset.mem_filter] at hp hp2
    simp only [Prod.mk.injEq] at hpp
    have e1 : p.2.2.1 = q.1 := by rw [← hp.2]
    have e2 : p.2.2.2 = q.2 := by rw [← hp.2]
    have e3 : p2.2.2.1 = q.1 := by rw [← hp2.2]
    have e4 : p2.2.2.2 = q.2 := by rw [← hp2.2]
    have h1 : p.2.2.1 = p2.2.2.1 := by rw [e1, e3]
    have h2 : p.2.2.2 = p2.2.2.2 := by rw [e2, e4]
    exact Prod.ext hpp.1 (Prod.ext hpp.2 (Prod.ext h1 h2))
  · intro r hr
    rw [Finset.mem_product, mem_nbrs2, mem_nbrs2] at hr
    obtain ⟨⟨ha, hac, had⟩, hb, hbc, hbd⟩ := hr
    refine ⟨(r.1, r.2, q.1, q.2), ?_, rfl⟩
    rw [Finset.mem_filter, mem_books]
    exact ⟨⟨⟨ha, hb, hqC, hqD⟩, hac, had, hbc, hbd, hqcd⟩, rfl⟩

/-! ## Fibra sobre `E(B,D)`: la entrada del paso 2 -/

/-- Los libros con `(b,d)` fijo son las aristas del rectángulo `(N(d)∩A , N(b)∩N(d)∩C)`. -/
theorem books_eq_sum_bd (A B C D : Finset α) :
    (books G A B C D).card
      = ∑ q ∈ G.interedges B D,
          (G.interedges (nbrs G A q.2) (nbrs2 G C q)).card := by
  classical
  have hmem : ∀ p ∈ books G A B C D, (p.2.1, p.2.2.2) ∈ G.interedges B D := by
    intro p hp
    rw [mem_books] at hp
    rw [SimpleGraph.mk_mem_interedges_iff]
    exact ⟨hp.1.2.1, hp.1.2.2.2, hp.2.2.2.2.1⟩
  rw [Finset.card_eq_sum_card_fiberwise hmem]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [SimpleGraph.mem_interedges_iff] at hq
  obtain ⟨hqB, hqD, hqbd⟩ := hq
  apply Finset.card_bij (fun p _ => (p.1, p.2.2.1))
  · intro p hp
    rw [Finset.mem_filter, mem_books] at hp
    obtain ⟨⟨⟨ha, -, hc, -⟩, hac, had, hbc, -, hcd⟩, hpq⟩ := hp
    have hb : p.2.1 = q.1 := by rw [← hpq]
    have hd : p.2.2.2 = q.2 := by rw [← hpq]
    rw [SimpleGraph.mk_mem_interedges_iff]
    refine ⟨mem_nbrs.2 ⟨ha, hd ▸ had⟩,
            mem_nbrs2.2 ⟨hc, (hb ▸ hbc).symm, hd ▸ hcd⟩, hac⟩
  · intro p hp p2 hp2 hpp
    rw [Finset.mem_filter] at hp hp2
    simp only [Prod.mk.injEq] at hpp
    have e1 : p.2.1 = q.1 := by rw [← hp.2]
    have e2 : p.2.2.2 = q.2 := by rw [← hp.2]
    have e3 : p2.2.1 = q.1 := by rw [← hp2.2]
    have e4 : p2.2.2.2 = q.2 := by rw [← hp2.2]
    have h1 : p.2.1 = p2.2.1 := by rw [e1, e3]
    have h2 : p.2.2.2 = p2.2.2.2 := by rw [e2, e4]
    exact Prod.ext hpp.1 (Prod.ext h1 (Prod.ext hpp.2 h2))
  · intro r hr
    rw [SimpleGraph.mk_mem_interedges_iff, mem_nbrs, mem_nbrs2] at hr
    obtain ⟨⟨ha, had⟩, ⟨hc, hcb, hcd⟩, hac⟩ := hr
    refine ⟨(r.1, q.1, r.2, q.2), ?_, rfl⟩
    rw [Finset.mem_filter, mem_books]
    exact ⟨⟨⟨ha, hqB, hc, hqD⟩, hac, had, hcb.symm, hqbd, hcd⟩, rfl⟩

/-! ## El segundo paso -/

/-- **Segundo paso para `K₄`.**  Sustituir el indicador de la pareja `(A,C)` por su densidad
cuesta a lo sumo `|B|·|D|·ε·|A|·|C|`.  El rectángulo de cada fibra es
`(N(d)∩A , N(b)∩N(d)∩C)`. -/
theorem step_two_K4 {ε : ℚ} (hε : 0 ≤ ε) {A B C D : Finset α}
    (h : OneStepEstimate.DiscrepAt G ε (G.edgeDensity A C) A C) :
    |((books G A B C D).card : ℚ)
        - G.edgeDensity A C
            * ∑ q ∈ G.interedges B D,
                (((nbrs G A q.2).card : ℚ) * ((nbrs2 G C q).card : ℚ))|
      ≤ (B.card : ℚ) * (D.card : ℚ) * (ε * A.card * C.card) := by
  classical
  have hsum : ((books G A B C D).card : ℚ)
      = ∑ q ∈ G.interedges B D,
          ((G.interedges (nbrs G A q.2) (nbrs2 G C q)).card : ℚ) := by
    rw [← Nat.cast_sum, ← books_eq_sum_bd]
  rw [hsum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hstep : ∀ q ∈ G.interedges B D,
      |((G.interedges (nbrs G A q.2) (nbrs2 G C q)).card : ℚ)
        - G.edgeDensity A C * (((nbrs G A q.2).card : ℚ) * ((nbrs2 G C q).card : ℚ))|
      ≤ ε * A.card * C.card := by
    intro q _
    have hsub : nbrs G A q.2 ⊆ A := Finset.filter_subset _ _
    have htub : nbrs2 G C q ⊆ C := Finset.filter_subset _ _
    have hkey := h _ hsub _ htub
    have hfac : G.edgeDensity A C * (((nbrs G A q.2).card : ℚ) * ((nbrs2 G C q).card : ℚ))
        = G.edgeDensity A C * ((nbrs G A q.2).card : ℚ) * ((nbrs2 G C q).card : ℚ) := by ring
    rw [hfac]
    exact hkey
  have hbound : ∑ q ∈ G.interedges B D,
      |((G.interedges (nbrs G A q.2) (nbrs2 G C q)).card : ℚ)
        - G.edgeDensity A C * (((nbrs G A q.2).card : ℚ) * ((nbrs2 G C q).card : ℚ))|
      ≤ ((G.interedges B D).card : ℚ) * (ε * A.card * C.card) := by
    calc _ ≤ ∑ _q ∈ G.interedges B D, ε * A.card * C.card := Finset.sum_le_sum hstep
      _ = ((G.interedges B D).card : ℚ) * (ε * A.card * C.card) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  refine le_trans hbound ?_
  have hbd : ((G.interedges B D).card : ℚ) ≤ (B.card : ℚ) * (D.card : ℚ) := by
    have hnat := G.card_interedges_le_mul B D
    exact_mod_cast hnat
  have hpos : (0 : ℚ) ≤ ε * A.card * C.card := by positivity
  calc ((G.interedges B D).card : ℚ) * (ε * A.card * C.card)
      ≤ ((B.card : ℚ) * (D.card : ℚ)) * (ε * A.card * C.card) :=
        mul_le_mul_of_nonneg_right hbd hpos
    _ = (B.card : ℚ) * (D.card : ℚ) * (ε * A.card * C.card) := by ring

end PaperIV.TelescopeK4Step2
