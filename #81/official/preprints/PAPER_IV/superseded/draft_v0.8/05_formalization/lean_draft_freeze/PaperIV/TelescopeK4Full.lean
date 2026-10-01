import PaperIV.TelescopeK4Step2

/-!
# `K₄` completo: paso 3 y ensamblaje

Novena pieza de **GAP-RP01**.  Cierra el lema de conteo para `K₄`:

```
| #K₄ transversales − d_AB·d_AC·d_AD·d_BC·d_BD·d_CD·|A||B||C||D| |  ≤  5·ε·|A||B||C||D|.
```

## La cadena

```
#K₄  --(paso 1, quita AB)-->  books  --(paso 2, quita AC)-->  fans
     --(paso 3, quita AD)-->  |A| · #K₃(B,C,D)  --(lema K₃)-->  densidades
```

| paso | quita | fibra sobre | rectángulo | error |
|---|---|---|---|---|
| 1 | `AB` | `(c,d) ∈ E(C,D)` | `(N(c)∩N(d)∩A , N(c)∩N(d)∩B)` | `ε\|A\|\|B\|\|C\|\|D\|` |
| 2 | `AC` | `(b,d) ∈ E(B,D)` | `(N(d)∩A , N(b)∩N(d)∩C)` | `ε\|A\|\|B\|\|C\|\|D\|` |
| 3 | `AD` | `(b,c) ∈ E(B,C)` | `(A , N(b)∩N(c)∩D)` | `ε\|A\|\|B\|\|C\|\|D\|` |
| — | — | — | `counting_lemma_K3` sobre `(B,C,D)` | `2ε\|A\|\|B\|\|C\|\|D\|` |
| | | | **total** | **`5ε\|A\|\|B\|\|C\|\|D\|`** |

**Cinco y no seis**: quitadas las tres parejas incidentes a `A`, lo que queda **es** el conteo
de `K₃` sobre las otras tres partes, ya demostrado, y ése cuesta dos pasos en vez de tres
(`TelescopeK3.last_step_free`).

Obsérvese cómo el rectángulo **se va simplificando**: en el paso 3 el lado izquierdo es ya
`A` entero.

## Contenido

* `fans` — los `K₄` menos `AB` y `AC`: el objeto que sale del paso 2.
* `fans_eq_sum_bd`, `fans_eq_sum_bc` — sus dos descomposiciones en fibras, que engranan el
  paso 2 con el 3.
* `sum_nbrs2_eq_triangles` — `∑_{(b,c)∈E(B,C)} |N(b)∩N(c)∩D| = #K₃(B,C,D)`: el punto donde la
  cadena entra en el lema `K₃`.
* `step_three_K4` — el tercer paso.
* `counting_lemma_K4` — **el lema de conteo para `K₄`**, con constante `5`.
-/

namespace PaperIV.TelescopeK4Full

open Finset
open PaperIV.TelescopeK3 (nbrs mem_nbrs)
open PaperIV.TelescopeK4 (nbrs2 mem_nbrs2)
open PaperIV.TelescopeK4Step2 (books mem_books books_eq_sum_cd books_eq_sum_bd step_two_K4)

variable {α : Type*} [DecidableEq α] {G : SimpleGraph α} [DecidableRel G.Adj]

/-- El predicado de «abanico»: un `K₄` **menos** las aristas `AB` y `AC`. -/
def isFan (G : SimpleGraph α) (p : α × α × α × α) : Prop :=
  G.Adj p.1 p.2.2.2 ∧ G.Adj p.2.1 p.2.2.1 ∧ G.Adj p.2.1 p.2.2.2 ∧ G.Adj p.2.2.1 p.2.2.2

instance : DecidablePred (isFan G) := by unfold isFan; infer_instance

/-- Las cuádruplas transversales que forman un abanico. -/
def fans (G : SimpleGraph α) [DecidableRel G.Adj] (A B C D : Finset α) :
    Finset (α × α × α × α) :=
  (A ×ˢ B ×ˢ C ×ˢ D).filter (isFan G)

theorem mem_fans {A B C D : Finset α} (p : α × α × α × α) :
    p ∈ fans G A B C D ↔
      (p.1 ∈ A ∧ p.2.1 ∈ B ∧ p.2.2.1 ∈ C ∧ p.2.2.2 ∈ D) ∧ isFan G p := by
  simp only [fans, Finset.mem_filter, Finset.mem_product]

/-! ## Las dos fibras de los abanicos -/

/-- Fibra sobre `E(B,D)`: **la salida del paso 2**.  Con `(b,d)` fijo el abanico es el
producto `(N(d)∩A) × (N(b)∩N(d)∩C)`: sin condición entre `a` y `c`, la arista quitada. -/
theorem fans_eq_sum_bd (A B C D : Finset α) :
    (fans G A B C D).card
      = ∑ q ∈ G.interedges B D, (nbrs G A q.2).card * (nbrs2 G C q).card := by
  classical
  have hmem : ∀ p ∈ fans G A B C D, (p.2.1, p.2.2.2) ∈ G.interedges B D := by
    intro p hp
    rw [mem_fans] at hp
    rw [SimpleGraph.mk_mem_interedges_iff]
    exact ⟨hp.1.2.1, hp.1.2.2.2, hp.2.2.2.1⟩
  rw [Finset.card_eq_sum_card_fiberwise hmem]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [SimpleGraph.mem_interedges_iff] at hq
  obtain ⟨hqB, hqD, hqbd⟩ := hq
  rw [← Finset.card_product]
  apply Finset.card_bij (fun p _ => (p.1, p.2.2.1))
  · intro p hp
    rw [Finset.mem_filter, mem_fans] at hp
    obtain ⟨⟨⟨ha, -, hc, -⟩, had, hbc, -, hcd⟩, hpq⟩ := hp
    have hb : p.2.1 = q.1 := by rw [← hpq]
    have hd : p.2.2.2 = q.2 := by rw [← hpq]
    exact Finset.mem_product.2
      ⟨mem_nbrs.2 ⟨ha, hd ▸ had⟩, mem_nbrs2.2 ⟨hc, (hb ▸ hbc).symm, hd ▸ hcd⟩⟩
  · intro p hp p2 hp2 hpp
    rw [Finset.mem_filter] at hp hp2
    simp only [Prod.mk.injEq] at hpp
    have e1 : p.2.1 = q.1 := by rw [← hp.2]
    have e2 : p.2.2.2 = q.2 := by rw [← hp.2]
    have e3 : p2.2.1 = q.1 := by rw [← hp2.2]
    have e4 : p2.2.2.2 = q.2 := by rw [← hp2.2]
    exact Prod.ext hpp.1 (Prod.ext (by rw [e1, e3]) (Prod.ext hpp.2 (by rw [e2, e4])))
  · intro r hr
    rw [Finset.mem_product, mem_nbrs, mem_nbrs2] at hr
    obtain ⟨⟨ha, had⟩, hc, hcb, hcd⟩ := hr
    refine ⟨(r.1, q.1, r.2, q.2), ?_, rfl⟩
    rw [Finset.mem_filter, mem_fans]
    exact ⟨⟨⟨ha, hqB, hc, hqD⟩, had, hcb.symm, hqbd, hcd⟩, rfl⟩

/-- Fibra sobre `E(B,C)`: **la entrada del paso 3**.  Con `(b,c)` fijo el abanico es el
rectángulo `(A , N(b)∩N(c)∩D)`.  El lado izquierdo es ya `A` entero. -/
theorem fans_eq_sum_bc (A B C D : Finset α) :
    (fans G A B C D).card
      = ∑ q ∈ G.interedges B C, (G.interedges A (nbrs2 G D q)).card := by
  classical
  have hmem : ∀ p ∈ fans G A B C D, (p.2.1, p.2.2.1) ∈ G.interedges B C := by
    intro p hp
    rw [mem_fans] at hp
    rw [SimpleGraph.mk_mem_interedges_iff]
    exact ⟨hp.1.2.1, hp.1.2.2.1, hp.2.2.1⟩
  rw [Finset.card_eq_sum_card_fiberwise hmem]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [SimpleGraph.mem_interedges_iff] at hq
  obtain ⟨hqB, hqC, hqbc⟩ := hq
  apply Finset.card_bij (fun p _ => (p.1, p.2.2.2))
  · intro p hp
    rw [Finset.mem_filter, mem_fans] at hp
    obtain ⟨⟨⟨ha, -, -, hd⟩, had, -, hbd, hcd⟩, hpq⟩ := hp
    have hb : p.2.1 = q.1 := by rw [← hpq]
    have hc : p.2.2.1 = q.2 := by rw [← hpq]
    rw [SimpleGraph.mk_mem_interedges_iff]
    exact ⟨ha, mem_nbrs2.2 ⟨hd, (hb ▸ hbd).symm, (hc ▸ hcd).symm⟩, had⟩
  · intro p hp p2 hp2 hpp
    rw [Finset.mem_filter] at hp hp2
    simp only [Prod.mk.injEq] at hpp
    have e1 : p.2.1 = q.1 := by rw [← hp.2]
    have e2 : p.2.2.1 = q.2 := by rw [← hp.2]
    have e3 : p2.2.1 = q.1 := by rw [← hp2.2]
    have e4 : p2.2.2.1 = q.2 := by rw [← hp2.2]
    exact Prod.ext hpp.1 (Prod.ext (by rw [e1, e3]) (Prod.ext (by rw [e2, e4]) hpp.2))
  · intro r hr
    rw [SimpleGraph.mk_mem_interedges_iff, mem_nbrs2] at hr
    obtain ⟨ha, ⟨hd, hdb, hdc⟩, had⟩ := hr
    refine ⟨(r.1, q.1, q.2, r.2), ?_, rfl⟩
    rw [Finset.mem_filter, mem_fans]
    exact ⟨⟨⟨ha, hqB, hqC, hd⟩, had, hqbc, hdb.symm, hdc.symm⟩, rfl⟩

/-! ## La entrada al lema `K₃` -/

/-- `∑_{(b,c)∈E(B,C)} |N(b)∩N(c)∩D| = #K₃(B,C,D)`.  Es el punto donde la cadena de `K₄`
entra en el lema de `K₃` ya demostrado. -/
theorem sum_nbrs2_eq_triangles (B C D : Finset α) :
    ∑ q ∈ G.interedges B C, (nbrs2 G D q).card
      = ((B ×ˢ C ×ˢ D).filter
          fun p => G.Adj p.1 p.2.1 ∧ G.Adj p.1 p.2.2 ∧ G.Adj p.2.1 p.2.2).card := by
  classical
  have hmem : ∀ p ∈ (B ×ˢ C ×ˢ D).filter
      (fun p => G.Adj p.1 p.2.1 ∧ G.Adj p.1 p.2.2 ∧ G.Adj p.2.1 p.2.2),
      (p.1, p.2.1) ∈ G.interedges B C := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_product] at hp
    rw [SimpleGraph.mk_mem_interedges_iff]
    exact ⟨hp.1.1, hp.1.2.1, hp.2.1⟩
  rw [Finset.card_eq_sum_card_fiberwise hmem]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [SimpleGraph.mem_interedges_iff] at hq
  obtain ⟨hqB, hqC, hqbc⟩ := hq
  apply Finset.card_bij (fun d _ => (q.1, q.2, d))
  · intro d hd
    rw [mem_nbrs2] at hd
    rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_product, Finset.mem_product]
    exact ⟨⟨⟨hqB, hqC, hd.1⟩, hqbc, hd.2.1.symm, hd.2.2.symm⟩, rfl⟩
  · intro d _ d2 _ h
    simpa using h
  · intro p hp
    rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_product, Finset.mem_product] at hp
    obtain ⟨⟨⟨-, -, hpD⟩, -, hbd, hcd⟩, hpq⟩ := hp
    have hb : p.1 = q.1 := by rw [← hpq]
    have hc : p.2.1 = q.2 := by rw [← hpq]
    refine ⟨p.2.2, mem_nbrs2.2 ⟨hpD, hb ▸ hbd.symm, hc ▸ hcd.symm⟩, ?_⟩
    rw [← hb, ← hc]

/-! ## El tercer paso -/

/-- **Tercer paso para `K₄`.**  Sustituir el indicador de la pareja `(A,D)` por su densidad
cuesta a lo sumo `|B|·|C|·ε·|A|·|D|`.  El rectángulo de cada fibra es `(A , N(b)∩N(c)∩D)`. -/
theorem step_three_K4 {ε : ℚ} (hε : 0 ≤ ε) {A B C D : Finset α}
    (h : OneStepEstimate.DiscrepAt G ε (G.edgeDensity A D) A D) :
    |((fans G A B C D).card : ℚ)
        - G.edgeDensity A D * (A.card : ℚ)
            * (((B ×ˢ C ×ˢ D).filter
                fun p => G.Adj p.1 p.2.1 ∧ G.Adj p.1 p.2.2 ∧ G.Adj p.2.1 p.2.2).card : ℚ)|
      ≤ (B.card : ℚ) * (C.card : ℚ) * (ε * A.card * D.card) := by
  classical
  have hsum : ((fans G A B C D).card : ℚ)
      = ∑ q ∈ G.interedges B C, ((G.interedges A (nbrs2 G D q)).card : ℚ) := by
    rw [← Nat.cast_sum, ← fans_eq_sum_bc]
  have htri : (((B ×ˢ C ×ˢ D).filter
      fun p => G.Adj p.1 p.2.1 ∧ G.Adj p.1 p.2.2 ∧ G.Adj p.2.1 p.2.2).card : ℚ)
      = ∑ q ∈ G.interedges B C, ((nbrs2 G D q).card : ℚ) := by
    rw [← Nat.cast_sum, sum_nbrs2_eq_triangles]
  rw [hsum, htri, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hstep : ∀ q ∈ G.interedges B C,
      |((G.interedges A (nbrs2 G D q)).card : ℚ)
        - G.edgeDensity A D * (A.card : ℚ) * ((nbrs2 G D q).card : ℚ)|
      ≤ ε * A.card * D.card := by
    intro q _
    have hsub : (A : Finset α) ⊆ A := Finset.Subset.refl A
    have htub : nbrs2 G D q ⊆ D := Finset.filter_subset _ _
    exact h _ hsub _ htub
  have hbound : ∑ q ∈ G.interedges B C,
      |((G.interedges A (nbrs2 G D q)).card : ℚ)
        - G.edgeDensity A D * (A.card : ℚ) * ((nbrs2 G D q).card : ℚ)|
      ≤ ((G.interedges B C).card : ℚ) * (ε * A.card * D.card) := by
    calc _ ≤ ∑ _q ∈ G.interedges B C, ε * A.card * D.card := Finset.sum_le_sum hstep
      _ = ((G.interedges B C).card : ℚ) * (ε * A.card * D.card) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  refine le_trans hbound ?_
  have hbc : ((G.interedges B C).card : ℚ) ≤ (B.card : ℚ) * (C.card : ℚ) := by
    have hnat := G.card_interedges_le_mul B C
    exact_mod_cast hnat
  have hpos : (0 : ℚ) ≤ ε * A.card * D.card := by positivity
  calc ((G.interedges B C).card : ℚ) * (ε * A.card * D.card)
      ≤ ((B.card : ℚ) * (C.card : ℚ)) * (ε * A.card * D.card) :=
        mul_le_mul_of_nonneg_right hbc hpos
    _ = (B.card : ℚ) * (C.card : ℚ) * (ε * A.card * D.card) := by ring


/-! ## El lema de conteo para `K₄` -/

set_option maxHeartbeats 1000000 in
/-- **El lema de conteo para `K₄`.**  Con las cinco parejas `ε`-uniformes que la cadena
consume,
```
| #K₄ transversales − d_AB·d_AC·d_AD·d_BC·d_BD·d_CD·|A||B||C||D| |  ≤  5·ε·|A||B||C||D|.
```
Constante `5` y no `6`: los tres pasos incidentes a `A` más el lema `K₃` sobre `(B,C,D)`,
que cuesta dos. -/
theorem counting_lemma_K4 {ε : ℚ} (hε : 0 ≤ ε) {A B C D : Finset α}
    (hAB : OneStepEstimate.DiscrepAt G ε (G.edgeDensity A B) A B)
    (hAC : OneStepEstimate.DiscrepAt G ε (G.edgeDensity A C) A C)
    (hAD : OneStepEstimate.DiscrepAt G ε (G.edgeDensity A D) A D)
    (hBC : OneStepEstimate.DiscrepAt G ε (G.edgeDensity B C) B C)
    (hBD : OneStepEstimate.DiscrepAt G ε (G.edgeDensity B D) B D) :
    |((PaperIV.TelescopeK4.k4s G A B C D).card : ℚ)
        - G.edgeDensity A B * G.edgeDensity A C * G.edgeDensity A D
            * (G.edgeDensity B C * G.edgeDensity B D * G.edgeDensity C D)
            * A.card * B.card * C.card * D.card|
      ≤ 5 * (ε * A.card * B.card * C.card * D.card) := by
  classical
  set T : ℚ := (((B ×ˢ C ×ˢ D).filter
      fun p => G.Adj p.1 p.2.1 ∧ G.Adj p.1 p.2.2 ∧ G.Adj p.2.1 p.2.2).card : ℚ) with hT
  set K : ℚ := ((PaperIV.TelescopeK4.k4s G A B C D).card : ℚ) with hK
  set Bk : ℚ := ((books G A B C D).card : ℚ) with hBk
  set Fn : ℚ := ((fans G A B C D).card : ℚ) with hFn
  set dAB : ℚ := G.edgeDensity A B with hdAB
  set dAC : ℚ := G.edgeDensity A C with hdAC
  set dAD : ℚ := G.edgeDensity A D with hdAD
  set dBC : ℚ := G.edgeDensity B C with hdBC
  set dBD : ℚ := G.edgeDensity B D with hdBD
  set dCD : ℚ := G.edgeDensity C D with hdCD
  set a : ℚ := (A.card : ℚ) with ha
  set b : ℚ := (B.card : ℚ) with hb
  set c : ℚ := (C.card : ℚ) with hc
  set d : ℚ := (D.card : ℚ) with hd
  have dAB0 : 0 ≤ dAB := G.edgeDensity_nonneg A B
  have dAB1 : dAB ≤ 1 := G.edgeDensity_le_one A B
  have dAC0 : 0 ≤ dAC := G.edgeDensity_nonneg A C
  have dAC1 : dAC ≤ 1 := G.edgeDensity_le_one A C
  have dAD0 : 0 ≤ dAD := G.edgeDensity_nonneg A D
  have dAD1 : dAD ≤ 1 := G.edgeDensity_le_one A D
  have ha0 : (0 : ℚ) ≤ a := by positivity
  -- paso 1
  have h1 := PaperIV.TelescopeK4.step_one_K4 (G := G) hε hAB (A := A) (B := B) (C := C) (D := D)
  have e1 : ∑ q ∈ G.interedges C D,
      ((nbrs2 G A q).card : ℚ) * ((nbrs2 G B q).card : ℚ) = Bk := by
    rw [hBk, books_eq_sum_cd]; push_cast; ring
  rw [e1] at h1
  -- paso 2
  have h2 := step_two_K4 (G := G) hε hAC (A := A) (B := B) (C := C) (D := D)
  have e2 : ∑ q ∈ G.interedges B D,
      (((nbrs G A q.2).card : ℚ) * ((nbrs2 G C q).card : ℚ)) = Fn := by
    rw [hFn, fans_eq_sum_bd]; push_cast; ring
  rw [e2] at h2
  -- paso 3 y lema K3
  have h3 := step_three_K4 (G := G) hε hAD (A := A) (B := B) (C := C) (D := D)
  have h4 := PaperIV.TelescopeK3Full.counting_lemma_K3 (G := G) hε hBC hBD
  -- cotas por paso
  have b1 : |K - dAB * Bk| ≤ ε * a * b * c * d := by
    calc |K - dAB * Bk| ≤ c * d * (ε * a * b) := h1
      _ = ε * a * b * c * d := by ring
  have b2 : |dAB * Bk - dAB * (dAC * Fn)| ≤ ε * a * b * c * d := by
    have hfac : dAB * Bk - dAB * (dAC * Fn) = dAB * (Bk - dAC * Fn) := by ring
    rw [hfac, abs_mul, abs_of_nonneg dAB0]
    have habs : (0 : ℚ) ≤ |Bk - dAC * Fn| := abs_nonneg _
    calc dAB * |Bk - dAC * Fn| ≤ 1 * |Bk - dAC * Fn| :=
          mul_le_mul_of_nonneg_right dAB1 habs
      _ = |Bk - dAC * Fn| := one_mul _
      _ ≤ b * d * (ε * a * c) := h2
      _ = ε * a * b * c * d := by ring
  have b3 : |dAB * (dAC * Fn) - dAB * (dAC * (dAD * a * T))| ≤ ε * a * b * c * d := by
    have hfac : dAB * (dAC * Fn) - dAB * (dAC * (dAD * a * T))
        = (dAB * dAC) * (Fn - dAD * a * T) := by ring
    rw [hfac, abs_mul, abs_of_nonneg (mul_nonneg dAB0 dAC0)]
    have habs : (0 : ℚ) ≤ |Fn - dAD * a * T| := abs_nonneg _
    have hp : dAB * dAC ≤ 1 := by
      calc dAB * dAC ≤ dAB * 1 := mul_le_mul_of_nonneg_left dAC1 dAB0
        _ = dAB := mul_one _
        _ ≤ 1 := dAB1
    calc (dAB * dAC) * |Fn - dAD * a * T| ≤ 1 * |Fn - dAD * a * T| :=
          mul_le_mul_of_nonneg_right hp habs
      _ = |Fn - dAD * a * T| := one_mul _
      _ ≤ b * c * (ε * a * d) := h3
      _ = ε * a * b * c * d := by ring
  have b4 : |dAB * (dAC * (dAD * a * T))
      - dAB * dAC * dAD * (dBC * dBD * dCD) * a * b * c * d| ≤ 2 * (ε * a * b * c * d) := by
    have hfac : dAB * (dAC * (dAD * a * T))
        - dAB * dAC * dAD * (dBC * dBD * dCD) * a * b * c * d
        = (dAB * dAC * dAD * a) * (T - dBC * dBD * dCD * b * c * d) := by ring
    rw [hfac, abs_mul,
      abs_of_nonneg (mul_nonneg (mul_nonneg (mul_nonneg dAB0 dAC0) dAD0) ha0)]
    have habs : (0 : ℚ) ≤ |T - dBC * dBD * dCD * b * c * d| := abs_nonneg _
    have hd12 : dAB * dAC ≤ 1 := by
      calc dAB * dAC ≤ dAB * 1 := mul_le_mul_of_nonneg_left dAC1 dAB0
        _ = dAB := mul_one _
        _ ≤ 1 := dAB1
    have hd3 : dAB * dAC * dAD ≤ 1 := by
      calc dAB * dAC * dAD ≤ (dAB * dAC) * 1 :=
            mul_le_mul_of_nonneg_left dAD1 (mul_nonneg dAB0 dAC0)
        _ = dAB * dAC := mul_one _
        _ ≤ 1 := hd12
    have hp : dAB * dAC * dAD * a ≤ a := by
      calc dAB * dAC * dAD * a ≤ 1 * a := mul_le_mul_of_nonneg_right hd3 ha0
        _ = a := one_mul a
    calc (dAB * dAC * dAD * a) * |T - dBC * dBD * dCD * b * c * d|
        ≤ a * |T - dBC * dBD * dCD * b * c * d| :=
          mul_le_mul_of_nonneg_right hp habs
      _ ≤ a * (2 * (ε * b * c * d)) := mul_le_mul_of_nonneg_left h4 ha0
      _ = 2 * (ε * a * b * c * d) := by ring
  -- ensamblaje
  obtain ⟨l1, u1⟩ := abs_le.1 b1
  obtain ⟨l2, u2⟩ := abs_le.1 b2
  obtain ⟨l3, u3⟩ := abs_le.1 b3
  obtain ⟨l4, u4⟩ := abs_le.1 b4
  rw [abs_le]
  constructor <;> linarith

end PaperIV.TelescopeK4Full
