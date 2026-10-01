import PaperIV.RootedK4Degree

/-!
# El conteo enraizado de `K₄` sobre una cuádrupla de partes regulares

Segunda mitad de la pieza local.  `RootedK4Degree` puso la combinatoria —la fibra de la raíz se
inyecta en las hiperaristas que contienen la arista, y los pares de copias con la misma raíz son
las copias del patrón doblado—.  Aquí se pone la **regularidad**:

* `count_transversal_K4` — primer momento, con `patCount_approx` sobre `patK4` (constante `6`);
* `count_rootPairs` — segundo momento, con `counting_doubledK4` (constante `11`);
* `second_moment_rooted` — `∑_{e} (c e − A)² ≤ 23·δ·t⁶` con `A = rootProd · t²`;
* `card_badRootEdges_mul_le` — Chebyshev: las raíces malas son pocas;
* `deg_ge_of_notMem_badRootEdges` — **la cota inferior del grado** fuera de las raíces malas.

`rootProd G V` es el producto de las **cinco** densidades que no son la de la pareja raíz
`(V 0, V 1)`; la escala esperada del conteo enraizado es `A = rootProd · t²`.
-/

namespace PaperIV.RootedK4Degree

open Finset
open PaperIV.OneStepEstimate
open PaperIV.PatternCounting PaperIV.RegularityFormat PaperIV.RC01Candidates
open PaperIV.FarRounding
open PaperIV.NibbleHypotheses (deg)
open PaperIV.RootedCountingBridge (fiber)

variable {α : Type*} [Fintype α] [DecidableEq α]
variable {G : SimpleGraph α} [DecidableRel G.Adj]

/-! ## 1. La escala esperada -/

/-- El producto de las cinco densidades que no son la de la pareja raíz. -/
def rootProd (G : SimpleGraph α) [DecidableRel G.Adj] (V : Fin 4 → Finset α) : ℚ :=
  ∏ e ∈ patK4root, G.edgeDensity (V e.1) (V e.2)

omit [Fintype α] [DecidableEq α] in
theorem rootProd_nonneg (V : Fin 4 → Finset α) : 0 ≤ rootProd G V :=
  Finset.prod_nonneg fun _ _ => G.edgeDensity_nonneg _ _

omit [Fintype α] [DecidableEq α] in
theorem rootProd_le_one (V : Fin 4 → Finset α) : rootProd G V ≤ 1 :=
  Finset.prod_le_one (fun _ _ => G.edgeDensity_nonneg _ _)
    (fun _ _ => G.edgeDensity_le_one _ _)

omit [Fintype α] [DecidableEq α] in
theorem prod_patK4_eq (V : Fin 4 → Finset α) :
    (∏ e ∈ patK4, G.edgeDensity (V e.1) (V e.2))
      = G.edgeDensity (V 0) (V 1) * rootProd G V := by
  rw [rootProd, patK4_eq_insert, Finset.prod_insert root_notMem_patK4root]

omit [Fintype α] in
/-- El número de aristas raíz es exactamente `d₀₁ · t²`. -/
theorem card_rootEdges_eq {V : Fin 4 → Finset α} {t : ℕ} (hcard : ∀ i, (V i).card = t)
    (hdisj : Disjoint (V 0) (V 1)) :
    ((rootEdges G V).card : ℚ) = G.edgeDensity (V 0) (V 1) * (t : ℚ) ^ 2 := by
  rw [card_rootEdges hdisj, card_interedges_eq, hcard 0, hcard 1]
  ring

/-! ## 2. Los dos conteos -/

/-- **Primer momento.**  El número de copias transversales de `K₄` dista a lo sumo `6δt⁴` del
producto de las seis densidades por `t⁴`. -/
theorem count_transversal_K4 {δ : ℚ} (hδ : 0 ≤ δ) {V : Fin 4 → Finset α} {t : ℕ}
    (hcard : ∀ i, (V i).card = t)
    (hdisc : ∀ i j : Fin 4, i ≠ j → DiscrepAt G δ (G.edgeDensity (V i) (V j)) (V i) (V j)) :
    |((transversal G V patK4).card : ℚ)
        - (G.edgeDensity (V 0) (V 1) * rootProd G V) * (t : ℚ) ^ 4|
      ≤ 6 * δ * (t : ℚ) ^ 4 := by
  have hprodcard : ∏ i, ((V i).card : ℚ) = (t : ℚ) ^ 4 := by
    rw [Fin.prod_univ_four, hcard 0, hcard 1, hcard 2, hcard 3]
    ring
  have h := patCount_approx (G := G) hδ V (fun e => G.edgeDensity (V e.1) (V e.2)) patK4
    patK4_sym patK4_ne (fun e _ => G.edgeDensity_nonneg _ _)
    (fun e _ => G.edgeDensity_le_one _ _)
    (fun e he => hdisc e.1 e.2 (patK4_ne e he))
  rw [patCount_eq_card_transversal, hprodcard, prod_patK4_eq, card_patK4] at h
  exact_mod_cast h

/-- Las once parejas del patrón doblado conectan índices distintos de la cuádrupla. -/
theorem dblIdx_ne : ∀ e ∈ doubledK4, dblIdx e.1 ≠ dblIdx e.2 := by decide

/-- **Segundo momento.**  El conteo del patrón doblado dista a lo sumo `11δt⁶` de
`d₀₁ · rootProd² · t⁶`. -/
theorem count_rootPairs {δ : ℚ} (hδ : 0 ≤ δ) {V : Fin 4 → Finset α} {t : ℕ}
    (hcard : ∀ i, (V i).card = t)
    (hdisc : ∀ i j : Fin 4, i ≠ j → DiscrepAt G δ (G.edgeDensity (V i) (V j)) (V i) (V j)) :
    |((transversal G (V ∘ dblIdx) doubledK4).card : ℚ)
        - (G.edgeDensity (V 0) (V 1) * rootProd G V ^ 2) * (t : ℚ) ^ 6|
      ≤ 11 * δ * (t : ℚ) ^ 6 := by
  have hprodcard : ∏ i, (((V ∘ dblIdx) i).card : ℚ) = (t : ℚ) ^ 6 := by
    rw [Fin.prod_univ_six]
    simp only [Function.comp_apply]
    rw [show dblIdx 0 = 0 from rfl, show dblIdx 1 = 1 from rfl, show dblIdx 2 = 2 from rfl,
      show dblIdx 3 = 3 from rfl, show dblIdx 4 = 2 from rfl, show dblIdx 5 = 3 from rfl,
      hcard 0, hcard 1, hcard 2, hcard 3]
    ring
  have hprodd : (∏ e ∈ doubledK4,
        G.edgeDensity ((V ∘ dblIdx) e.1) ((V ∘ dblIdx) e.2))
      = G.edgeDensity (V 0) (V 1) * rootProd G V ^ 2 := by
    rw [rootProd]
    simp only [doubledK4, patK4root, Function.comp_apply]
    rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide),
      Finset.prod_insert (by decide), Finset.prod_insert (by decide),
      Finset.prod_insert (by decide), Finset.prod_insert (by decide),
      Finset.prod_insert (by decide), Finset.prod_insert (by decide),
      Finset.prod_insert (by decide), Finset.prod_insert (by decide),
      Finset.prod_singleton, Finset.prod_insert (by decide),
      Finset.prod_insert (by decide), Finset.prod_insert (by decide),
      Finset.prod_insert (by decide), Finset.prod_singleton]
    rw [show dblIdx 0 = 0 from rfl, show dblIdx 1 = 1 from rfl, show dblIdx 2 = 2 from rfl,
      show dblIdx 3 = 3 from rfl, show dblIdx 4 = 2 from rfl, show dblIdx 5 = 3 from rfl]
    ring
  have h := counting_doubledK4 (G := G) hδ (V ∘ dblIdx)
    (fun e => G.edgeDensity ((V ∘ dblIdx) e.1) ((V ∘ dblIdx) e.2))
    (fun e _ => G.edgeDensity_nonneg _ _) (fun e _ => G.edgeDensity_le_one _ _)
    (fun e he => hdisc _ _ (dblIdx_ne e he))
  rw [patCount_eq_card_transversal, hprodcard, hprodd] at h
  exact_mod_cast h

/-! ## 3. El segundo momento del conteo enraizado -/

/-- **La cota de segundo momento.**  Con `A = rootProd · t²` la desviación cuadrática total del
conteo enraizado no pasa de `23·δ·t⁶`. -/
theorem second_moment_rooted {δ : ℚ} (hδ : 0 ≤ δ) {V : Fin 4 → Finset α} {t : ℕ}
    (hcard : ∀ i, (V i).card = t)
    (hdisj : ∀ i j : Fin 4, i ≠ j → Disjoint (V i) (V j))
    (hdisc : ∀ i j : Fin 4, i ≠ j → DiscrepAt G δ (G.edgeDensity (V i) (V j)) (V i) (V j)) :
    ∑ e ∈ rootEdges G V,
        (((fiber (transversal G V patK4) rootEdge e).card : ℚ) - rootProd G V * (t : ℚ) ^ 2) ^ 2
      ≤ 23 * δ * (t : ℚ) ^ 6 := by
  classical
  set A : ℚ := rootProd G V * (t : ℚ) ^ 2 with hA
  have hcardE : ((rootEdges G V).card : ℚ) = G.edgeDensity (V 0) (V 1) * (t : ℚ) ^ 2 :=
    card_rootEdges_eq hcard (hdisj 0 1 (by decide))
  have h₁ : |((transversal G V patK4).card : ℚ) - A * ((rootEdges G V).card : ℚ)|
      ≤ 6 * δ * (t : ℚ) ^ 4 := by
    have h := count_transversal_K4 hδ hcard hdisc
    rw [hcardE, hA]
    have hEq : rootProd G V * (t : ℚ) ^ 2 * (G.edgeDensity (V 0) (V 1) * (t : ℚ) ^ 2)
        = G.edgeDensity (V 0) (V 1) * rootProd G V * (t : ℚ) ^ 4 := by ring
    rw [hEq]
    exact h
  have h₂ : |((((transversal G V patK4) ×ˢ (transversal G V patK4)).filter
        fun p => rootEdge p.1 = rootEdge p.2).card : ℚ) - A ^ 2 * ((rootEdges G V).card : ℚ)|
      ≤ 11 * δ * (t : ℚ) ^ 6 := by
    have h := count_rootPairs hδ hcard hdisc
    rw [card_rootPairs_eq (hdisj 0 1 (by decide)), hcardE, hA]
    have hEq : (rootProd G V * (t : ℚ) ^ 2) ^ 2 * (G.edgeDensity (V 0) (V 1) * (t : ℚ) ^ 2)
        = G.edgeDensity (V 0) (V 1) * rootProd G V ^ 2 * (t : ℚ) ^ 6 := by ring
    rw [hEq]
    exact h
  have hmain := PaperIV.RootedCountingBridge.second_moment_of_pattern_counts
    (transversal G V patK4) rootEdge (rootEdges G V) A (6 * δ * (t : ℚ) ^ 4)
    (11 * δ * (t : ℚ) ^ 6) (fun K hK => rootEdge_mem_rootEdges hK) h₁ h₂
  refine hmain.trans ?_
  have hAabs : |A| = A :=
    abs_of_nonneg (by rw [hA]; exact mul_nonneg (rootProd_nonneg V) (by positivity))
  have hAle : A ≤ (t : ℚ) ^ 2 := by
    rw [hA]
    have h1 : rootProd G V ≤ 1 := rootProd_le_one V
    nlinarith [sq_nonneg ((t : ℚ))]
  have ht0 : (0 : ℚ) ≤ (t : ℚ) ^ 4 := by positivity
  rw [hAabs]
  nlinarith [mul_nonneg hδ ht0, rootProd_nonneg (G := G) V]

/-! ## 4. Las raíces malas y la cota inferior del grado -/

/-- Las aristas raíz cuyo conteo enraizado queda por debajo del umbral `thr`. -/
def badRootEdges (G : SimpleGraph α) [DecidableRel G.Adj] (V : Fin 4 → Finset α) (thr : ℚ) :
    Finset (Sym2 α) :=
  (rootEdges G V).filter
    (fun e => ((fiber (transversal G V patK4) rootEdge e).card : ℚ) < thr)

omit [Fintype α] in
theorem badRootEdges_mono {V : Fin 4 → Finset α} {thr thr' : ℚ} (h : thr ≤ thr') :
    badRootEdges G V thr ⊆ badRootEdges G V thr' := by
  intro e he
  rw [badRootEdges, Finset.mem_filter] at he ⊢
  exact ⟨he.1, lt_of_lt_of_le he.2 h⟩

/-- **Chebyshev.**  El número de aristas raíz con conteo bajo está acotado por el segundo
momento dividido por el cuadrado de la desviación admitida.  El umbral `thr` se toma por debajo
de `(1−u)·p₀·t²`, con `p₀` una cota inferior uniforme del producto de las cinco densidades. -/
theorem card_badRootEdges_le {δ u p₀ thr : ℚ} (hδ : 0 ≤ δ) (hu : 0 < u) (hu1 : u ≤ 1)
    (hp₀ : 0 < p₀) {V : Fin 4 → Finset α} {t : ℕ}
    (hcard : ∀ i, (V i).card = t)
    (hdisj : ∀ i j : Fin 4, i ≠ j → Disjoint (V i) (V j))
    (hdisc : ∀ i j : Fin 4, i ≠ j → DiscrepAt G δ (G.edgeDensity (V i) (V j)) (V i) (V j))
    (ht : 0 < t) (hP : p₀ ≤ rootProd G V) (hthr : thr ≤ (1 - u) * (p₀ * (t : ℚ) ^ 2)) :
    ((badRootEdges G V thr).card : ℚ) ≤ 23 * δ * (t : ℚ) ^ 2 / (u * p₀) ^ 2 := by
  classical
  set A : ℚ := rootProd G V * (t : ℚ) ^ 2 with hA
  have htq : (0 : ℚ) < (t : ℚ) := by exact_mod_cast ht
  have hPpos : 0 < rootProd G V := lt_of_lt_of_le hp₀ hP
  have hApos : 0 < A := by rw [hA]; positivity
  have hthrA : thr ≤ (1 - u) * A := by
    refine hthr.trans ?_
    have h1 : (0 : ℚ) ≤ 1 - u := by linarith
    have : p₀ * (t : ℚ) ^ 2 ≤ A := by
      rw [hA]
      nlinarith [sq_nonneg ((t : ℚ))]
    exact mul_le_mul_of_nonneg_left this h1
  have hsub : badRootEdges G V thr
      ⊆ (rootEdges G V).filter (fun e =>
          u * A < |((fiber (transversal G V patK4) rootEdge e).card : ℚ) - A|) := by
    intro e he
    have he' := badRootEdges_mono (G := G) (V := V) hthrA he
    rw [badRootEdges, Finset.mem_filter] at he'
    refine Finset.mem_filter.2 ⟨he'.1, ?_⟩
    have hlt := he'.2
    have hgt : u * A < A - ((fiber (transversal G V patK4) rootEdge e).card : ℚ) := by nlinarith
    calc u * A < A - ((fiber (transversal G V patK4) rootEdge e).card : ℚ) := hgt
      _ ≤ |((fiber (transversal G V patK4) rootEdge e).card : ℚ) - A| := by
          rw [abs_sub_comm]
          exact le_abs_self _
  have hcheb := PaperIV.RootedCounting.card_bad_roots_le (rootEdges G V)
    (fun e => ((fiber (transversal G V patK4) rootEdge e).card : ℚ)) A u
    (23 * δ * (t : ℚ) ^ 6) hu hApos (second_moment_rooted hδ hcard hdisj hdisc)
  have hle : ((badRootEdges G V thr).card : ℚ)
      ≤ (((rootEdges G V).filter (fun e =>
          u * A < |((fiber (transversal G V patK4) rootEdge e).card : ℚ) - A|)).card : ℚ) := by
    exact_mod_cast Finset.card_le_card hsub
  have hstep : ((badRootEdges G V thr).card : ℚ) * (u * (p₀ * (t : ℚ) ^ 2)) ^ 2
      ≤ 23 * δ * (t : ℚ) ^ 6 := by
    refine le_trans ?_ hcheb
    have h1 : (u * (p₀ * (t : ℚ) ^ 2)) ^ 2 ≤ (u * A) ^ 2 := by
      have hle' : u * (p₀ * (t : ℚ) ^ 2) ≤ u * A := by
        refine mul_le_mul_of_nonneg_left ?_ hu.le
        rw [hA]
        nlinarith [sq_nonneg ((t : ℚ))]
      have h0 : (0 : ℚ) ≤ u * (p₀ * (t : ℚ) ^ 2) := by positivity
      nlinarith
    have h2 : (0 : ℚ) ≤ ((badRootEdges G V thr).card : ℚ) := by positivity
    calc ((badRootEdges G V thr).card : ℚ) * (u * (p₀ * (t : ℚ) ^ 2)) ^ 2
        ≤ ((badRootEdges G V thr).card : ℚ) * (u * A) ^ 2 := by nlinarith
      _ ≤ _ := mul_le_mul_of_nonneg_right hle (by positivity)
  have hden : (0 : ℚ) < (u * p₀) ^ 2 := by positivity
  rw [le_div_iff₀ hden]
  have hexp : (u * (p₀ * (t : ℚ) ^ 2)) ^ 2 = (u * p₀) ^ 2 * (t : ℚ) ^ 4 := by ring
  rw [hexp] at hstep
  nlinarith [hstep, pow_pos htq 4]

/-- **La cota inferior del grado, local.**  Fuera de las raíces malas, toda arista entre las
partes `V 0` y `V 1` está en al menos `thr` hiperaristas del pool. -/
theorem deg_ge_of_notMem_badRootEdges {thr : ℚ} {V : Fin 4 → Finset α}
    {H : Finset (Finset (Sym2 α))}
    (hdisj : ∀ i j : Fin 4, i ≠ j → Disjoint (V i) (V j))
    (hsub : k4CandidateSupports G V ⊆ H)
    {e : Sym2 α} (he : e ∈ rootEdges G V) (hbad : e ∉ badRootEdges G V thr) :
    thr ≤ (deg H e : ℚ) := by
  classical
  rw [badRootEdges, Finset.mem_filter, not_and, not_lt] at hbad
  have h1 := hbad he
  have h2 : ((fiber (transversal G V patK4) rootEdge e).card : ℚ) ≤ (deg H e : ℚ) := by
    exact_mod_cast fiber_card_le_deg hdisj hsub e
  linarith

end PaperIV.RootedK4Degree
