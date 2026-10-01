import PaperIV.RC01K3Pool
import PaperIV.RootedVariance
import PaperIV.NibbleHypotheses

/-!
# El conteo enraizado de **triángulos**: la pieza local

Gemelo de `PaperIV.RootedK4Degree` / `RootedK4Counting` con `3` aristas por candidato en vez
de `6`.

## Qué cambia frente a `K₄`

* la fibra de la raíz se inyecta igual en las hiperaristas del pool que contienen la arista
  (`fiber_card_le_deg3`), y la inyección es **más fácil**: `pairs` es inversa de `cliqueOf`
  sobre conjuntos de al menos dos vértices, así que no hace falta el lema de inyectividad de
  `pairs` sobre `4`-conjuntos;
* el segundo momento **ya estaba demostrado**: `PaperIV.RootedVariance.rooted_variance_K3`, con
  constante `11 = 5 + 2·3` (`5 = |doubledK3|`, `3 = |patK3|`).  Aquí sólo se transporta de la
  raíz *par ordenado* a la raíz *arista* `s(φ 0, φ 1)`;
* la escala esperada es `A = rootProd3 · t` —con **una** parte libre en vez de dos— y el
  producto de densidades que sobrevive es `p³` en el sentido de que sólo quedan **dos**
  densidades fuera de la raíz, luego el umbral natural es `d₀² · t`.

La conclusión, `deg_ge_of_notMem_badRootEdges3`, tiene exactamente la forma que consume el
calendario.
-/

namespace PaperIV.RootedK3Degree

open Finset
open PaperIV.OneStepEstimate
open PaperIV.PatternCounting PaperIV.RegularityFormat PaperIV.RC01Candidates
open PaperIV.RC01K3Pool
open PaperIV.FarRounding
open PaperIV.NibbleHypotheses (deg)
open PaperIV.RootedCountingBridge (fiber)

variable {α : Type*} [Fintype α] [DecidableEq α]
variable {G : SimpleGraph α} [DecidableRel G.Adj]

/-! ## 1. El triángulo transversal, visto desde su arista raíz -/

/-- Caracterización cómoda: una copia transversal de `K₃` realiza **todas** las parejas. -/
theorem mem_transversal_K3 {V : Fin 3 → Finset α} {φ : Fin 3 → α} :
    φ ∈ transversal G V patK3 ↔
      (∀ i, φ i ∈ V i) ∧ ∀ i j : Fin 3, i ≠ j → G.Adj (φ i) (φ j) := by
  constructor
  · intro h
    exact ⟨(mem_transversal.1 h).1, fun i j hij => adj_of_transversal_K3 h hij⟩
  · intro h
    exact mem_transversal.2 ⟨h.1, fun e he => h.2 e.1 e.2 (patK3_ne e he)⟩

/-- La arista raíz de un triángulo transversal: la que une las partes `0` y `1`. -/
def rootEdge3 (φ : Fin 3 → α) : Sym2 α := s(φ 0, φ 1)

/-- Las aristas físicas entre las partes `V 0` y `V 1`. -/
def rootEdges3 (G : SimpleGraph α) [DecidableRel G.Adj] (V : Fin 3 → Finset α) :
    Finset (Sym2 α) :=
  (G.interedges (V 0) (V 1)).image (fun p => s(p.1, p.2))

omit [Fintype α] [DecidableEq α] in
/-- Sobre las parejas entre dos partes disjuntas, olvidar el orden es inyectivo. -/
theorem sym2_injOn_interedges {V : Fin 3 → Finset α} (hdisj : Disjoint (V 0) (V 1)) :
    ∀ p ∈ G.interedges (V 0) (V 1), ∀ q ∈ G.interedges (V 0) (V 1),
      s(p.1, p.2) = s(q.1, q.2) → p = q := by
  intro p hp q hq hpq
  rw [SimpleGraph.mem_interedges_iff] at hp hq
  rw [Sym2.eq_iff] at hpq
  rcases hpq with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Prod.ext h1 h2
  · exact absurd (Finset.disjoint_left.1 hdisj hp.1) (by rw [h1]; exact fun h => h hq.2.1)

omit [Fintype α] in
theorem card_rootEdges3 {V : Fin 3 → Finset α} (hdisj : Disjoint (V 0) (V 1)) :
    (rootEdges3 G V).card = (G.interedges (V 0) (V 1)).card :=
  Finset.card_image_of_injOn (fun p hp q hq h =>
    sym2_injOn_interedges hdisj p (Finset.mem_coe.1 hp) q (Finset.mem_coe.1 hq) h)

theorem rootEdge3_mem_rootEdges3 {V : Fin 3 → Finset α} {φ : Fin 3 → α}
    (hφ : φ ∈ transversal G V patK3) : rootEdge3 φ ∈ rootEdges3 G V := by
  obtain ⟨hmem, hadj⟩ := mem_transversal_K3.1 hφ
  refine Finset.mem_image.2 ⟨(φ 0, φ 1), ?_, rfl⟩
  exact (SimpleGraph.mem_interedges_iff (G := G)).2 ⟨hmem 0, hmem 1, hadj 0 1 (by decide)⟩

/-! ## 2. Enraizar es más restrictivo que contener -/

/-- **El puente con `deg`.**  La fibra de la raíz `e` se inyecta en las hiperaristas del pool
que contienen `e`. -/
theorem fiber_card_le_deg3 {V : Fin 3 → Finset α} {H : Finset (Finset (Sym2 α))}
    (hdisj : ∀ i j : Fin 3, i ≠ j → Disjoint (V i) (V j))
    (hsub : k3CandidateSupports G V ⊆ H) (e : Sym2 α) :
    (fiber (transversal G V patK3) rootEdge3 e).card ≤ deg H e := by
  classical
  rw [deg]
  refine Finset.card_le_card_of_injOn (fun φ => pairs (piece φ)) ?_ ?_
  · intro φ hφ
    rw [Finset.mem_coe, fiber, Finset.mem_filter] at hφ
    obtain ⟨hmem, -⟩ := mem_transversal_K3.1 hφ.1
    refine Finset.mem_filter.2 ⟨hsub (Finset.mem_image.2 ⟨piece φ, ?_, rfl⟩), ?_⟩
    · exact mem_candidates.2 ⟨φ, hφ.1, rfl⟩
    · rw [← hφ.2, rootEdge3]
      refine mk_mem_pairs.2 ⟨apply_mem_piece φ 0, apply_mem_piece φ 1, ?_⟩
      intro h01
      exact (hdisj 0 1 (by decide)).forall_ne_finset (hmem 0) (hmem 1) h01
  · intro φ hφ ψ hψ hpairs
    rw [Finset.mem_coe, fiber, Finset.mem_filter] at hφ hψ
    have hφcard : (piece φ).card = 3 := by
      rw [card_piece hdisj (mem_transversal_K3.1 hφ.1).1]; decide
    have hψcard : (piece ψ).card = 3 := by
      rw [card_piece hdisj (mem_transversal_K3.1 hψ.1).1]; decide
    have hpiece : piece φ = piece ψ :=
      calc piece φ = PaperIV.NibblePort.cliqueOf (pairs (piece φ)) :=
            (PaperIV.NibblePort.cliqueOf_pairs (K := piece φ) (by omega)).symm
        _ = PaperIV.NibblePort.cliqueOf (pairs (piece ψ)) := by
            rw [show pairs (piece φ) = pairs (piece ψ) from hpairs]
        _ = piece ψ := PaperIV.NibblePort.cliqueOf_pairs (K := piece ψ) (by omega)
    exact piece_injOn hdisj patK3 (Finset.mem_coe.2 hφ.1) (Finset.mem_coe.2 hψ.1) hpiece

/-! ## 3. El segundo momento, transportado a la raíz `Sym2` -/

/-- El producto de las **dos** densidades que no son la de la pareja raíz. -/
def rootProd3 (G : SimpleGraph α) [DecidableRel G.Adj] (V : Fin 3 → Finset α) : ℚ :=
  G.edgeDensity (V 0) (V 2) * G.edgeDensity (V 1) (V 2)

omit [Fintype α] [DecidableEq α] in
theorem rootProd3_nonneg (V : Fin 3 → Finset α) : 0 ≤ rootProd3 G V :=
  mul_nonneg (G.edgeDensity_nonneg _ _) (G.edgeDensity_nonneg _ _)

omit [Fintype α] [DecidableEq α] in
theorem rootProd3_le_one (V : Fin 3 → Finset α) : rootProd3 G V ≤ 1 := by
  have h1 : G.edgeDensity (V 0) (V 2) ≤ 1 := G.edgeDensity_le_one _ _
  have h2 : G.edgeDensity (V 1) (V 2) ≤ 1 := G.edgeDensity_le_one _ _
  have h0 : 0 ≤ G.edgeDensity (V 1) (V 2) := G.edgeDensity_nonneg _ _
  calc G.edgeDensity (V 0) (V 2) * G.edgeDensity (V 1) (V 2)
      ≤ 1 * G.edgeDensity (V 1) (V 2) := mul_le_mul_of_nonneg_right h1 h0
    _ = G.edgeDensity (V 1) (V 2) := one_mul _
    _ ≤ 1 := h2

/-- La fibra sobre la arista `s(x, y)` es la fibra sobre la pareja ordenada `(x, y)`. -/
theorem fiber_card_eq_of_mem_interedges {V : Fin 3 → Finset α}
    (hdisj : Disjoint (V 0) (V 1)) {p : α × α} (hp : p ∈ G.interedges (V 0) (V 1)) :
    (fiber (transversal G V patK3) rootEdge3 s(p.1, p.2)).card
      = (fiber (PaperIV.RootedVariance.copies G V patK3) (fun φ => (φ 0, φ 1)) p).card := by
  classical
  refine congrArg Finset.card (Finset.ext fun φ => ?_)
  rw [SimpleGraph.mem_interedges_iff] at hp
  simp only [fiber, Finset.mem_filter]
  constructor
  · rintro ⟨hmem, hroot⟩
    obtain ⟨hV, -⟩ := mem_transversal_K3.1 hmem
    refine ⟨hmem, ?_⟩
    rw [rootEdge3, Sym2.eq_iff] at hroot
    rcases hroot with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
    · exact absurd (h1 ▸ hV 0) (Finset.disjoint_right.1 hdisj hp.2.1)
  · rintro ⟨hmem, hroot⟩
    refine ⟨hmem, ?_⟩
    have h1 : φ 0 = p.1 := congrArg Prod.fst hroot
    have h2 : φ 1 = p.2 := congrArg Prod.snd hroot
    rw [rootEdge3, h1, h2]

/-- **La cota de segundo momento.**  Con `A = rootProd3 · t` la desviación cuadrática total del
conteo enraizado no pasa de `11·δ·t⁴`.  Es `RootedVariance.rooted_variance_K3` con la raíz
transportada de `α × α` a `Sym2 α`. -/
theorem second_moment_rooted3 {δ : ℚ} (hδ : 0 ≤ δ) {V : Fin 3 → Finset α} {t : ℕ}
    (hcard : ∀ i, (V i).card = t)
    (hdisj : ∀ i j : Fin 3, i ≠ j → Disjoint (V i) (V j))
    (hdisc : ∀ i j : Fin 3, i ≠ j → DiscrepAt G δ (G.edgeDensity (V i) (V j)) (V i) (V j)) :
    ∑ e ∈ rootEdges3 G V,
        (((fiber (transversal G V patK3) rootEdge3 e).card : ℚ) - rootProd3 G V * (t : ℚ)) ^ 2
      ≤ 11 * δ * (t : ℚ) ^ 4 := by
  classical
  have hvar := PaperIV.RootedVariance.rooted_variance_K3 (G := G) hδ V
    (hdisc 0 1 (by decide)) (hdisc 0 2 (by decide)) (hdisc 1 2 (by decide))
  have hsum : ∑ e ∈ rootEdges3 G V,
        (((fiber (transversal G V patK3) rootEdge3 e).card : ℚ)
          - rootProd3 G V * (t : ℚ)) ^ 2
      = ∑ p ∈ G.interedges (V 0) (V 1),
        (((fiber (PaperIV.RootedVariance.copies G V patK3)
              (fun φ => (φ 0, φ 1)) p).card : ℚ)
          - G.edgeDensity (V 0) (V 2) * G.edgeDensity (V 1) (V 2) * ((V 2).card : ℚ)) ^ 2 := by
    rw [rootEdges3, Finset.sum_image (sym2_injOn_interedges (hdisj 0 1 (by decide)))]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [fiber_card_eq_of_mem_interedges (hdisj 0 1 (by decide)) hp, rootProd3, hcard 2]
  rw [hsum]
  refine hvar.trans (le_of_eq ?_)
  rw [hcard 0, hcard 1, hcard 2]
  ring

/-! ## 4. Las raíces malas y la cota inferior del grado -/

/-- Las aristas raíz cuyo conteo enraizado queda por debajo del umbral `thr`. -/
def badRootEdges3 (G : SimpleGraph α) [DecidableRel G.Adj] (V : Fin 3 → Finset α) (thr : ℚ) :
    Finset (Sym2 α) :=
  (rootEdges3 G V).filter
    (fun e => ((fiber (transversal G V patK3) rootEdge3 e).card : ℚ) < thr)

omit [Fintype α] in
theorem badRootEdges3_mono {V : Fin 3 → Finset α} {thr thr' : ℚ} (h : thr ≤ thr') :
    badRootEdges3 G V thr ⊆ badRootEdges3 G V thr' := by
  intro e he
  rw [badRootEdges3, Finset.mem_filter] at he ⊢
  exact ⟨he.1, lt_of_lt_of_le he.2 h⟩

/-- **Chebyshev.**  El número de aristas raíz con conteo bajo está acotado por el segundo
momento dividido por el cuadrado de la desviación admitida. -/
theorem card_badRootEdges3_le {δ u p₀ thr : ℚ} (hδ : 0 ≤ δ) (hu : 0 < u) (hu1 : u ≤ 1)
    (hp₀ : 0 < p₀) {V : Fin 3 → Finset α} {t : ℕ}
    (hcard : ∀ i, (V i).card = t)
    (hdisj : ∀ i j : Fin 3, i ≠ j → Disjoint (V i) (V j))
    (hdisc : ∀ i j : Fin 3, i ≠ j → DiscrepAt G δ (G.edgeDensity (V i) (V j)) (V i) (V j))
    (ht : 0 < t) (hP : p₀ ≤ rootProd3 G V) (hthr : thr ≤ (1 - u) * (p₀ * (t : ℚ))) :
    ((badRootEdges3 G V thr).card : ℚ) ≤ 11 * δ * (t : ℚ) ^ 2 / (u * p₀) ^ 2 := by
  classical
  set A : ℚ := rootProd3 G V * (t : ℚ) with hA
  have htq : (0 : ℚ) < (t : ℚ) := by exact_mod_cast ht
  have hPpos : 0 < rootProd3 G V := lt_of_lt_of_le hp₀ hP
  have hApos : 0 < A := by rw [hA]; positivity
  have hthrA : thr ≤ (1 - u) * A := by
    refine hthr.trans ?_
    have h1 : (0 : ℚ) ≤ 1 - u := by linarith
    exact mul_le_mul_of_nonneg_left (by rw [hA]; nlinarith) h1
  have hsub : badRootEdges3 G V thr
      ⊆ (rootEdges3 G V).filter (fun e =>
          u * A < |((fiber (transversal G V patK3) rootEdge3 e).card : ℚ) - A|) := by
    intro e he
    have he' := badRootEdges3_mono (G := G) (V := V) hthrA he
    rw [badRootEdges3, Finset.mem_filter] at he'
    refine Finset.mem_filter.2 ⟨he'.1, ?_⟩
    have hgt : u * A < A - ((fiber (transversal G V patK3) rootEdge3 e).card : ℚ) := by
      nlinarith [he'.2]
    calc u * A < A - ((fiber (transversal G V patK3) rootEdge3 e).card : ℚ) := hgt
      _ ≤ |((fiber (transversal G V patK3) rootEdge3 e).card : ℚ) - A| := by
          rw [abs_sub_comm]; exact le_abs_self _
  have hcheb := PaperIV.RootedCounting.card_bad_roots_le (rootEdges3 G V)
    (fun e => ((fiber (transversal G V patK3) rootEdge3 e).card : ℚ)) A u
    (11 * δ * (t : ℚ) ^ 4) hu hApos (second_moment_rooted3 hδ hcard hdisj hdisc)
  have hle : ((badRootEdges3 G V thr).card : ℚ)
      ≤ (((rootEdges3 G V).filter (fun e =>
          u * A < |((fiber (transversal G V patK3) rootEdge3 e).card : ℚ) - A|)).card : ℚ) := by
    exact_mod_cast Finset.card_le_card hsub
  have hstep : ((badRootEdges3 G V thr).card : ℚ) * (u * (p₀ * (t : ℚ))) ^ 2
      ≤ 11 * δ * (t : ℚ) ^ 4 := by
    refine le_trans ?_ hcheb
    have hle' : u * (p₀ * (t : ℚ)) ≤ u * A :=
      mul_le_mul_of_nonneg_left (by rw [hA]; nlinarith) hu.le
    have h0 : (0 : ℚ) ≤ u * (p₀ * (t : ℚ)) := by positivity
    have h1 : (u * (p₀ * (t : ℚ))) ^ 2 ≤ (u * A) ^ 2 := by nlinarith
    have h2 : (0 : ℚ) ≤ ((badRootEdges3 G V thr).card : ℚ) := by positivity
    calc ((badRootEdges3 G V thr).card : ℚ) * (u * (p₀ * (t : ℚ))) ^ 2
        ≤ ((badRootEdges3 G V thr).card : ℚ) * (u * A) ^ 2 := by nlinarith
      _ ≤ _ := mul_le_mul_of_nonneg_right hle (by positivity)
  have hden : (0 : ℚ) < (u * p₀) ^ 2 := by positivity
  rw [le_div_iff₀ hden]
  have hexp : (u * (p₀ * (t : ℚ))) ^ 2 = (u * p₀) ^ 2 * (t : ℚ) ^ 2 := by ring
  rw [hexp] at hstep
  nlinarith [hstep, pow_pos htq 2]

/-- **La cota inferior del grado, local.**  Fuera de las raíces malas, toda arista entre las
partes `V 0` y `V 1` está en al menos `thr` hiperaristas del pool. -/
theorem deg_ge_of_notMem_badRootEdges3 {thr : ℚ} {V : Fin 3 → Finset α}
    {H : Finset (Finset (Sym2 α))}
    (hdisj : ∀ i j : Fin 3, i ≠ j → Disjoint (V i) (V j))
    (hsub : k3CandidateSupports G V ⊆ H)
    {e : Sym2 α} (he : e ∈ rootEdges3 G V) (hbad : e ∉ badRootEdges3 G V thr) :
    thr ≤ (deg H e : ℚ) := by
  classical
  rw [badRootEdges3, Finset.mem_filter, not_and, not_lt] at hbad
  have h1 := hbad he
  have h2 : ((fiber (transversal G V patK3) rootEdge3 e).card : ℚ) ≤ (deg H e : ℚ) := by
    exact_mod_cast fiber_card_le_deg3 hdisj hsub e
  linarith

end PaperIV.RootedK3Degree
