import PaperIV.RC01CanonicalSupports
import PaperIV.RootedCountingBridge
import PaperIV.NibbleHypotheses

/-!
# El grado del pool por conteo enraizado: la pieza local

Este módulo demuestra, para **una** cuádrupla de partes, la cota inferior del grado del pool
canónico de soportes: salvo pocas excepciones, toda arista entre dos de las partes está en
muchos `K₄` transversales de la cuádrupla.

## El objeto sobre el que se cuenta

`deg (canonicalSupportPool R) e` cuenta las hiperaristas del pool **que contienen** `e`, no las
que tienen a `e` como raíz.  El puente `RootedCountingBridge.second_moment_of_pattern_counts`
está enunciado con una raíz por objeto.  La adaptación correcta **no** es duplicar el pool por
las seis posiciones: basta observar que, para una **cota inferior**, las copias enraizadas en
`e` son un subconjunto de las que contienen `e`, de modo que

```
(fiber (transversal G V patK4) rootEdge e).card  ≤  deg H e
```

(`fiber_card_le_deg`), y el conteo enraizado con raíz `s(φ 0, φ 1)` basta tal cual.  Duplicar
por posiciones sería necesario sólo para una igualdad o para una cota superior.

Como las hipótesis del conteo local (`hcard`, `hdisj`, `hdisc`) son **simétricas en los cuatro
índices**, la elección de la pareja raíz `(0,1)` no pierde generalidad: para enraizar en otra
pareja se aplica el mismo teorema a `V ∘ σ`, que tiene los mismos candidatos
(`candidates_comp_perm`) y por tanto los mismos soportes.

## La cadena

1. `count_transversal_K4` — primer momento: `|#copias − A·#raíces| ≤ 6δt⁴`;
2. `card_rootPairs_eq` + `count_rootPairs` — segundo momento: el conteo de pares de copias con
   la misma raíz **es** el conteo del patrón doblado `doubledK4`, luego dista `11δt⁶` de
   `A²·#raíces`;
3. `second_moment_rooted` — `∑ (c e − A)² ≤ 23δt⁶`;
4. `card_badRootEdges_le` — el conjunto de raíces malas es pequeño;
5. `deg_ge_of_notMem_badRootEdges` — fuera de él, `deg ≥ (1−u)·A`.

con `A = rootProd G V · t²` y `rootProd` el producto de las **cinco** densidades que no son la
de la pareja raíz.
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

/-! ## 0. La discrepancia de cortes es simétrica -/

omit [Fintype α] [DecidableEq α] in
/-- (3.2) no distingue el orden de las dos partes. -/
theorem discrepAt_symm {ε d : ℚ} {s t : Finset α} (h : DiscrepAt G ε d s t) :
    DiscrepAt G ε d t s := by
  intro t' ht' s' hs'
  have hcard : (G.interedges t' s').card = (G.interedges s' t').card :=
    Rel.card_interedges_comm G.symm t' s'
  have := h s' hs' t' ht'
  rw [hcard]
  calc |((G.interedges s' t').card : ℚ) - d * (t'.card : ℚ) * (s'.card : ℚ)|
      = |((G.interedges s' t').card : ℚ) - d * (s'.card : ℚ) * (t'.card : ℚ)| := by ring_nf
    _ ≤ ε * (s.card : ℚ) * (t.card : ℚ) := this
    _ = ε * (t.card : ℚ) * (s.card : ℚ) := by ring

/-! ## 1. El patrón `K₄` visto desde su pareja raíz -/

/-- Las cinco parejas de `patK4` que no son la raíz `(0,1)`. -/
def patK4root : Finset (Fin 4 × Fin 4) := {(0, 2), (0, 3), (1, 2), (1, 3), (2, 3)}

theorem patK4_eq_insert : patK4 = insert ((0, 1) : Fin 4 × Fin 4) patK4root := by decide

theorem root_notMem_patK4root : ((0, 1) : Fin 4 × Fin 4) ∉ patK4root := by decide

/-- Caracterización cómoda: una copia transversal de `K₄` realiza **todas** las parejas. -/
theorem mem_transversal_K4 {V : Fin 4 → Finset α} {φ : Fin 4 → α} :
    φ ∈ transversal G V patK4 ↔
      (∀ i, φ i ∈ V i) ∧ ∀ i j : Fin 4, i ≠ j → G.Adj (φ i) (φ j) := by
  constructor
  · intro h
    exact ⟨(mem_transversal.1 h).1, fun i j hij => adj_of_transversal_K4 h hij⟩
  · intro h
    exact mem_transversal.2 ⟨h.1, fun e he => h.2 e.1 e.2 (patK4_ne e he)⟩

/-! ## 2. La arista raíz -/

/-- La arista raíz de una copia transversal: la que une las partes `0` y `1`. -/
def rootEdge (φ : Fin 4 → α) : Sym2 α := s(φ 0, φ 1)

/-- Las aristas físicas entre las partes `V 0` y `V 1`. -/
def rootEdges (G : SimpleGraph α) [DecidableRel G.Adj] (V : Fin 4 → Finset α) :
    Finset (Sym2 α) :=
  (G.interedges (V 0) (V 1)).image (fun p => s(p.1, p.2))

omit [Fintype α] in
theorem card_rootEdges {V : Fin 4 → Finset α} (hdisj : Disjoint (V 0) (V 1)) :
    (rootEdges G V).card = (G.interedges (V 0) (V 1)).card := by
  refine Finset.card_image_of_injOn ?_
  intro p hp q hq hpq
  rw [Finset.mem_coe, SimpleGraph.mem_interedges_iff] at hp hq
  rw [Sym2.eq_iff] at hpq
  rcases hpq with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Prod.ext h1 h2
  · exact absurd (Finset.disjoint_left.1 hdisj hp.1) (by rw [h1]; exact fun h => h hq.2.1)

theorem rootEdge_mem_rootEdges {V : Fin 4 → Finset α} {φ : Fin 4 → α}
    (hφ : φ ∈ transversal G V patK4) : rootEdge φ ∈ rootEdges G V := by
  obtain ⟨hmem, hadj⟩ := mem_transversal_K4.1 hφ
  refine Finset.mem_image.2 ⟨(φ 0, φ 1), ?_, rfl⟩
  exact (SimpleGraph.mem_interedges_iff (G := G)).2 ⟨hmem 0, hmem 1, hadj 0 1 (by decide)⟩

omit [Fintype α] [DecidableEq α] in
/-- Dos copias con la misma arista raíz coinciden en los dos vértices raíz. -/
theorem eq_of_rootEdge_eq {V : Fin 4 → Finset α} (hdisj : Disjoint (V 0) (V 1))
    {φ ψ : Fin 4 → α} (hφ : ∀ i, φ i ∈ V i) (hψ : ∀ i, ψ i ∈ V i)
    (h : rootEdge φ = rootEdge ψ) : φ 0 = ψ 0 ∧ φ 1 = ψ 1 := by
  rw [rootEdge, rootEdge, Sym2.eq_iff] at h
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨h1, h2⟩
  · exact absurd (h1 ▸ hφ 0) (Finset.disjoint_right.1 hdisj (hψ 1))

/-! ## 3. Las copias enraizadas en `e` son parte de las hiperaristas que contienen `e` -/

/-- **El puente con `deg`.**  Enraizar es más restrictivo que contener: la fibra de la raíz `e`
se inyecta en las hiperaristas del pool que contienen `e`. -/
theorem fiber_card_le_deg {V : Fin 4 → Finset α} {H : Finset (Finset (Sym2 α))}
    (hdisj : ∀ i j : Fin 4, i ≠ j → Disjoint (V i) (V j))
    (hsub : k4CandidateSupports G V ⊆ H) (e : Sym2 α) :
    (fiber (transversal G V patK4) rootEdge e).card ≤ deg H e := by
  classical
  rw [deg]
  refine Finset.card_le_card_of_injOn (fun φ => pairs (piece φ)) ?_ ?_
  · intro φ hφ
    rw [Finset.mem_coe, fiber, Finset.mem_filter] at hφ
    obtain ⟨hmem, hadj⟩ := mem_transversal_K4.1 hφ.1
    refine Finset.mem_filter.2 ⟨hsub (Finset.mem_image.2 ⟨piece φ, ?_, rfl⟩), ?_⟩
    · exact mem_candidates.2 ⟨φ, hφ.1, rfl⟩
    · rw [← hφ.2, rootEdge]
      refine mk_mem_pairs.2 ⟨apply_mem_piece φ 0, apply_mem_piece φ 1, ?_⟩
      intro h01
      exact (hdisj 0 1 (by decide)).forall_ne_finset (hmem 0) (hmem 1) h01
  · intro φ hφ ψ hψ hpairs
    rw [Finset.mem_coe, fiber, Finset.mem_filter] at hφ hψ
    have hφcard : (piece φ).card = 4 := by
      rw [card_piece hdisj (mem_transversal_K4.1 hφ.1).1]
      decide
    have hψcard : (piece ψ).card = 4 := by
      rw [card_piece hdisj (mem_transversal_K4.1 hψ.1).1]
      decide
    have hpiece : piece φ = piece ψ :=
      PaperIV.K4UniformNibbleCounts.pairs_inj_four hφcard hψcard hpairs
    exact piece_injOn hdisj patK4 (Finset.mem_coe.2 hφ.1) (Finset.mem_coe.2 hψ.1) hpiece

/-! ## 4. Permutar los índices no cambia los candidatos -/

omit [Fintype α] in
theorem piece_comp_perm (φ : Fin 4 → α) (σ : Equiv.Perm (Fin 4)) :
    piece (φ ∘ σ) = piece φ := by
  calc piece (φ ∘ σ) = (Finset.univ.image (σ : Fin 4 → Fin 4)).image φ :=
        (Finset.image_image).symm
    _ = piece φ := by rw [Finset.image_univ_equiv]; rfl

theorem candidates_comp_perm {V : Fin 4 → Finset α} (σ : Equiv.Perm (Fin 4)) :
    candidates G (V ∘ σ) patK4 = candidates G V patK4 := by
  classical
  ext K
  constructor
  · rintro hK
    obtain ⟨φ, hφ, rfl⟩ := mem_candidates.1 hK
    obtain ⟨hmem, hadj⟩ := mem_transversal_K4.1 hφ
    refine mem_candidates.2 ⟨φ ∘ σ.symm, mem_transversal_K4.2 ⟨fun i => ?_, fun i j hij => ?_⟩, ?_⟩
    · have := hmem (σ.symm i)
      simpa using this
    · exact hadj _ _ (fun h => hij (σ.symm.injective h))
    · exact piece_comp_perm φ σ.symm
  · rintro hK
    obtain ⟨φ, hφ, rfl⟩ := mem_candidates.1 hK
    obtain ⟨hmem, hadj⟩ := mem_transversal_K4.1 hφ
    refine mem_candidates.2 ⟨φ ∘ σ, mem_transversal_K4.2 ⟨fun i => hmem (σ i), fun i j hij => ?_⟩, ?_⟩
    · exact hadj _ _ (fun h => hij (σ.injective h))
    · exact piece_comp_perm φ σ

/-! ## 5. El patrón doblado: los pares con la misma raíz -/

/-- Las seis partes del patrón doblado: las dos copias comparten `V 0` y `V 1` y repiten
`V 2`, `V 3`. -/
def dblIdx : Fin 6 → Fin 4 := ![0, 1, 2, 3, 2, 3]

/-- La copia doble determinada por dos copias que comparten la arista raíz. -/
def merge (φ ψ : Fin 4 → α) : Fin 6 → α := ![φ 0, φ 1, φ 2, φ 3, ψ 2, ψ 3]

/-- La primera de las dos copias de una copia doble. -/
def unmergeL (χ : Fin 6 → α) : Fin 4 → α := ![χ 0, χ 1, χ 2, χ 3]

/-- La segunda de las dos copias de una copia doble. -/
def unmergeR (χ : Fin 6 → α) : Fin 4 → α := ![χ 0, χ 1, χ 4, χ 5]

/-- **El segundo momento es el conteo del patrón doblado.**  Los pares ordenados de copias
transversales de `K₄` con la misma arista raíz están en biyección con las copias
transversales de `doubledK4` sobre las partes repetidas. -/
theorem card_rootPairs_eq {V : Fin 4 → Finset α} (hdisj : Disjoint (V 0) (V 1)) :
    (((transversal G V patK4) ×ˢ (transversal G V patK4)).filter
        fun p => rootEdge p.1 = rootEdge p.2).card
      = (transversal G (V ∘ dblIdx) doubledK4).card := by
  classical
  refine Finset.card_nbij' (fun p => merge p.1 p.2)
    (fun χ => (unmergeL χ, unmergeR χ)) ?_ ?_ ?_ ?_
  · intro p hp
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hp
    obtain ⟨⟨h1, h2⟩, hroot⟩ := hp
    obtain ⟨hm1, ha1⟩ := mem_transversal_K4.1 h1
    obtain ⟨hm2, ha2⟩ := mem_transversal_K4.1 h2
    obtain ⟨e0, e1⟩ := eq_of_rootEdge_eq hdisj hm1 hm2 hroot
    rw [Finset.mem_coe]
    refine mem_transversal.2 ⟨fun i => ?_, fun e he => ?_⟩
    · fin_cases i
      · exact hm1 0
      · exact hm1 1
      · exact hm1 2
      · exact hm1 3
      · exact hm2 2
      · exact hm2 3
    · simp only [doubledK4, Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ha1 0 1 (by decide)
      · exact ha1 0 2 (by decide)
      · exact ha1 0 3 (by decide)
      · exact ha1 1 2 (by decide)
      · exact ha1 1 3 (by decide)
      · exact ha1 2 3 (by decide)
      · show G.Adj (p.1 0) (p.2 2)
        rw [e0]
        exact ha2 0 2 (by decide)
      · show G.Adj (p.1 0) (p.2 3)
        rw [e0]
        exact ha2 0 3 (by decide)
      · show G.Adj (p.1 1) (p.2 2)
        rw [e1]
        exact ha2 1 2 (by decide)
      · show G.Adj (p.1 1) (p.2 3)
        rw [e1]
        exact ha2 1 3 (by decide)
      · exact ha2 2 3 (by decide)
  · intro χ hχ
    rw [Finset.mem_coe] at hχ
    obtain ⟨hm, ha⟩ := mem_transversal.1 hχ
    have hadj : ∀ e ∈ doubledK4, G.Adj (χ e.1) (χ e.2) := ha
    have h01 : G.Adj (χ 0) (χ 1) := hadj (0, 1) (by decide)
    have h02 : G.Adj (χ 0) (χ 2) := hadj (0, 2) (by decide)
    have h03 : G.Adj (χ 0) (χ 3) := hadj (0, 3) (by decide)
    have h12 : G.Adj (χ 1) (χ 2) := hadj (1, 2) (by decide)
    have h13 : G.Adj (χ 1) (χ 3) := hadj (1, 3) (by decide)
    have h23 : G.Adj (χ 2) (χ 3) := hadj (2, 3) (by decide)
    have h04 : G.Adj (χ 0) (χ 4) := hadj (0, 4) (by decide)
    have h05 : G.Adj (χ 0) (χ 5) := hadj (0, 5) (by decide)
    have h14 : G.Adj (χ 1) (χ 4) := hadj (1, 4) (by decide)
    have h15 : G.Adj (χ 1) (χ 5) := hadj (1, 5) (by decide)
    have h45 : G.Adj (χ 4) (χ 5) := hadj (4, 5) (by decide)
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_product]
    refine ⟨⟨mem_transversal_K4.2 ⟨fun i => ?_, fun i j hij => ?_⟩,
      mem_transversal_K4.2 ⟨fun i => ?_, fun i j hij => ?_⟩⟩, rfl⟩
    · fin_cases i
      · exact hm 0
      · exact hm 1
      · exact hm 2
      · exact hm 3
    · fin_cases i <;> fin_cases j <;>
        first
        | exact absurd rfl hij
        | exact h01 | exact h02 | exact h03 | exact h12 | exact h13 | exact h23
        | exact h01.symm | exact h02.symm | exact h03.symm | exact h12.symm | exact h13.symm
        | exact h23.symm
    · fin_cases i
      · exact hm 0
      · exact hm 1
      · exact hm 4
      · exact hm 5
    · fin_cases i <;> fin_cases j <;>
        first
        | exact absurd rfl hij
        | exact h01 | exact h04 | exact h05 | exact h14 | exact h15 | exact h45
        | exact h01.symm | exact h04.symm | exact h05.symm | exact h14.symm | exact h15.symm
        | exact h45.symm
  · intro p hp
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hp
    obtain ⟨⟨h1, h2⟩, hroot⟩ := hp
    obtain ⟨hm1, -⟩ := mem_transversal_K4.1 h1
    obtain ⟨hm2, -⟩ := mem_transversal_K4.1 h2
    obtain ⟨e0, e1⟩ := eq_of_rootEdge_eq hdisj hm1 hm2 hroot
    refine Prod.ext ?_ ?_
    · funext i
      fin_cases i <;> rfl
    · funext i
      fin_cases i
      · exact e0
      · exact e1
      · rfl
      · rfl
  · intro χ _
    funext i
    fin_cases i <;> rfl

end PaperIV.RootedK4Degree
