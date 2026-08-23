/-
# Nibble — the block-allocation residual is false outside its fine parameter range

`Nibble.AX1.BlockCoverResidual` (`Nibble.CoreGapBlockCover`) is stated for every relative block size
`α ≤ δ / 2`.  This file shows, machine-checked, that the statement is **false** at the coarse end of
that range, and therefore that the parameter coupling recorded in
`Nibble.AX1.BlockCoverResidualFine` (`δ ≤ ε` and `α ≤ ε ^ 2`, both supplied by the AX1 reduction) is
not cosmetic.

The witness is completely explicit: `δ = 1`, `α = 1/2`, `ε₁ = 1`, `T₀ = 1`, `ε = 1/1000`, the
complete graph on `5N` vertices and the equipartition into five clusters of size `N`.

* every cluster pair has density `1`, so `δ = 1` still admits every cluster triple, and the
  regularity-reduced graph is the complete `5`-partite graph, whose fractional triangle packing
  number is at least `10N²/3` (`Nibble.AX1.nu3star_fivePartite_ge`);
* `α = 1/2` forces every block to occupy at least half of its cluster, so a block sub-triple carries
  three rectangles of area at least `(N/2)²` each, and two sub-triples living on the same cluster
  pair cannot both have their two sides larger than `N/2`
  (`Nibble.AX1.card_le_of_disjoint_big_rects`);
* hence at most `13` sub-triples fit in total, and the covering sum they produce is at most
  `13·(N/2 + 2)² < 10N²/3 − ε·(5N)²` (`Nibble.AX1.blockCover_family_bound`).

The obstruction is pure quantisation: `40/3` is not an integer, so the ten cluster pairs of five
clusters cannot be exactly tiled by the `3`-per-triple rectangles of a block design at relative size
`1/2`.  It disappears as soon as the blocks are small compared with their clusters, which is what
`Nibble.AX1.BlockCoverResidualFine` assumes.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.CoreGapBlockCover
import Nibble.LowDegreeQuadraticFrac
import Mathlib.Data.NNRat.Floor

open Finset SimpleGraph Hypergraph Nibble.YusterE

namespace Nibble.AX1

/-! ### A sharper general lower bound for `ν₃*` -/

variable {V : Type} [Fintype V] [DecidableEq V]

/-- If every vertex completing the set `e` to a triangle lies in `S`, then at most `#S` hyperedges
of the triangle hypergraph contain `e`. -/
theorem card_filter_triangleHypergraphE_le_of_subset (G : SimpleGraph V) [DecidableRel G.Adj]
    (e S : Finset V) (hS : ∀ v : V, v ∉ e → (∀ u ∈ e, G.Adj v u) → v ∈ S) :
    #((triangleHypergraphE G).filter (fun T => e ∈ T)) ≤ #S := by
  classical
  have hsub : (triangleHypergraphE G).filter (fun T => e ∈ T) ⊆
      S.image (fun v : V => (insert v e).powersetCard 2) := by
    intro T hT
    rw [Finset.mem_filter] at hT
    obtain ⟨hTH, heT⟩ := hT
    rw [triangleHypergraphE, Finset.mem_image] at hTH
    obtain ⟨t, ht, rfl⟩ := hTH
    rw [Finset.mem_powersetCard] at heT
    obtain ⟨hesub, hecard⟩ := heT
    have hclique := SimpleGraph.mem_cliqueFinset_iff.mp ht
    have htcard : t.card = 3 := hclique.card_eq
    have hadd := Finset.card_sdiff_add_card_eq_card hesub
    have hone : (t \ e).card = 1 := by omega
    obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hone
    have hvt : v ∈ t := by
      have : v ∈ t \ e := by rw [hv]; simp
      exact (Finset.mem_sdiff.mp this).1
    have hve : v ∉ e := by
      have : v ∈ t \ e := by rw [hv]; simp
      exact (Finset.mem_sdiff.mp this).2
    have hteq : t = insert v e := by
      have hu := Finset.sdiff_union_of_subset hesub
      rw [hv] at hu
      rw [← hu]
      ext x
      simp [Finset.mem_insert]
    have hadj : ∀ u ∈ e, G.Adj v u := by
      intro u hu
      exact hclique.1 hvt (hesub hu) (by rintro rfl; exact hve hu)
    exact Finset.mem_image.mpr ⟨v, hS v hve hadj, by rw [hteq]⟩
  calc #((triangleHypergraphE G).filter (fun T => e ∈ T))
      ≤ #(S.image (fun v : V => (insert v e).powersetCard 2)) := Finset.card_le_card hsub
    _ ≤ #S := Finset.card_image_le

/-- **A general lower bound on `ν₃*`.**  If every edge lies in at most `D` triangles then uniform
weight `1/D` on all triangles is a fractional packing, so `ν₃* ≥ #triangles / D`. -/
theorem card_triangles_div_le_nu3star (G : SimpleGraph V) [DecidableRel G.Adj] {D : ℝ} (hD : 0 < D)
    (hdeg : ∀ e : Finset V, (#((triangleHypergraphE G).filter (fun T => e ∈ T)) : ℝ) ≤ D) :
    ((G.cliqueFinset 3).card : ℝ) / D ≤ nu3star G := by
  classical
  set c : ℝ := 1 / D with hc
  set w : Finset (Finset V) → ℝ := fun T => if T ∈ triangleHypergraphE G then c else 0 with hw
  have hcpos : 0 < c := by positivity
  have hpack : IsFracPacking G w := by
    refine ⟨fun T => ?_, fun T hT => ?_, fun e => ?_⟩
    · simp only [hw]; split_ifs <;> [exact hcpos.le; exact le_rfl]
    · simp only [hw]; rw [if_neg hT]
    · have hsum : ∑ T ∈ (triangleHypergraphE G).filter (fun T => e ∈ T), w T
          = ((#((triangleHypergraphE G).filter (fun T => e ∈ T)) : ℝ)) * c := by
        rw [Finset.sum_congr rfl (fun T hT => ?_), Finset.sum_const, nsmul_eq_mul]
        simp only [hw]
        rw [if_pos (Finset.mem_filter.mp hT).1]
      rw [hsum, hc, mul_one_div, div_le_one hD]
      exact hdeg e
  have hval : ∑ T ∈ triangleHypergraphE G, w T = ((G.cliqueFinset 3).card : ℝ) / D := by
    have hsum : ∑ T ∈ triangleHypergraphE G, w T = ((triangleHypergraphE G).card : ℝ) * c := by
      rw [Finset.sum_congr rfl (fun T hT => ?_), Finset.sum_const, nsmul_eq_mul]
      simp only [hw]
      rw [if_pos hT]
    rw [hsum, triangleHypergraphE_card G, hc, mul_one_div]
  exact le_csSup (nu3star_bddAbove G) ⟨w, hpack, hval.symm⟩

/-! ### Five clusters of size `N` -/

/-- The `a`-th cluster of `Fin 5 × Fin N`. -/
def cpart (N : ℕ) (a : Fin 5) : Finset (Fin 5 × Fin N) :=
  ({a} : Finset (Fin 5)) ×ˢ (univ : Finset (Fin N))

theorem mem_cpart {N : ℕ} {a : Fin 5} {v : Fin 5 × Fin N} : v ∈ cpart N a ↔ v.1 = a := by
  cases v; simp [cpart, eq_comm]

theorem card_cpart (N : ℕ) (a : Fin 5) : #(cpart N a) = N := by simp [cpart]

/-- The five clusters. -/
def cparts (N : ℕ) : Finset (Finset (Fin 5 × Fin N)) := (univ : Finset (Fin 5)).image (cpart N)

theorem mem_cparts {N : ℕ} {s : Finset (Fin 5 × Fin N)} : s ∈ cparts N ↔ ∃ a, s = cpart N a := by
  simp [cparts, eq_comm]

/-- The equipartition of `Fin 5 × Fin N` into its five clusters. -/
def cpartition (N : ℕ) (hN : 0 < N) : Finpartition (univ : Finset (Fin 5 × Fin N)) where
  parts := cparts N
  supIndep := by
    rw [Finset.supIndep_iff_pairwiseDisjoint]
    intro s hs t ht hst
    simp only [Finset.mem_coe] at hs ht
    obtain ⟨a, rfl⟩ := mem_cparts.mp hs
    obtain ⟨b, rfl⟩ := mem_cparts.mp ht
    have hab : a ≠ b := by rintro rfl; exact hst rfl
    simp only [Finset.disjoint_left, id_eq]
    intro v hv hv'
    rw [mem_cpart] at hv hv'
    exact hab (hv ▸ hv')
  sup_parts := by
    ext v
    simp only [Finset.mem_sup, Finset.mem_univ, iff_true, id_eq]
    exact ⟨cpart N v.1, mem_cparts.mpr ⟨v.1, rfl⟩, mem_cpart.mpr rfl⟩
  bot_notMem := by
    intro h
    obtain ⟨a, ha⟩ := mem_cparts.mp h
    have hv : (⟨a, ⟨0, hN⟩⟩ : Fin 5 × Fin N) ∈ cpart N a := mem_cpart.mpr rfl
    rw [← ha] at hv
    simp at hv

theorem cpartition_parts (N : ℕ) (hN : 0 < N) : (cpartition N hN).parts = cparts N := rfl

theorem cpartition_parts_card (N : ℕ) (hN : 0 < N) : #(cpartition N hN).parts = 5 := by
  rw [cpartition_parts, cparts, Finset.card_image_of_injective _ ?_]
  · simp
  · intro a b hab
    have : (⟨a, ⟨0, hN⟩⟩ : Fin 5 × Fin N) ∈ cpart N b := hab ▸ mem_cpart.mpr rfl
    exact mem_cpart.mp this

theorem cpartition_isEquipartition (N : ℕ) (hN : 0 < N) : (cpartition N hN).IsEquipartition := by
  rw [Finpartition.IsEquipartition, Set.equitableOn_iff_exists_eq_eq_add_one]
  refine ⟨N, ?_⟩
  intro s hs
  obtain ⟨a, rfl⟩ := mem_cparts.mp hs
  exact Or.inl (card_cpart N a)

theorem card_univ_five (N : ℕ) : Fintype.card (Fin 5 × Fin N) = 5 * N := by simp

/-! ### The complete graph on the five clusters -/

omit [Fintype V] in
theorem top_interedges {A B : Finset V} (h : Disjoint A B) :
    (⊤ : SimpleGraph V).interedges A B = A ×ˢ B := by
  ext ⟨a, b⟩
  simp only [SimpleGraph.mem_interedges_iff, Finset.mem_product, top_adj]
  constructor
  · rintro ⟨ha, hb, -⟩; exact ⟨ha, hb⟩
  · rintro ⟨ha, hb⟩
    exact ⟨ha, hb, by rintro rfl; exact (Finset.disjoint_left.mp h ha) hb⟩

omit [Fintype V] in
theorem top_edgeDensity {A B : Finset V} (h : Disjoint A B) (hA : A.Nonempty) (hB : B.Nonempty) :
    (⊤ : SimpleGraph V).edgeDensity A B = 1 := by
  rw [SimpleGraph.edgeDensity, Rel.edgeDensity]
  rw [show (Rel.interedges (⊤ : SimpleGraph V).Adj A B) = A ×ˢ B from top_interedges h]
  rw [Finset.card_product]
  have h1 : (0:ℚ) < #A := by exact_mod_cast Finset.card_pos.mpr hA
  have h2 : (0:ℚ) < #B := by exact_mod_cast Finset.card_pos.mpr hB
  push_cast
  field_simp

omit [Fintype V] in
theorem top_isUniform {ep : ℝ} (hep : 0 < ep) {U W : Finset V} (h : Disjoint U W)
    (hU : U.Nonempty) (hW : W.Nonempty) : (⊤ : SimpleGraph V).IsUniform ep U W := by
  intro s' hs' t' ht' hs ht
  have hUc : (0:ℝ) < #U := by exact_mod_cast Finset.card_pos.mpr hU
  have hWc : (0:ℝ) < #W := by exact_mod_cast Finset.card_pos.mpr hW
  have hs0 : (0:ℝ) < #s' := lt_of_lt_of_le (by positivity) hs
  have ht0 : (0:ℝ) < #t' := lt_of_lt_of_le (by positivity) ht
  have hsne : s'.Nonempty := Finset.card_pos.mp (by exact_mod_cast hs0)
  have htne : t'.Nonempty := Finset.card_pos.mp (by exact_mod_cast ht0)
  rw [top_edgeDensity (h.mono hs' ht') hsne htne, top_edgeDensity h hU hW]
  simpa using hep

theorem cpart_nonempty {N : ℕ} (hN : 0 < N) (a : Fin 5) : (cpart N a).Nonempty :=
  ⟨⟨a, ⟨0, hN⟩⟩, mem_cpart.mpr rfl⟩

theorem cpart_disjoint {N : ℕ} {a b : Fin 5} (hab : a ≠ b) : Disjoint (cpart N a) (cpart N b) := by
  simp only [Finset.disjoint_left]
  intro v hv hv'
  rw [mem_cpart] at hv hv'
  exact hab (hv ▸ hv')

theorem cpartition_isUniform (N : ℕ) (hN : 0 < N) {ep : ℝ} (hep : 0 < ep) :
    (cpartition N hN).IsUniform (⊤ : SimpleGraph (Fin 5 × Fin N)) ep := by
  have hempty : (cpartition N hN).nonUniforms (⊤ : SimpleGraph (Fin 5 × Fin N)) ep = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    rintro ⟨u, w⟩ hx
    rw [Finpartition.nonUniforms, Finset.mem_filter, Finset.mem_offDiag] at hx
    obtain ⟨⟨hu, hw, huw⟩, hnu⟩ := hx
    rw [cpartition_parts] at hu hw
    obtain ⟨a, rfl⟩ := mem_cparts.mp hu
    obtain ⟨b, rfl⟩ := mem_cparts.mp hw
    have hab : a ≠ b := by rintro rfl; exact huw rfl
    exact hnu (top_isUniform hep (cpart_disjoint hab) (cpart_nonempty hN a) (cpart_nonempty hN b))
  rw [Finpartition.IsUniform, hempty]
  simp only [Finset.card_empty, Nat.cast_zero]
  positivity

/-- The regularity-reduced graph of the complete graph at the five clusters is the complete
`5`-partite graph. -/
theorem cred_adj (N : ℕ) (hN : 0 < N) {ep de : ℝ} (hep : 0 < ep) (hde : de ≤ 1)
    (x y : Fin 5 × Fin N) :
    ((⊤ : SimpleGraph (Fin 5 × Fin N)).regularityReduced (cpartition N hN) ep de).Adj x y
      ↔ x.1 ≠ y.1 := by
  constructor
  · rintro ⟨-, U, hU, W, hW, hxU, hyW, hUW, -, -⟩
    rw [cpartition_parts] at hU hW
    obtain ⟨a, rfl⟩ := mem_cparts.mp hU
    obtain ⟨b, rfl⟩ := mem_cparts.mp hW
    rw [mem_cpart] at hxU hyW
    intro hxy
    exact hUW (by rw [← hxU, ← hyW, hxy])
  · intro hxy
    refine ⟨?_, cpart N x.1, ?_, cpart N y.1, ?_, mem_cpart.mpr rfl, mem_cpart.mpr rfl, ?_, ?_, ?_⟩
    · simp only [top_adj]
      intro h; exact hxy (by rw [h])
    · rw [cpartition_parts]; exact mem_cparts.mpr ⟨_, rfl⟩
    · rw [cpartition_parts]; exact mem_cparts.mpr ⟨_, rfl⟩
    · intro h
      have : (⟨y.1, ⟨0, hN⟩⟩ : Fin 5 × Fin N) ∈ cpart N x.1 := h ▸ mem_cpart.mpr rfl
      exact hxy (mem_cpart.mp this).symm
    · exact top_isUniform hep (cpart_disjoint hxy) (cpart_nonempty hN _) (cpart_nonempty hN _)
    · rw [top_edgeDensity (cpart_disjoint hxy) (cpart_nonempty hN _) (cpart_nonempty hN _)]
      simpa using hde

/-! ### The fractional packing number of the five-partite blow-up -/

/-- Three vertices in three different clusters form a triangle of the reduced graph. -/
theorem cred_triple_clique (N : ℕ) (hN : 0 < N) {ep de : ℝ} (hep : 0 < ep) (hde : de ≤ 1)
    {a b c : Fin 5} (hab : a < b) (hbc : b < c) (i j k : Fin N) :
    ({(a, i), (b, j), (c, k)} : Finset (Fin 5 × Fin N)) ∈
      ((⊤ : SimpleGraph (Fin 5 × Fin N)).regularityReduced (cpartition N hN) ep de).cliqueFinset
        3 := by
  rw [SimpleGraph.mem_cliqueFinset_iff, SimpleGraph.is3Clique_triple_iff]
  refine ⟨?_, ?_, ?_⟩ <;> rw [cred_adj N hN hep hde] <;> simp <;> omega

theorem tri_triple_inj {N : ℕ} {a b c a' b' c' : Fin 5} {i j k i' j' k' : Fin N}
    (hab : a < b) (hbc : b < c) (hab' : a' < b') (hbc' : b' < c')
    (h : ({(a, i), (b, j), (c, k)} : Finset (Fin 5 × Fin N)) = {(a', i'), (b', j'), (c', k')}) :
    a = a' ∧ b = b' ∧ c = c' ∧ i = i' ∧ j = j' ∧ k = k' := by
  have hmem : ∀ p : Fin 5 × Fin N, p ∈ ({(a, i), (b, j), (c, k)} : Finset (Fin 5 × Fin N)) ↔
      p ∈ ({(a', i'), (b', j'), (c', k')} : Finset (Fin 5 × Fin N)) := by
    intro p; rw [h]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  have h1 := (hmem (a, i)).mp (by simp)
  have h2 := (hmem (a', i')).mpr (by simp)
  have h3 := (hmem (c, k)).mp (by simp)
  have h4 := (hmem (c', k')).mpr (by simp)
  have h5 := (hmem (b, j)).mp (by simp)
  simp only [Prod.mk.injEq] at h1 h2 h3 h4 h5
  have haa : a = a' := by
    rcases h1 with ⟨e, -⟩|⟨e, -⟩|⟨e, -⟩ <;> rcases h2 with ⟨e2, -⟩|⟨e2, -⟩|⟨e2, -⟩ <;> omega
  have hcc : c = c' := by
    rcases h3 with ⟨e, -⟩|⟨e, -⟩|⟨e, -⟩ <;> rcases h4 with ⟨e2, -⟩|⟨e2, -⟩|⟨e2, -⟩ <;> omega
  have hbb : b = b' := by
    rcases h5 with ⟨e, -⟩|⟨e, -⟩|⟨e, -⟩ <;> omega
  refine ⟨haa, hbb, hcc, ?_, ?_, ?_⟩
  · rcases h1 with ⟨-, e⟩|⟨e, -⟩|⟨e, -⟩
    · exact e
    · omega
    · omega
  · rcases h5 with ⟨e, -⟩|⟨-, e⟩|⟨e, -⟩
    · omega
    · exact e
    · omega
  · rcases h3 with ⟨e, -⟩|⟨e, -⟩|⟨-, e⟩
    · omega
    · omega
    · exact e

/-- The five-partite blow-up has at least `10N³` triangles. -/
theorem cred_card_cliques (N : ℕ) (hN : 0 < N) {ep de : ℝ} (hep : 0 < ep) (hde : de ≤ 1) :
    10 * (N * N * N) ≤
      #(((⊤ : SimpleGraph (Fin 5 × Fin N)).regularityReduced (cpartition N hN) ep
        de).cliqueFinset 3) := by
  classical
  set D : Finset ((Fin 5 × Fin 5 × Fin 5) × (Fin N × Fin N × Fin N)) :=
    ((univ : Finset (Fin 5 × Fin 5 × Fin 5)).filter (fun t => t.1 < t.2.1 ∧ t.2.1 < t.2.2)) ×ˢ
      (univ : Finset (Fin N × Fin N × Fin N)) with hD
  have hcard : #D = 10 * (N * N * N) := by
    rw [hD, Finset.card_product]
    have h1 : #((univ : Finset (Fin 5 × Fin 5 × Fin 5)).filter
        (fun t => t.1 < t.2.1 ∧ t.2.1 < t.2.2)) = 10 := by decide
    have h2 : #(univ : Finset (Fin N × Fin N × Fin N)) = N * N * N := by
      simp [Finset.card_univ, mul_assoc]
    rw [h1, h2]
  rw [← hcard]
  refine Finset.card_le_card_of_injOn
    (fun p => {(p.1.1, p.2.1), (p.1.2.1, p.2.2.1), (p.1.2.2, p.2.2.2)}) ?_ ?_
  · rintro ⟨⟨a, b, c⟩, ⟨i, j, k⟩⟩ hp
    simp only [hD, Finset.mem_coe, Finset.mem_product, Finset.mem_filter, Finset.mem_univ,
      true_and] at hp
    exact cred_triple_clique N hN hep hde hp.1.1 hp.1.2 i j k
  · rintro ⟨⟨a, b, c⟩, ⟨i, j, k⟩⟩ hp ⟨⟨a', b', c'⟩, ⟨i', j', k'⟩⟩ hp' heq
    simp only [hD, Finset.coe_product, Finset.mem_coe, Set.mem_prod,
      Finset.mem_univ, true_and, Finset.coe_filter, Set.mem_setOf_eq] at hp hp'
    obtain ⟨e1, e2, e3, e4, e5, e6⟩ :=
      tri_triple_inj hp.1.1 hp.1.2 hp'.1.1 hp'.1.2 heq
    simp only [Prod.mk.injEq]
    exact ⟨⟨e1, e2, e3⟩, e4, e5, e6⟩

/-- At most `3N` triangles of the five-partite blow-up contain a given edge. -/
theorem cred_edge_bound (N : ℕ) (hN : 0 < N) {ep de : ℝ} (hep : 0 < ep) (hde : de ≤ 1)
    (e : Finset (Fin 5 × Fin N)) :
    #((triangleHypergraphE
        ((⊤ : SimpleGraph (Fin 5 × Fin N)).regularityReduced (cpartition N hN) ep de)).filter
      (fun T => e ∈ T)) ≤ 3 * N := by
  classical
  set G' := (⊤ : SimpleGraph (Fin 5 × Fin N)).regularityReduced (cpartition N hN) ep de with hG'
  rcases Finset.eq_empty_or_nonempty ((triangleHypergraphE G').filter (fun T => e ∈ T)) with
    hemp | ⟨T, hT⟩
  · rw [hemp]; simp
  · rw [Finset.mem_filter, triangleHypergraphE, Finset.mem_image] at hT
    obtain ⟨⟨t, ht, rfl⟩, heT⟩ := hT
    rw [Finset.mem_powersetCard] at heT
    obtain ⟨hesub, hecard⟩ := heT
    obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hecard
    have hclique := SimpleGraph.mem_cliqueFinset_iff.mp ht
    have hxt : x ∈ t := hesub (by simp)
    have hyt : y ∈ t := hesub (by simp)
    have hadjxy : G'.Adj x y := hclique.1 hxt hyt hxy
    have hxy1 : x.1 ≠ y.1 := (cred_adj N hN hep hde x y).mp hadjxy
    set S : Finset (Fin 5 × Fin N) :=
      ((univ : Finset (Fin 5)).filter (fun a => a ≠ x.1 ∧ a ≠ y.1)) ×ˢ (univ : Finset (Fin N))
      with hS
    have hcardS : #S = 3 * N := by
      rw [hS, Finset.card_product]
      have h1 : (univ : Finset (Fin 5)).filter (fun a => a ≠ x.1 ∧ a ≠ y.1)
          = (univ : Finset (Fin 5)) \ {x.1, y.1} := by
        ext a; simp
      have h2 : #((univ : Finset (Fin 5)) \ {x.1, y.1}) = 3 := by
        rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_pair hxy1]
        simp
      rw [h1, h2]
      simp
    rw [← hcardS]
    refine card_filter_triangleHypergraphE_le_of_subset G' _ S ?_
    intro v hve hadj
    have hvx : G'.Adj v x := hadj x (by simp)
    have hvy : G'.Adj v y := hadj y (by simp)
    rw [hS, Finset.mem_product]
    exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (cred_adj N hN hep hde v x).mp hvx, (cred_adj N hN hep hde v y).mp hvy⟩, Finset.mem_univ _⟩

/-- **The fractional triangle packing number of the five-partite blow-up is at least `10N²/3`.** -/
theorem nu3star_fivePartite_ge (N : ℕ) (hN : 0 < N) {ep de : ℝ} (hep : 0 < ep) (hde : de ≤ 1) :
    10 * (N : ℝ) ^ 2 / 3 ≤
      nu3star ((⊤ : SimpleGraph (Fin 5 × Fin N)).regularityReduced (cpartition N hN) ep de) := by
  classical
  set G' := (⊤ : SimpleGraph (Fin 5 × Fin N)).regularityReduced (cpartition N hN) ep de with hG'
  have hNR : (0:ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hD : (0:ℝ) < 3 * (N : ℝ) := by linarith only [hNR]
  have hmain := card_triangles_div_le_nu3star G' hD (fun e => by
    have := cred_edge_bound N hN hep hde e
    have h2 : (#((triangleHypergraphE G').filter (fun T => e ∈ T)) : ℝ) ≤ ((3 * N : ℕ) : ℝ) := by
      exact_mod_cast this
    simpa using h2)
  have hcount : (10 * ((N : ℝ) * N * N)) ≤ ((G'.cliqueFinset 3).card : ℝ) := by
    have := cred_card_cliques N hN hep hde
    have : ((10 * (N * N * N) : ℕ) : ℝ) ≤ ((G'.cliqueFinset 3).card : ℝ) := by exact_mod_cast this
    push_cast at this
    linarith
  have hstep : 10 * (N : ℝ) ^ 2 / 3 ≤ ((G'.cliqueFinset 3).card : ℝ) / (3 * N) := by
    rw [le_div_iff₀ hD]
    nlinarith only [hcount]
  exact hstep.trans hmain

/-! ### The area available to the rectangles -/

/-- The ordered pairs of vertices lying in two different clusters. -/
def crossPairs (N : ℕ) : Finset ((Fin 5 × Fin N) × (Fin 5 × Fin N)) :=
  (univ : Finset ((Fin 5 × Fin N) × (Fin 5 × Fin N))).filter (fun p => p.1.1 ≠ p.2.1)

theorem card_crossPairs_le (N : ℕ) : #(crossPairs N) ≤ 20 * (N * N) := by
  classical
  have hcard : #(((univ : Finset (Fin 5 × Fin 5)).filter (fun z => z.1 ≠ z.2)) ×ˢ
      (univ : Finset (Fin N × Fin N))) = 20 * (N * N) := by
    rw [Finset.card_product]
    have h1 : #((univ : Finset (Fin 5 × Fin 5)).filter (fun z => z.1 ≠ z.2)) = 20 := by decide
    have h2 : #(univ : Finset (Fin N × Fin N)) = N * N := by simp
    rw [h1, h2]
  rw [← hcard]
  refine Finset.card_le_card_of_injOn (fun p => ((p.1.1, p.2.1), (p.1.2, p.2.2))) ?_ ?_
  · rintro ⟨⟨a, i⟩, ⟨b, j⟩⟩ hp
    simp only [crossPairs, Finset.coe_filter, Set.mem_setOf_eq,
      Finset.mem_univ, true_and] at hp
    simp [hp]
  · rintro ⟨⟨a, i⟩, ⟨b, j⟩⟩ - ⟨⟨a', i'⟩, ⟨b', j'⟩⟩ - heq
    simp only [Prod.mk.injEq] at heq ⊢
    exact ⟨⟨heq.1.1, heq.2.1⟩, heq.1.2, heq.2.2⟩

/-- **The rectangles of the family fit into the cross-cluster pairs.** -/
theorem sum_area_le_cross {N k : ℕ} (A B C : ℕ → Finset (Fin 5 × Fin N))
    (hAB : ∀ i < k, Disjoint (A i) (B i)) (hAC : ∀ i < k, Disjoint (A i) (C i))
    (hBC : ∀ i < k, Disjoint (B i) (C i))
    (hcross : ∀ i < k, tripleRect (A i) (B i) (C i) ⊆ crossPairs N)
    (hdisj : ∀ i < k, ∀ j < k, i ≠ j →
      Disjoint (tripleRect (A i) (B i) (C i)) (tripleRect (A j) (B j) (C j))) :
    2 * ∑ i ∈ Finset.range k, (#(A i) * #(B i) + #(A i) * #(C i) + #(B i) * #(C i))
      ≤ 20 * (N * N) := by
  classical
  have hpair : ((Finset.range k : Finset ℕ) : Set ℕ).PairwiseDisjoint
      (fun i => tripleRect (A i) (B i) (C i)) := by
    intro i hi j hj hij
    exact hdisj i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj) hij
  have hsum : ∑ i ∈ Finset.range k, #(tripleRect (A i) (B i) (C i))
      = #((Finset.range k).biUnion (fun i => tripleRect (A i) (B i) (C i))) :=
    (Finset.card_biUnion hpair).symm
  have hle : #((Finset.range k).biUnion (fun i => tripleRect (A i) (B i) (C i)))
      ≤ #(crossPairs N) := by
    refine Finset.card_le_card ?_
    intro z hz
    rw [Finset.mem_biUnion] at hz
    obtain ⟨i, hi, hz⟩ := hz
    exact hcross i (Finset.mem_range.mp hi) hz
  have hterm : ∀ i ∈ Finset.range k, #(tripleRect (A i) (B i) (C i))
      = 2 * (#(A i) * #(B i) + #(A i) * #(C i) + #(B i) * #(C i)) := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    exact card_tripleRect (hAB i hi') (hAC i hi') (hBC i hi')
  calc 2 * ∑ i ∈ Finset.range k, (#(A i) * #(B i) + #(A i) * #(C i) + #(B i) * #(C i))
      = ∑ i ∈ Finset.range k, #(tripleRect (A i) (B i) (C i)) := by
        rw [Finset.mul_sum]
        exact (Finset.sum_congr rfl hterm).symm
    _ = #((Finset.range k).biUnion (fun i => tripleRect (A i) (B i) (C i))) := hsum
    _ ≤ #(crossPairs N) := hle
    _ ≤ 20 * (N * N) := card_crossPairs_le N

/-! ### The shape of a block sub-triple of the five-cluster complete graph -/

theorem tripleRect_symm {V : Type} [DecidableEq V] {A B C : Finset V} {x y : V}
    (h : (x, y) ∈ tripleRect A B C) : (y, x) ∈ tripleRect A B C := by
  simp only [tripleRect, Finset.mem_union, Finset.mem_product] at h ⊢
  tauto

theorem prod_subset_tripleRect_AB {V : Type} [DecidableEq V] {A B C : Finset V} :
    A ×ˢ B ⊆ tripleRect A B C := by
  intro z hz
  simp only [tripleRect, Finset.mem_union]
  exact Or.inl (Or.inl (Or.inl hz))

theorem prod_subset_tripleRect_AC {V : Type} [DecidableEq V] {A B C : Finset V} :
    A ×ˢ C ⊆ tripleRect A B C := by
  intro z hz
  simp only [tripleRect, Finset.mem_union]
  exact Or.inl (Or.inr (Or.inl hz))

theorem prod_subset_tripleRect_BC {V : Type} [DecidableEq V] {A B C : Finset V} :
    B ×ˢ C ⊆ tripleRect A B C := by
  intro z hz
  simp only [tripleRect, Finset.mem_union]
  exact Or.inr (Or.inl hz)

/-- The index of the cluster a set of vertices lives in. -/
def partIdx {N : ℕ} (S : Finset (Fin 5 × Fin N)) : Fin 5 :=
  if h : (S.image Prod.fst).Nonempty then (S.image Prod.fst).min' h else 0

theorem partIdx_cpart (N : ℕ) (hN : 0 < N) (a : Fin 5) : partIdx (cpart N a) = a := by
  have himg : (cpart N a).image Prod.fst = {a} := by
    ext b
    simp only [Finset.mem_image, Finset.mem_singleton]
    constructor
    · rintro ⟨v, hv, rfl⟩; exact mem_cpart.mp hv
    · rintro rfl; exact ⟨⟨_, ⟨0, hN⟩⟩, mem_cpart.mpr rfl, rfl⟩
  simp [partIdx, himg]

/-- **The numerical shape of a block sub-triple** at `δ = 1`, `α = 1/2` in the five-cluster
complete graph: the three clusters are three different ones, the three blocks are large halves of
them, and all three have size within `1` of the scale `τ`. -/
theorem grid_digest (N : ℕ) (hN : 0 < N) {τ : ℝ} {U W X A B C : Finset (Fin 5 × Fin N)}
    (h : IsGridSubTriple (⊤ : SimpleGraph (Fin 5 × Fin N)) (cpartition N hN) (1 / 8) 1 (1 / 2) τ
      U W X A B C) :
    ∃ a b c : Fin 5, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ U = cpart N a ∧ W = cpart N b ∧ X = cpart N c ∧
      A ⊆ cpart N a ∧ B ⊆ cpart N b ∧ C ⊆ cpart N c ∧
      ((N : ℝ) / 2 ≤ #A ∧ (N : ℝ) / 2 ≤ #B ∧ (N : ℝ) / 2 ≤ #C) ∧
      (|(#A : ℝ) - τ| ≤ 1 ∧ |(#B : ℝ) - τ| ≤ 1 ∧ |(#C : ℝ) - τ| ≤ 1) := by
  obtain ⟨hgood, hAU, hBW, hCX, hrelA, hrelB, hrelC, hsA, hsB, hsC⟩ := h
  obtain ⟨hU, hW, hX, hUW, hUX, hWX, -, -, -, -, -, -⟩ := hgood
  rw [cpartition_parts] at hU hW hX
  obtain ⟨a, rfl⟩ := mem_cparts.mp hU
  obtain ⟨b, rfl⟩ := mem_cparts.mp hW
  obtain ⟨c, rfl⟩ := mem_cparts.mp hX
  have hab : a ≠ b := by rintro rfl; exact hUW rfl
  have hac : a ≠ c := by rintro rfl; exact hUX rfl
  have hbc : b ≠ c := by rintro rfl; exact hWX rfl
  have hdWX : ((⊤ : SimpleGraph (Fin 5 × Fin N)).edgeDensity (cpart N b) (cpart N c) : ℝ) = 1 := by
    rw [top_edgeDensity (cpart_disjoint hbc) (cpart_nonempty hN b) (cpart_nonempty hN c)]
    norm_num
  have hdUX : ((⊤ : SimpleGraph (Fin 5 × Fin N)).edgeDensity (cpart N a) (cpart N c) : ℝ) = 1 := by
    rw [top_edgeDensity (cpart_disjoint hac) (cpart_nonempty hN a) (cpart_nonempty hN c)]
    norm_num
  have hdUW : ((⊤ : SimpleGraph (Fin 5 × Fin N)).edgeDensity (cpart N a) (cpart N b) : ℝ) = 1 := by
    rw [top_edgeDensity (cpart_disjoint hab) (cpart_nonempty hN a) (cpart_nonempty hN b)]
    norm_num
  rw [hdWX] at hsA
  rw [hdUX] at hsB
  rw [hdUW] at hsC
  rw [card_cpart] at hrelA hrelB hrelC
  refine ⟨a, b, c, hab, hac, hbc, rfl, rfl, rfl, hAU, hBW, hCX, ⟨by linarith, by linarith,
    by linarith⟩, ?_, ?_, ?_⟩
  · simpa using hsA
  · simpa using hsB
  · simpa using hsC

/-! ### Blocks bigger than half a cluster: at most one rectangle per cluster pair -/

/-- Two subsets of a cluster, each of more than half its size, meet. -/
theorem big_subsets_meet {N : ℕ} {p : Fin 5} {R R' : Finset (Fin 5 × Fin N)}
    (hR : R ⊆ cpart N p) (hR' : R' ⊆ cpart N p) (hc : (N : ℝ) < 2 * #R)
    (hc' : (N : ℝ) < 2 * #R') : ∃ x, x ∈ R ∧ x ∈ R' := by
  classical
  by_contra hcon
  push_neg at hcon
  have hdisjRR : Disjoint R R' := Finset.disjoint_left.mpr (fun x hx hx' => hcon x hx hx')
  have hun : #(R ∪ R') = #R + #R' := Finset.card_union_of_disjoint hdisjRR
  have hsub : R ∪ R' ⊆ cpart N p := Finset.union_subset hR hR'
  have hle : #(R ∪ R') ≤ N := by
    have := Finset.card_le_card hsub
    rwa [card_cpart] at this
  have hleR : (#R : ℝ) + (#R' : ℝ) ≤ (N : ℝ) := by
    have : ((#R + #R' : ℕ) : ℝ) ≤ ((N : ℕ) : ℝ) := by exact_mod_cast hun ▸ hle
    push_cast at this
    linarith only [this]
  linarith only [hc, hc', hleR]

theorem pair_ne_of_three {a b c : Fin 5} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ({a, b} : Finset (Fin 5)) ≠ {a, c} ∧ ({a, b} : Finset (Fin 5)) ≠ {b, c} ∧
      ({a, c} : Finset (Fin 5)) ≠ {b, c} := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have hc : c ∈ ({a, b} : Finset (Fin 5)) := by rw [h]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with rfl | rfl
    · exact hac rfl
    · exact hbc rfl
  · intro h
    have hc : c ∈ ({a, b} : Finset (Fin 5)) := by rw [h]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with rfl | rfl
    · exact hac rfl
    · exact hbc rfl
  · intro h
    have hb : b ∈ ({a, c} : Finset (Fin 5)) := by rw [h]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hb
    rcases hb with rfl | rfl
    · exact hab rfl
    · exact hbc rfl

theorem finset_pair_eq_pair {a b c d : Fin 5} (hab : a ≠ b)
    (h : ({a, b} : Finset (Fin 5)) = {c, d}) : (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  have ha : a ∈ ({c, d} : Finset (Fin 5)) := by rw [← h]; simp
  have hb : b ∈ ({c, d} : Finset (Fin 5)) := by rw [← h]; simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
  rcases ha with rfl | rfl
  · rcases hb with rfl | rfl
    · exact absurd rfl hab
    · exact Or.inl ⟨rfl, rfl⟩
  · rcases hb with rfl | rfl
    · exact Or.inr ⟨rfl, rfl⟩
    · exact absurd rfl hab

set_option maxHeartbeats 1000000 in
/-- **At the coarse scale `τ > N/2 + 1` at most three sub-triples fit**: each of them occupies three
of the ten cluster pairs, and no cluster pair can carry two of them, since two rectangles with both
sides larger than half a cluster always meet. -/
theorem card_le_of_disjoint_big_rects (N : ℕ) (hN : 0 < N) {τ : ℝ} {k : ℕ}
    (U W X A B C : ℕ → Finset (Fin 5 × Fin N))
    (hgrid : ∀ i < k, IsGridSubTriple (⊤ : SimpleGraph (Fin 5 × Fin N)) (cpartition N hN)
      (1 / 8) 1 (1 / 2) τ (U i) (W i) (X i) (A i) (B i) (C i))
    (hdisj : ∀ i < k, ∀ j < k, i ≠ j →
      Disjoint (tripleRect (A i) (B i) (C i)) (tripleRect (A j) (B j) (C j)))
    (hbig : (N : ℝ) < 2 * (τ - 1)) : k ≤ 3 := by
  classical
  set g : ℕ × Fin 3 → Finset (Fin 5) := fun z =>
    if z.2 = 0 then {partIdx (U z.1), partIdx (W z.1)}
    else if z.2 = 1 then {partIdx (U z.1), partIdx (X z.1)}
    else {partIdx (W z.1), partIdx (X z.1)} with hg
  have hkey : ∀ i, i < k → ∀ m : Fin 3, ∃ p q : Fin 5, ∃ R S : Finset (Fin 5 × Fin N),
      p ≠ q ∧ g (i, m) = {p, q} ∧ R ⊆ cpart N p ∧ S ⊆ cpart N q ∧
      (N : ℝ) < 2 * #R ∧ (N : ℝ) < 2 * #S ∧
      ∀ x ∈ R, ∀ y ∈ S, (x, y) ∈ tripleRect (A i) (B i) (C i) := by
    intro i hi m
    obtain ⟨a, b, c, hab, hac, hbc, hU, hW, hX, hA, hB, hC, -, hAt, hBt, hCt⟩ :=
      grid_digest N hN (hgrid i hi)
    have hpa : partIdx (U i) = a := by rw [hU]; exact partIdx_cpart N hN a
    have hpb : partIdx (W i) = b := by rw [hW]; exact partIdx_cpart N hN b
    have hpc : partIdx (X i) = c := by rw [hX]; exact partIdx_cpart N hN c
    have hcA : (N : ℝ) < 2 * #(A i) := by
      have := (abs_le.mp hAt).1; linarith only [hbig, this]
    have hcB : (N : ℝ) < 2 * #(B i) := by
      have := (abs_le.mp hBt).1; linarith only [hbig, this]
    have hcC : (N : ℝ) < 2 * #(C i) := by
      have := (abs_le.mp hCt).1; linarith only [hbig, this]
    fin_cases m
    · refine ⟨a, b, A i, B i, hab, by simp [hg, hpa, hpb], hA, hB, hcA, hcB, ?_⟩
      intro x hx y hy
      exact prod_subset_tripleRect_AB (Finset.mem_product.mpr ⟨hx, hy⟩)
    · refine ⟨a, c, A i, C i, hac, by simp [hg, hpa, hpc], hA, hC, hcA, hcC, ?_⟩
      intro x hx y hy
      exact prod_subset_tripleRect_AC (Finset.mem_product.mpr ⟨hx, hy⟩)
    · refine ⟨b, c, B i, C i, hbc, by simp [hg, hpb, hpc], hB, hC, hcB, hcC, ?_⟩
      intro x hx y hy
      exact prod_subset_tripleRect_BC (Finset.mem_product.mpr ⟨hx, hy⟩)
  have hcount : k * 3 ≤ 10 := by
    have hdom : #((Finset.range k) ×ˢ (univ : Finset (Fin 3))) = k * 3 := by
      rw [Finset.card_product]; simp
    have htgt : #((univ : Finset (Fin 5)).powersetCard 2) = 10 := by decide
    rw [← hdom, ← htgt]
    refine Finset.card_le_card_of_injOn g ?_ ?_
    · rintro ⟨i, m⟩ hz
      simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_range] at hz
      obtain ⟨p, q, R, S, hpq, hgz, -, -, -, -, -⟩ := hkey i hz.1 m
      simp only [Finset.mem_coe, Finset.mem_powersetCard]
      exact ⟨Finset.subset_univ _, by rw [hgz, Finset.card_pair hpq]⟩
    · rintro ⟨i, m⟩ hz ⟨i', m'⟩ hz' heq
      simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_range] at hz hz'
      obtain ⟨p, q, R, S, hpq, hgz, hR, hS, hRc, hSc, hRS⟩ := hkey i hz.1 m
      obtain ⟨p', q', R', S', hpq', hgz', hR', hS', hR'c, hS'c, hR'S'⟩ := hkey i' hz'.1 m'
      by_cases hii : i = i'
      · subst hii
        obtain ⟨a, b, c, hab, hac, hbc, hU, hW, hX, -, -, -, -, -, -, -⟩ :=
          grid_digest N hN (hgrid i hz.1)
        have hpa : partIdx (U i) = a := by rw [hU]; exact partIdx_cpart N hN a
        have hpb : partIdx (W i) = b := by rw [hW]; exact partIdx_cpart N hN b
        have hpc : partIdx (X i) = c := by rw [hX]; exact partIdx_cpart N hN c
        obtain ⟨hne1, hne2, hne3⟩ := pair_ne_of_three hab hac hbc
        have hgval : ∀ n : Fin 3, g (i, n) = if n = 0 then ({a, b} : Finset (Fin 5))
            else if n = 1 then {a, c} else {b, c} := by
          intro n
          simp only [hg, hpa, hpb, hpc]
        rw [Prod.mk.injEq]
        refine ⟨rfl, ?_⟩
        rw [hgval m, hgval m'] at heq
        clear hkey hgrid hdisj hRS hR'S' hR hS hR' hS' hRc hSc hR'c hS'c hgz hgz'
          hpq hpq' hgval hU hW hX hpa hpb hpc
        fin_cases m <;> fin_cases m' <;>
          simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceEq,
            if_true, if_false] at heq ⊢ <;>
          first
            | rfl
            | exact absurd heq hne1
            | exact absurd heq hne2
            | exact absurd heq hne3
            | exact absurd heq.symm hne1
            | exact absurd heq.symm hne2
            | exact absurd heq.symm hne3
      · exfalso
        rw [hgz, hgz'] at heq
        rcases finset_pair_eq_pair hpq heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · obtain ⟨x, hx, hx'⟩ := big_subsets_meet hR hR' hRc hR'c
          obtain ⟨y, hy, hy'⟩ := big_subsets_meet hS hS' hSc hS'c
          exact (Finset.disjoint_left.mp (hdisj i hz.1 i' hz'.1 hii))
            (hRS x hx y hy) (hR'S' x hx' y hy')
        · obtain ⟨x, hx, hx'⟩ := big_subsets_meet hR hS' hRc hS'c
          obtain ⟨y, hy, hy'⟩ := big_subsets_meet hS hR' hSc hR'c
          exact (Finset.disjoint_left.mp (hdisj i hz.1 i' hz'.1 hii))
            (hRS x hx y hy) (tripleRect_symm (hR'S' y hy' x hx'))
  omega


/-! ### The total area of a family of block sub-triples -/

theorem mem_crossPairs_of {N : ℕ} {p q : Fin 5} {x y : Fin 5 × Fin N}
    (hx : x ∈ cpart N p) (hy : y ∈ cpart N q) (hpq : p ≠ q) : (x, y) ∈ crossPairs N := by
  simp only [crossPairs, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [show ((x, y) : (Fin 5 × Fin N) × (Fin 5 × Fin N)).1.1 = x.1 from rfl,
    show ((x, y) : (Fin 5 × Fin N) × (Fin 5 × Fin N)).2.1 = y.1 from rfl,
    mem_cpart.mp hx, mem_cpart.mp hy]
  exact hpq

theorem tripleRect_subset_crossPairs {N : ℕ} {a b c : Fin 5} {A B C : Finset (Fin 5 × Fin N)}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hA : A ⊆ cpart N a) (hB : B ⊆ cpart N b) (hC : C ⊆ cpart N c) :
    tripleRect A B C ⊆ crossPairs N := by
  rintro ⟨x, y⟩ hz
  simp only [tripleRect, Finset.mem_union, Finset.mem_product] at hz
  rcases hz with ((⟨h1, h2⟩ | ⟨h1, h2⟩) | (⟨h1, h2⟩ | ⟨h1, h2⟩)) | (⟨h1, h2⟩ | ⟨h1, h2⟩)
  · exact mem_crossPairs_of (hA h1) (hB h2) hab
  · exact mem_crossPairs_of (hB h1) (hA h2) hab.symm
  · exact mem_crossPairs_of (hA h1) (hC h2) hac
  · exact mem_crossPairs_of (hC h1) (hA h2) hac.symm
  · exact mem_crossPairs_of (hB h1) (hC h2) hbc
  · exact mem_crossPairs_of (hC h1) (hB h2) hbc.symm

/-- **The total covering area of a disjoint family of block sub-triples is at most `9.9 N²`.**

Two regimes: if the scale `τ` exceeds `N/2 + 1` then all blocks are bigger than half a cluster, so
at most three sub-triples fit (`Nibble.AX1.card_le_of_disjoint_big_rects`) and the area is at most
`9N²`; otherwise every block has at most `N/2 + 2` vertices while still having at least `N/2`, so
the disjointness of the rectangles caps the number of sub-triples at `13` and the area at
`39 (N/2 + 2)² ≤ 9.9 N²`. -/
theorem blockCover_family_bound (N : ℕ) (hN : 0 < N) (hN1000 : 1000 ≤ N) {τ : ℝ} {k : ℕ}
    (U W X A B C : ℕ → Finset (Fin 5 × Fin N))
    (hgrid : ∀ i < k, IsGridSubTriple (⊤ : SimpleGraph (Fin 5 × Fin N)) (cpartition N hN)
      (1 / 8) 1 (1 / 2) τ (U i) (W i) (X i) (A i) (B i) (C i))
    (hdisj : ∀ i < k, ∀ j < k, i ≠ j →
      Disjoint (tripleRect (A i) (B i) (C i)) (tripleRect (A j) (B j) (C j))) :
    ∑ i ∈ Finset.range k,
        ((#(A i) : ℝ) * #(B i) + (#(A i) : ℝ) * #(C i) + (#(B i) : ℝ) * #(C i))
      ≤ 99 * (N : ℝ) ^ 2 / 10 := by
  classical
  have hNR : (0:ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hN1000R : (1000:ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1000
  -- basic per-index data
  have hbase : ∀ i < k, (A i ⊆ cpart N (partIdx (U i)) ∧ B i ⊆ cpart N (partIdx (W i)) ∧
      C i ⊆ cpart N (partIdx (X i))) ∧
      (Disjoint (A i) (B i) ∧ Disjoint (A i) (C i) ∧ Disjoint (B i) (C i)) ∧
      tripleRect (A i) (B i) (C i) ⊆ crossPairs N ∧
      ((N : ℝ) / 2 ≤ #(A i) ∧ (N : ℝ) / 2 ≤ #(B i) ∧ (N : ℝ) / 2 ≤ #(C i)) ∧
      (|(#(A i) : ℝ) - τ| ≤ 1 ∧ |(#(B i) : ℝ) - τ| ≤ 1 ∧ |(#(C i) : ℝ) - τ| ≤ 1) := by
    intro i hi
    obtain ⟨a, b, c, hab, hac, hbc, hU, hW, hX, hA, hB, hC, hbig, hnear⟩ :=
      grid_digest N hN (hgrid i hi)
    have hpa : partIdx (U i) = a := by rw [hU]; exact partIdx_cpart N hN a
    have hpb : partIdx (W i) = b := by rw [hW]; exact partIdx_cpart N hN b
    have hpc : partIdx (X i) = c := by rw [hX]; exact partIdx_cpart N hN c
    refine ⟨⟨by rw [hpa]; exact hA, by rw [hpb]; exact hB, by rw [hpc]; exact hC⟩,
      ⟨?_, ?_, ?_⟩, tripleRect_subset_crossPairs hab hac hbc hA hB hC, hbig, hnear⟩
    · exact Finset.disjoint_of_subset_left hA
        (Finset.disjoint_of_subset_right hB (cpart_disjoint hab))
    · exact Finset.disjoint_of_subset_left hA
        (Finset.disjoint_of_subset_right hC (cpart_disjoint hac))
    · exact Finset.disjoint_of_subset_left hB
        (Finset.disjoint_of_subset_right hC (cpart_disjoint hbc))
  have hareaN : 2 * ∑ i ∈ Finset.range k,
      (#(A i) * #(B i) + #(A i) * #(C i) + #(B i) * #(C i)) ≤ 20 * (N * N) :=
    sum_area_le_cross A B C (fun i hi => (hbase i hi).2.1.1) (fun i hi => (hbase i hi).2.1.2.1)
      (fun i hi => (hbase i hi).2.1.2.2) (fun i hi => (hbase i hi).2.2.1)
      hdisj
  have harea : 2 * ∑ i ∈ Finset.range k,
      ((#(A i) : ℝ) * #(B i) + (#(A i) : ℝ) * #(C i) + (#(B i) : ℝ) * #(C i))
      ≤ 20 * ((N : ℝ) * N) := by
    have := (Nat.cast_le (α := ℝ)).mpr hareaN
    push_cast at this
    linarith only [this]
  by_cases hbig : (N : ℝ) < 2 * (τ - 1)
  · -- coarse regime: at most three sub-triples, each of area at most `3N²`
    have hk : k ≤ 3 := card_le_of_disjoint_big_rects N hN U W X A B C hgrid hdisj hbig
    have hterm : ∀ i ∈ Finset.range k,
        ((#(A i) : ℝ) * #(B i) + (#(A i) : ℝ) * #(C i) + (#(B i) : ℝ) * #(C i))
          ≤ 3 * (N : ℝ) ^ 2 := by
      intro i hi
      have hi' := Finset.mem_range.mp hi
      obtain ⟨⟨hA, hB, hC⟩, -, -, -, -⟩ := hbase i hi'
      have cA : (#(A i) : ℝ) ≤ (N : ℝ) := by
        have := Finset.card_le_card hA
        rw [card_cpart] at this
        exact_mod_cast this
      have cB : (#(B i) : ℝ) ≤ (N : ℝ) := by
        have := Finset.card_le_card hB
        rw [card_cpart] at this
        exact_mod_cast this
      have cC : (#(C i) : ℝ) ≤ (N : ℝ) := by
        have := Finset.card_le_card hC
        rw [card_cpart] at this
        exact_mod_cast this
      have pA : (0:ℝ) ≤ #(A i) := Nat.cast_nonneg _
      have pB : (0:ℝ) ≤ #(B i) := Nat.cast_nonneg _
      have pC : (0:ℝ) ≤ #(C i) := Nat.cast_nonneg _
      nlinarith only [cA, cB, cC]
    calc ∑ i ∈ Finset.range k,
          ((#(A i) : ℝ) * #(B i) + (#(A i) : ℝ) * #(C i) + (#(B i) : ℝ) * #(C i))
        ≤ ∑ _i ∈ Finset.range k, 3 * (N : ℝ) ^ 2 := Finset.sum_le_sum hterm
      _ = (k : ℝ) * (3 * (N : ℝ) ^ 2) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ 99 * (N : ℝ) ^ 2 / 10 := by
          have hkR : (k : ℝ) ≤ 3 := by exact_mod_cast hk
          nlinarith [sq_nonneg ((N : ℝ))]
  · -- fine regime: every block has between `N/2` and `N/2 + 2` vertices
    push_neg at hbig
    have hτ : τ ≤ (N : ℝ) / 2 + 1 := by linarith only [hbig]
    have hupper : ∀ i ∈ Finset.range k,
        ((#(A i) : ℝ) * #(B i) + (#(A i) : ℝ) * #(C i) + (#(B i) : ℝ) * #(C i))
          ≤ 3 * ((N : ℝ) / 2 + 2) ^ 2 := by
      intro i hi
      have hi' := Finset.mem_range.mp hi
      obtain ⟨-, -, -, -, hnA, hnB, hnC⟩ := hbase i hi'
      have cA : (#(A i) : ℝ) ≤ (N : ℝ) / 2 + 2 := by
        have := (abs_le.mp hnA).2; linarith only [hτ, this]
      have cB : (#(B i) : ℝ) ≤ (N : ℝ) / 2 + 2 := by
        have := (abs_le.mp hnB).2; linarith only [hτ, this]
      have cC : (#(C i) : ℝ) ≤ (N : ℝ) / 2 + 2 := by
        have := (abs_le.mp hnC).2; linarith only [hτ, this]
      have pA : (0:ℝ) ≤ #(A i) := Nat.cast_nonneg _
      have pB : (0:ℝ) ≤ #(B i) := Nat.cast_nonneg _
      have pC : (0:ℝ) ≤ #(C i) := Nat.cast_nonneg _
      nlinarith only [cA, cB, cC]
    have hlower : ∀ i ∈ Finset.range k, 3 * ((N : ℝ) / 2) ^ 2
        ≤ ((#(A i) : ℝ) * #(B i) + (#(A i) : ℝ) * #(C i) + (#(B i) : ℝ) * #(C i)) := by
      intro i hi
      have hi' := Finset.mem_range.mp hi
      obtain ⟨-, -, -, ⟨hA, hB, hC⟩, -⟩ := hbase i hi'
      nlinarith
    have hksum : (k : ℝ) * (3 * ((N : ℝ) / 2) ^ 2)
        ≤ ∑ i ∈ Finset.range k,
          ((#(A i) : ℝ) * #(B i) + (#(A i) : ℝ) * #(C i) + (#(B i) : ℝ) * #(C i)) := by
      calc (k : ℝ) * (3 * ((N : ℝ) / 2) ^ 2)
          = ∑ _i ∈ Finset.range k, 3 * ((N : ℝ) / 2) ^ 2 := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        _ ≤ _ := Finset.sum_le_sum hlower
    have hN2 : (0:ℝ) < (N : ℝ) ^ 2 := by positivity
    have hstep : ((k : ℝ) * 3) * (N : ℝ) ^ 2 ≤ 40 * (N : ℝ) ^ 2 := by nlinarith
    have hk13 : (k : ℝ) ≤ 13 := by
      have h1 : (k : ℝ) * 3 ≤ 40 := le_of_mul_le_mul_right (by linarith) hN2
      have h2 : (k * 3 : ℕ) ≤ 40 := by exact_mod_cast h1
      have h3 : k ≤ 13 := by omega
      exact_mod_cast h3
    calc ∑ i ∈ Finset.range k,
          ((#(A i) : ℝ) * #(B i) + (#(A i) : ℝ) * #(C i) + (#(B i) : ℝ) * #(C i))
        ≤ ∑ _i ∈ Finset.range k, 3 * ((N : ℝ) / 2 + 2) ^ 2 := Finset.sum_le_sum hupper
      _ = (k : ℝ) * (3 * ((N : ℝ) / 2 + 2) ^ 2) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ 13 * (3 * ((N : ℝ) / 2 + 2) ^ 2) := by
          have : (0:ℝ) ≤ 3 * ((N : ℝ) / 2 + 2) ^ 2 := by positivity
          nlinarith
      _ ≤ 99 * (N : ℝ) ^ 2 / 10 := by nlinarith


/-! ### The covering sum of the complete graph is the plain area -/

/-- Every cluster pair of the complete graph has density `1`, so the density-weighted covering sum
of a family of block sub-triples is exactly its area. -/
theorem cover_sum_eq_area (N : ℕ) (hN : 0 < N) {τ : ℝ} {k : ℕ}
    (U W X A B C : ℕ → Finset (Fin 5 × Fin N))
    (hgrid : ∀ i < k, IsGridSubTriple (⊤ : SimpleGraph (Fin 5 × Fin N)) (cpartition N hN)
      (1 / 8) 1 (1 / 2) τ (U i) (W i) (X i) (A i) (B i) (C i)) :
    ∑ i ∈ Finset.range k,
        (((⊤ : SimpleGraph (Fin 5 × Fin N)).edgeDensity (U i) (W i) : ℝ) * (#(A i) : ℝ)
            * (#(B i) : ℝ)
          + ((⊤ : SimpleGraph (Fin 5 × Fin N)).edgeDensity (U i) (X i) : ℝ) * (#(A i) : ℝ)
            * (#(C i) : ℝ)
          + ((⊤ : SimpleGraph (Fin 5 × Fin N)).edgeDensity (W i) (X i) : ℝ) * (#(B i) : ℝ)
            * (#(C i) : ℝ))
      = ∑ i ∈ Finset.range k,
        ((#(A i) : ℝ) * #(B i) + (#(A i) : ℝ) * #(C i) + (#(B i) : ℝ) * #(C i)) := by
  refine Finset.sum_congr rfl (fun i hi => ?_)
  obtain ⟨a, b, c, hab, hac, hbc, hU, hW, hX, -, -, -, -, -⟩ :=
    grid_digest N hN (hgrid i (Finset.mem_range.mp hi))
  have d1 : ((⊤ : SimpleGraph (Fin 5 × Fin N)).edgeDensity (U i) (W i) : ℝ) = 1 := by
    rw [hU, hW, top_edgeDensity (cpart_disjoint hab) (cpart_nonempty hN a) (cpart_nonempty hN b)]
    norm_num
  have d2 : ((⊤ : SimpleGraph (Fin 5 × Fin N)).edgeDensity (U i) (X i) : ℝ) = 1 := by
    rw [hU, hX, top_edgeDensity (cpart_disjoint hac) (cpart_nonempty hN a) (cpart_nonempty hN c)]
    norm_num
  have d3 : ((⊤ : SimpleGraph (Fin 5 × Fin N)).edgeDensity (W i) (X i) : ℝ) = 1 := by
    rw [hW, hX, top_edgeDensity (cpart_disjoint hbc) (cpart_nonempty hN b) (cpart_nonempty hN c)]
    norm_num
  rw [d1, d2, d3]
  ring

/-! ### The refutation -/

/-- **`Nibble.AX1.BlockCoverResidual` is false.**

The witness is `ε = 1/1000`, `δ = 1`, `α = 1/2`, `T₀ = ε₁ = 1`, the complete graph on `5N` vertices
(`N ≥ 1000` and `N ≥ n₀`) and the equipartition into five clusters of size `N`.  The reduced graph
is the complete `5`-partite graph, whose fractional triangle packing number is at least `10N²/3`
(`Nibble.AX1.nu3star_fivePartite_ge`), while any disjoint family of block sub-triples at relative
block size `1/2` has covering area at most `9.9 N²` (`Nibble.AX1.blockCover_family_bound`); the
residual would then require `10N²/3 ≤ 3.3N² + 0.025N²`, which is false. -/
theorem not_blockCoverResidual : ¬ BlockCoverResidual := by
  classical
  intro h
  obtain ⟨n₀, hn₀⟩ := h (1/1000) 1 (1/2) 1 1 (by norm_num) one_pos le_rfl (by norm_num)
    (by norm_num) one_pos one_pos le_rfl
  set N : ℕ := max n₀ 1000 with hNdef
  have hN1000 : 1000 ≤ N := le_max_right _ _
  have hNn₀ : n₀ ≤ N := le_max_left _ _
  have hN : 0 < N := lt_of_lt_of_le (by norm_num) hN1000
  have hNR : (0:ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hN1000R : (1000:ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1000
  have hcard : n₀ ≤ Fintype.card (Fin 5 × Fin N) := by
    rw [card_univ_five]; omega
  have hparts : (4:ℝ) / 1 ≤ (((cpartition N hN).parts.card : ℕ) : ℝ) := by
    rw [cpartition_parts_card]; norm_num
  have hbound : (((cpartition N hN).parts.card : ℕ) : ℝ)
      ≤ ((SzemerediRegularity.bound ((1:ℝ) / 8) ⌈(4:ℝ) / 1⌉₊ : ℕ) : ℝ) := by
    rw [cpartition_parts_card]
    have h1 := SzemerediRegularity.seven_le_initialBound ((1:ℝ)/8) ⌈(4:ℝ)/1⌉₊
    have h2 := SzemerediRegularity.initialBound_le_bound ((1:ℝ)/8) ⌈(4:ℝ)/1⌉₊
    have h3 : (7:ℕ) ≤ SzemerediRegularity.bound ((1:ℝ)/8) ⌈(4:ℝ)/1⌉₊ := le_trans h1 h2
    have h4 : (7:ℝ) ≤ ((SzemerediRegularity.bound ((1:ℝ)/8) ⌈(4:ℝ)/1⌉₊ : ℕ):ℝ) := by
      exact_mod_cast h3
    have h5 : (5:ℝ) ≤ ((SzemerediRegularity.bound ((1:ℝ)/8) ⌈(4:ℝ)/1⌉₊ : ℕ):ℝ) := by linarith only [h4]
    exact_mod_cast h5
  obtain ⟨τ, k, U, W, X, A, B, C, -, hgrid, hdisj, hcov⟩ :=
    hn₀ (Fin 5 × Fin N) (⊤ : SimpleGraph (Fin 5 × Fin N)) (cpartition N hN) hcard
      (cpartition_isEquipartition N hN) hparts hbound
      (cpartition_isUniform N hN (by norm_num))
  rw [cover_sum_eq_area N hN U W X A B C hgrid] at hcov
  have harea := blockCover_family_bound N hN hN1000 U W X A B C hgrid hdisj
  have hlow := nu3star_fivePartite_ge N hN (ep := (1:ℝ)/8) (de := (1:ℝ)/4) (by norm_num)
    (by norm_num)
  rw [card_univ_five] at hcov
  have hVR : (((5 * N : ℕ)) : ℝ) = 5 * (N : ℝ) := by push_cast; ring
  rw [hVR] at hcov
  nlinarith [hlow, hcov, harea, sq_nonneg ((N:ℝ))]

end Nibble.AX1
