/-
  Part B (Phase 2) — a NEGATIVE result about the *rigid* transformer-bank route.

  `absorber_of_transformer_bank` (AbsorberCore.lean) is proved, but its `hrich` hypothesis asks
  for a bank whose configs `S i` are FIXED and pairwise disjoint, and which realises EVERY
  admissible leftover `L` as a union `⋃_{i∈J} S i`.  This file shows that this hypothesis is
  **unsatisfiable** in exactly the regime needed by `build_absorber_transformer`:

  * the configs `S i` are pairwise disjoint (`hcross`), so every edge lies in at most one config;
  * if `e = xy` lies in two triangles `xyz`, `xyw` of the residual graph, then the config
    containing `e` must be contained in both triangles' edge sets, hence equal `{e}`;
  * but a config has size divisible by `3` (it is the difference of two edge-disjoint triangle
    families), so `|S i| = 1` is impossible.

  Since the residual graph is required to have min degree `≥ 9n/10`, two such triangles always
  exist, so the rigid route is a DEAD END, just like the octahedral flex route.  The corrected
  (satisfiable) interface is in `FlexBank.lean`.
-/
import Ax2.PartB.BKLO.AbsorberCore
import Ax2.PartB.BKLO.Gadget
import Ax2.PartB.BKLO.Parity

namespace Ax2.BKLO

open SimpleGraph Finset Ax2

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
/-- The three edges of a triple of pairwise distinct vertices. -/
theorem triEdges_triple {x y z : V} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    triEdges ({x, y, z} : Finset V) = {s(x, y), s(x, z), s(y, z)} := by
  ext e
  induction e using Sym2.inductionOn with | _ a b =>
    simp only [triEdges, mem_filter, mem_sym2_iff, mem_insert, mem_singleton,
      Sym2.mk_isDiag_iff, Sym2.eq_iff]
    aesop

omit [Fintype V] in
/-- Two triangles sharing exactly one vertex pair meet in exactly that edge. -/
theorem triEdges_triple_inter {x y z w : V} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hxw : x ≠ w) (hyw : y ≠ w) (hzw : z ≠ w) :
    triEdges ({x, y, z} : Finset V) ∩ triEdges ({x, y, w} : Finset V) = {s(x, y)} := by
  rw [triEdges_triple hxy hxz hyz, triEdges_triple hxy hxw hyw]
  ext e
  induction e using Sym2.inductionOn with | _ a b =>
    simp only [mem_inter, mem_insert, mem_singleton, Sym2.eq_iff]
    aesop

omit [Fintype V] in
/-- Every vertex has even degree in the edge set of a triangle. -/
theorem triEdges_filter_even {x y z : V} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (v : V) :
    Even (((triEdges ({x, y, z} : Finset V)).filter (fun e => v ∈ e)).card) := by
  have hcov : coveredEdges ({{x, y, z}} : Finset (Finset V)) = triEdges ({x, y, z} : Finset V) := by
    simp [coveredEdges]
  have hcard : ∀ t ∈ ({{x, y, z}} : Finset (Finset V)), t.card = 3 := by
    intro t ht
    rw [Finset.mem_singleton] at ht
    subst ht
    rw [Finset.card_insert_of_notMem (by simp [hxy, hxz]),
      Finset.card_insert_of_notMem (by simp [hyz])]
    simp
  have hdisj : EdgeDisjoint ({{x, y, z}} : Finset (Finset V)) := by
    intro t₁ ht₁ t₂ ht₂ hne
    rw [Finset.mem_singleton] at ht₁ ht₂
    exact absurd (ht₁.trans ht₂.symm) hne
  have := coveredEdges_degree_even ({{x, y, z}} : Finset (Finset V)) hcard hdisj v
  rwa [hcov] at this

/-- A config of a transformer that avoids the base's edges has size divisible by `3`. -/
theorem config_card_dvd_three (G : SimpleGraph V) [DecidableRel G.Adj]
    {Bi Abi : Finset (Finset V)} {Si : Finset (Sym2 V)}
    (hBcl : ∀ t ∈ Bi, G.IsNClique 3 t) (hAbcl : ∀ t ∈ Abi, G.IsNClique 3 t)
    (hBd : EdgeDisjoint Bi) (hAbd : EdgeDisjoint Abi)
    (hcov : coveredEdges Abi = coveredEdges Bi ∪ Si)
    (hdisj : Disjoint Si (coveredEdges Bi)) : 3 ∣ Si.card := by
  have h1 : (coveredEdges Abi).card = 3 * Abi.card := coveredEdges_card G hAbcl hAbd
  have h2 : (coveredEdges Bi).card = 3 * Bi.card := coveredEdges_card G hBcl hBd
  have h3 : (coveredEdges Bi ∪ Si).card = (coveredEdges Bi).card + Si.card :=
    Finset.card_union_of_disjoint hdisj.symm
  rw [hcov, h3, h2] at h1
  omega

omit [Fintype V] in
/-- A config of a transformer that avoids the base's edges has all degrees even.  Together with
`config_card_dvd_three` this says that **every absorbable config is triangle-divisible**: a
transformer can never absorb a leftover chunk with an odd degree or with `|S|` not divisible by
`3`. -/
theorem config_degrees_even (G : SimpleGraph V) [DecidableRel G.Adj]
    {Bi Abi : Finset (Finset V)} {Si : Finset (Sym2 V)}
    (hBcl : ∀ t ∈ Bi, G.IsNClique 3 t) (hAbcl : ∀ t ∈ Abi, G.IsNClique 3 t)
    (hBd : EdgeDisjoint Bi) (hAbd : EdgeDisjoint Abi)
    (hcov : coveredEdges Abi = coveredEdges Bi ∪ Si)
    (hdisj : Disjoint Si (coveredEdges Bi)) (v : V) :
    Even ((Si.filter (fun e => v ∈ e)).card) := by
  classical
  have hAeven := coveredEdges_degree_even Abi (fun t ht => (hAbcl t ht).card_eq) hAbd v
  have hBeven := coveredEdges_degree_even Bi (fun t ht => (hBcl t ht).card_eq) hBd v
  have hsplit : (coveredEdges Abi).filter (fun e => v ∈ e)
      = ((coveredEdges Bi).filter (fun e => v ∈ e)) ∪ (Si.filter (fun e => v ∈ e)) := by
    rw [hcov, Finset.filter_union]
  have hd : Disjoint ((coveredEdges Bi).filter (fun e => v ∈ e)) (Si.filter (fun e => v ∈ e)) :=
    Finset.disjoint_of_subset_left (Finset.filter_subset _ _)
      (Finset.disjoint_of_subset_right (Finset.filter_subset _ _) hdisj.symm)
  rw [hsplit, Finset.card_union_of_disjoint hd] at hAeven
  obtain ⟨k, hk⟩ := hAeven
  obtain ⟨l, hl⟩ := hBeven
  exact ⟨k - l, by omega⟩

/-- **FINDING (not an axiom): the rigid transformer-bank hypothesis `hrich` is contradictory**
as soon as some edge of the leftover-available part of `G` lies in two triangles avoiding the
bank's base edges.  Consequently `absorber_of_transformer_bank` can never be applied with a
nonempty admissible leftover. -/
theorem rigid_bank_hrich_elim (G : SimpleGraph V) [DecidableRel G.Adj] (β : ℝ)
    {ι : Type*} [DecidableEq ι] (I : Finset ι)
    (B Ab : ι → Finset (Finset V)) (S : ι → Finset (Sym2 V))
    (hBcl : ∀ i ∈ I, ∀ t ∈ B i, G.IsNClique 3 t)
    (hAbcl : ∀ i ∈ I, ∀ t ∈ Ab i, G.IsNClique 3 t)
    (hAbcov : ∀ i ∈ I, coveredEdges (Ab i) = coveredEdges (B i) ∪ S i)
    (hBd : ∀ i ∈ I, EdgeDisjoint (B i)) (hAbd : ∀ i ∈ I, EdgeDisjoint (Ab i))
    (hcross : ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
      Disjoint (coveredEdges (B i) ∪ S i) (coveredEdges (B j) ∪ S j))
    (hrich : ∀ L : Finset (Sym2 V), L ⊆ G.edgeFinset →
      Disjoint L (I.biUnion (fun i => coveredEdges (B i))) →
      (L.card : ℝ) ≤ β * (Fintype.card V : ℝ) ^ 2 → 3 ∣ L.card →
      (∀ v : V, Even ((L.filter (fun e => v ∈ e)).card)) →
      ∃ J ⊆ I, J.biUnion S = L)
    {x y z w : V} (hzw : z ≠ w)
    (ht1 : G.IsNClique 3 ({x, y, z} : Finset V)) (ht2 : G.IsNClique 3 ({x, y, w} : Finset V))
    (hd1 : Disjoint (triEdges ({x, y, z} : Finset V)) (I.biUnion (fun i => coveredEdges (B i))))
    (hd2 : Disjoint (triEdges ({x, y, w} : Finset V)) (I.biUnion (fun i => coveredEdges (B i))))
    (hβ : (3 : ℝ) ≤ β * (Fintype.card V : ℝ) ^ 2) : False := by
  classical
  obtain ⟨axy, axz, ayz⟩ := SimpleGraph.is3Clique_triple_iff.mp ht1
  obtain ⟨-, axw, ayw⟩ := SimpleGraph.is3Clique_triple_iff.mp ht2
  have hxy : x ≠ y := axy.ne
  have hxz : x ≠ z := axz.ne
  have hyz : y ≠ z := ayz.ne
  have hxw : x ≠ w := axw.ne
  have hyw : y ≠ w := ayw.ne
  set L1 : Finset (Sym2 V) := triEdges ({x, y, z} : Finset V) with hL1
  set L2 : Finset (Sym2 V) := triEdges ({x, y, w} : Finset V) with hL2
  -- both triangles' edge sets are admissible leftovers
  have hsub : ∀ {a b c : V}, G.Adj a b → G.Adj a c → G.Adj b c →
      triEdges ({a, b, c} : Finset V) ⊆ G.edgeFinset := by
    intro a b c hab hac hbc
    rw [triEdges_triple hab.ne hac.ne hbc.ne]
    intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl <;> simpa using ‹_›
  have hc1 : L1.card = 3 := triEdges_card_of_isNClique G ht1
  have hc2 : L2.card = 3 := triEdges_card_of_isNClique G ht2
  obtain ⟨J1, hJ1I, hJ1⟩ := hrich L1 (hsub axy axz ayz) hd1
    (by rw [hc1]; exact_mod_cast hβ) (by rw [hc1]) (triEdges_filter_even hxy hxz hyz)
  obtain ⟨J2, hJ2I, hJ2⟩ := hrich L2 (hsub axy axw ayw) hd2
    (by rw [hc2]; exact_mod_cast hβ) (by rw [hc2]) (triEdges_filter_even hxy hxw hyw)
  -- the unit owning the shared edge `s(x,y)`
  have hxyL1 : s(x, y) ∈ L1 := by rw [hL1, triEdges_triple hxy hxz hyz]; simp
  have hxyL2 : s(x, y) ∈ L2 := by rw [hL2, triEdges_triple hxy hxw hyw]; simp
  obtain ⟨i, hi1, hiS⟩ := Finset.mem_biUnion.mp (hJ1 ▸ hxyL1)
  obtain ⟨j, hj2, hjS⟩ := Finset.mem_biUnion.mp (hJ2 ▸ hxyL2)
  have hij : i = j := by
    by_contra hne
    have := hcross i (hJ1I hi1) j (hJ2I hj2) hne
    exact (Finset.disjoint_left.mp this (Finset.mem_union_right _ hiS))
      (Finset.mem_union_right _ hjS)
  subst hij
  -- the config of that unit sits inside both triangles, hence equals `{s(x,y)}`
  have hSsub1 : S i ⊆ L1 := by rw [← hJ1]; exact Finset.subset_biUnion_of_mem S hi1
  have hSsub2 : S i ⊆ L2 := by rw [← hJ2]; exact Finset.subset_biUnion_of_mem S hj2
  have hSsub : S i ⊆ ({s(x, y)} : Finset (Sym2 V)) := by
    rw [← triEdges_triple_inter hxy hxz hyz hxw hyw hzw]
    exact Finset.subset_inter hSsub1 hSsub2
  have hScard : (S i).card = 1 := by
    have : S i = ({s(x, y)} : Finset (Sym2 V)) :=
      Finset.Subset.antisymm hSsub (Finset.singleton_subset_iff.mpr hiS)
    rw [this]; simp
  -- but every config has size divisible by 3
  have hdisjS : Disjoint (S i) (coveredEdges (B i)) := by
    refine Finset.disjoint_of_subset_left hSsub1 ?_
    exact Finset.disjoint_of_subset_right
      (Finset.subset_biUnion_of_mem (fun k => coveredEdges (B k)) (hJ1I hi1)) hd1
  have := config_card_dvd_three G (hBcl i (hJ1I hi1)) (hAbcl i (hJ1I hi1)) (hBd i (hJ1I hi1))
    (hAbd i (hJ1I hi1)) (hAbcov i (hJ1I hi1)) hdisjS
  omega

/-- **The rigid transformer-bank route cannot prove `build_absorber_transformer`** (subgraph
form).  If some spanning subgraph `R` of `G` avoiding the bank's reserved edges has min degree
`≥ 9n/10` and `3 ≤ β n²`, then no rigid bank satisfying `hrich` exists. -/
theorem rigid_bank_elim_of_dense_subgraph (G : SimpleGraph V) [DecidableRel G.Adj] (β : ℝ)
    {ι : Type*} [DecidableEq ι] (I : Finset ι)
    (B Ab : ι → Finset (Finset V)) (S : ι → Finset (Sym2 V))
    (hBcl : ∀ i ∈ I, ∀ t ∈ B i, G.IsNClique 3 t)
    (hAbcl : ∀ i ∈ I, ∀ t ∈ Ab i, G.IsNClique 3 t)
    (hAbcov : ∀ i ∈ I, coveredEdges (Ab i) = coveredEdges (B i) ∪ S i)
    (hBd : ∀ i ∈ I, EdgeDisjoint (B i)) (hAbd : ∀ i ∈ I, EdgeDisjoint (Ab i))
    (hcross : ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
      Disjoint (coveredEdges (B i) ∪ S i) (coveredEdges (B j) ∪ S j))
    (hrich : ∀ L : Finset (Sym2 V), L ⊆ G.edgeFinset →
      Disjoint L (I.biUnion (fun i => coveredEdges (B i))) →
      (L.card : ℝ) ≤ β * (Fintype.card V : ℝ) ^ 2 → 3 ∣ L.card →
      (∀ v : V, Even ((L.filter (fun e => v ∈ e)).card)) →
      ∃ J ⊆ I, J.biUnion S = L)
    (R : SimpleGraph V) [DecidableRel R.Adj] (hRle : R ≤ G)
    (hRedge : R.edgeFinset = G.edgeFinset \ coveredEdges (I.biUnion B))
    (hres : ∀ v : V, 9 * Fintype.card V ≤ 10 * R.degree v)
    (hn : 3 ≤ Fintype.card V) (hβ : (3 : ℝ) ≤ β * (Fintype.card V : ℝ) ^ 2) : False := by
  classical
  have hcovU : coveredEdges (I.biUnion B) = I.biUnion (fun i => coveredEdges (B i)) :=
    coveredEdges_biUnion I B
  -- pick an edge of the (dense) residual graph and two common neighbours
  have hne : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨x⟩ := hne
  have hdx := hres x
  have hxpos : 0 < R.degree x := by omega
  obtain ⟨y, hy⟩ := Finset.card_pos.mp (by rwa [R.card_neighborFinset_eq_degree x])
  rw [SimpleGraph.mem_neighborFinset] at hy
  have hdy := hres y
  have hcn := card_common_neighbors_ge R x y
  have h2 : 1 < (R.neighborFinset x ∩ R.neighborFinset y).card := by omega
  obtain ⟨z, hz, w, hw, hzw⟩ := Finset.one_lt_card.mp h2
  rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset, SimpleGraph.mem_neighborFinset] at hz hw
  -- the two triangles `xyz`, `xyw` of the residual graph
  have hRtri : ∀ {a b c : V}, R.Adj a b → R.Adj a c → R.Adj b c →
      G.IsNClique 3 ({a, b, c} : Finset V) := by
    intro a b c hab hac hbc
    exact SimpleGraph.is3Clique_triple_iff.mpr ⟨hRle hab, hRle hac, hRle hbc⟩
  have hRdisj : ∀ {a b c : V}, R.Adj a b → R.Adj a c → R.Adj b c →
      Disjoint (triEdges ({a, b, c} : Finset V)) (I.biUnion (fun i => coveredEdges (B i))) := by
    intro a b c hab hac hbc
    rw [← hcovU, Finset.disjoint_right]
    intro e he hemem
    rw [triEdges_triple hab.ne hac.ne hbc.ne] at hemem
    have hR' : e ∈ R.edgeFinset := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hemem
      rcases hemem with rfl | rfl | rfl <;> simpa using ‹_›
    rw [hRedge, Finset.mem_sdiff] at hR'
    exact hR'.2 he
  exact rigid_bank_hrich_elim G β I B Ab S hBcl hAbcl hAbcov hBd hAbd hcross hrich hzw
    (hRtri hy hz.1 hz.2) (hRtri hy hw.1 hw.2)
    (hRdisj hy hz.1 hz.2) (hRdisj hy hw.1 hw.2) hβ

/-- **The rigid transformer-bank route cannot prove `build_absorber_transformer`.**  If the
residual graph of the bank's core has min degree `≥ 9n/10` (which is exactly what that theorem
demands) and `3 ≤ β n²`, then no rigid bank satisfying `hrich` exists.  Hence the route through
`absorber_of_transformer_bank` is a dead end; use `absorber_of_flexBank` instead. -/
theorem rigid_bank_elim_of_dense_residual (G : SimpleGraph V) [DecidableRel G.Adj] (β : ℝ)
    {ι : Type*} [DecidableEq ι] (I : Finset ι)
    (B Ab : ι → Finset (Finset V)) (S : ι → Finset (Sym2 V))
    (hBcl : ∀ i ∈ I, ∀ t ∈ B i, G.IsNClique 3 t)
    (hAbcl : ∀ i ∈ I, ∀ t ∈ Ab i, G.IsNClique 3 t)
    (hAbcov : ∀ i ∈ I, coveredEdges (Ab i) = coveredEdges (B i) ∪ S i)
    (hBd : ∀ i ∈ I, EdgeDisjoint (B i)) (hAbd : ∀ i ∈ I, EdgeDisjoint (Ab i))
    (hcross : ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
      Disjoint (coveredEdges (B i) ∪ S i) (coveredEdges (B j) ∪ S j))
    (hrich : ∀ L : Finset (Sym2 V), L ⊆ G.edgeFinset →
      Disjoint L (I.biUnion (fun i => coveredEdges (B i))) →
      (L.card : ℝ) ≤ β * (Fintype.card V : ℝ) ^ 2 → 3 ∣ L.card →
      (∀ v : V, Even ((L.filter (fun e => v ∈ e)).card)) →
      ∃ J ⊆ I, J.biUnion S = L)
    (hres : ∀ v : V, 9 * Fintype.card V ≤ 10 * (residual G (I.biUnion B)).degree v)
    (hn : 3 ≤ Fintype.card V) (hβ : (3 : ℝ) ≤ β * (Fintype.card V : ℝ) ^ 2) : False := by
  classical
  refine rigid_bank_elim_of_dense_subgraph G β I B Ab S hBcl hAbcl hAbcov hBd hAbd hcross hrich
    (residual G (I.biUnion B)) ?_ ?_ hres hn hβ
  · exact SimpleGraph.deleteEdges_le _
  · apply Finset.coe_injective
    simp only [SimpleGraph.coe_edgeFinset, residual, SimpleGraph.edgeSet_deleteEdges,
      Finset.coe_sdiff]

end Ax2.BKLO
