import PaperIV.RD09PhaseII

/-!
# RD09 root-factor phase

Concrete adapter from a literal root clique, a matching factor of root edges, and
one or two compatible exterior hosts for every factor edge into the generic phase-II
construction.  It deliberately proves only literal local coverage; global coverage
remains an explicit equality supplied by the eventual RD09 construction.
-/

namespace PaperIV.RD09RootFactorPhase

open Finset PaperIV.Model PaperIV.ExteriorTriangleLift PaperIV.MultiHostTriangleLift
open PaperIV.RD09PhaseII

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

omit [DecidableEq V] in
theorem mem_graphEdges_of_isClique {s : Finset V} (hs : G.IsClique (s : Set V))
    {e : Sym2 V} (hsub : ∀ a ∈ e, a ∈ s) (hd : ¬ e.IsDiag) : e ∈ graphEdges G := by
  induction e with
  | _ a b =>
    have hne : a ≠ b := by simpa [Sym2.isDiag_iff_proj_eq] using hd
    rw [mem_graphEdges, SimpleGraph.mem_edgeSet]
    exact hs (by simpa using hsub a (by simp)) (by simpa using hsub b (by simp)) hne

variable {J : Type*} [Fintype J] [DecidableEq J]
variable {root : Finset V} {hub : J → Finset V} {base : J → Sym2 V}

/-- Primitive RD09 data for a factor of a literal root clique. -/
structure IsRootFactorFamily (G : SimpleGraph V) [DecidableRel G.Adj] (root : Finset V)
    (hub : J → Finset V) (base : J → Sym2 V) : Prop where
  rootClique : G.IsClique (root : Set V)
  baseSubRoot : ∀ j, ∀ a ∈ base j, a ∈ root
  baseNotDiag : ∀ j, ¬ (base j).IsDiag
  baseMatching : ∀ j k, j ≠ k → Disjoint (base j).toFinset (base k).toFinset
  hubCard : ∀ j, (hub j).card = 1 ∨ (hub j).card = 2
  hubClique : ∀ j, G.IsClique (hub j : Set V)
  hubAdj : ∀ j, ∀ a ∈ base j, ∀ w ∈ hub j, G.Adj w a
  hubExterior : ∀ j, ∀ w ∈ hub j, w ∉ root
  hubMeet : ∀ j k, j ≠ k → (hub j ∩ hub k).card ≤ 1

namespace IsRootFactorFamily

variable (h : IsRootFactorFamily G root hub base)
include h

omit [Fintype J] [DecidableEq J] in
theorem base_mem_graphEdges (j : J) : base j ∈ graphEdges G :=
  mem_graphEdges_of_isClique h.rootClique (h.baseSubRoot j) (h.baseNotDiag j)

omit [Fintype V] [Fintype J] [DecidableEq J] in
theorem sep (j k : J) : ∀ a ∈ base j, a ∉ hub k := fun a ha hmem =>
  h.hubExterior k a hmem (h.baseSubRoot j a ha)

omit [Fintype V] [Fintype J] [DecidableEq J] in
theorem base_injective : Function.Injective base := by
  intro j k hjk
  by_contra hne
  have hcard : (base j).toFinset.card = 2 :=
    Sym2.card_toFinset_of_not_isDiag _ (h.baseNotDiag j)
  obtain ⟨a, ha⟩ : (base j).toFinset.Nonempty := Finset.card_pos.mp (by omega)
  exact Finset.disjoint_left.mp (h.baseMatching j k hne) ha (hjk ▸ ha)

omit [Fintype J] [DecidableEq J] in
theorem isPhaseTwoFamily : IsPhaseTwoFamily G hub base :=
  isPhaseTwoFamily_of_matching_hubs h.base_mem_graphEdges h.hubCard h.hubClique h.hubAdj
    h.sep h.baseMatching h.hubMeet

end IsRootFactorFamily

omit [Fintype V] [DecidableRel G.Adj] in
theorem disjoint_toFinset_of_isMatching {M : G.Subgraph} (hM : M.IsMatching)
    {e f : Sym2 V} (he : e ∈ M.edgeSet) (hf : f ∈ M.edgeSet) (hef : e ≠ f) :
    Disjoint e.toFinset f.toFinset := by
  rw [Finset.disjoint_left]
  intro v hve hvf
  have hv : v ∈ e := Sym2.mem_toFinset.mp hve
  have hv' : v ∈ f := Sym2.mem_toFinset.mp hvf
  obtain ⟨a, ha, rfl⟩ : ∃ a, M.Adj v a ∧ e = s(v, a) := by
    induction e with
    | _ x y =>
      simp only [Sym2.mem_iff] at hv
      rw [SimpleGraph.Subgraph.mem_edgeSet] at he
      rcases hv with rfl | rfl
      · exact ⟨y, he, rfl⟩
      · exact ⟨x, he.symm, Sym2.eq_swap⟩
  obtain ⟨b, hb, rfl⟩ : ∃ b, M.Adj v b ∧ f = s(v, b) := by
    induction f with
    | _ x y =>
      simp only [Sym2.mem_iff] at hv'
      rw [SimpleGraph.Subgraph.mem_edgeSet] at hf
      rcases hv' with rfl | rfl
      · exact ⟨y, hf, rfl⟩
      · exact ⟨x, hf.symm, Sym2.eq_swap⟩
  obtain ⟨w, -, hw⟩ := hM (M.edge_vert ha)
  exact hef (by rw [hw a ha, hw b hb])

omit [Fintype V] [DecidableRel G.Adj] [Fintype J] [DecidableEq J] in
theorem baseMatching_of_isMatching {M : G.Subgraph} (hM : M.IsMatching)
    (hmem : ∀ j, base j ∈ M.edgeSet) (hinj : Function.Injective base) :
    ∀ j k, j ≠ k → Disjoint (base j).toFinset (base k).toFinset := fun j k hjk =>
  disjoint_toFinset_of_isMatching hM (hmem j) (hmem k) fun he => hjk (hinj he)

omit [Fintype V] [DecidableRel G.Adj] [Fintype J] [DecidableEq J] in
theorem baseMatching_of_isOneFactorization {ι : Type*} {M : ι → G.Subgraph}
    (hM : SimpleGraph.IsOneFactorization G M) (i : ι)
    (hmem : ∀ j, base j ∈ (M i).edgeSet) (hinj : Function.Injective base) :
    ∀ j k, j ≠ k → Disjoint (base j).toFinset (base k).toFinset :=
  baseMatching_of_isMatching (hM.1 i).1 hmem hinj

omit [Fintype V] [Fintype J] [DecidableEq J] in
theorem baseMatching_of_mapColourClass {A Color : Type*} [DecidableEq A] [DecidableEq Color]
    {f : A ↪ V} {E : Finset (Sym2 A)} {colour : Sym2 A → Color}
    (hproper : PaperIV.ColourClasses.ProperOn E colour) (c : Color)
    (hmem : ∀ j, base j ∈ PaperIV.TransportedMatchings.mapColourClass f E colour c)
    (hinj : Function.Injective base) :
    ∀ j k, j ≠ k → Disjoint (base j).toFinset (base k).toFinset :=
  PaperIV.RD09PhaseII.baseMatching_of_mapColourClass hproper c hmem hinj

omit [Fintype J] [DecidableEq J] in
theorem baseMatching_of_lineGraphColouring {Color : Type*} [Inhabited Color] [DecidableEq Color]
    (C : (G.lineGraph).Coloring Color) (c : Color)
    (hmem : ∀ j, base j ∈ PaperIV.ColourClasses.colourClass (graphEdges G)
      (PaperIV.LineGraphColouring.edgeColourOfLineGraph C) c)
    (hinj : Function.Injective base) :
    ∀ j k, j ≠ k → Disjoint (base j).toFinset (base k).toFinset := by
  have hpd := PaperIV.ColourClasses.colourClass_pairwiseDisjoint_toFinset
    (PaperIV.LineGraphColouring.properOn_of_lineGraph_colouring C) c
  exact fun j k hjk => hpd (by simpa using hmem j) (by simpa using hmem k)
    fun he => hjk (hinj he)

def phaseTwoPool (root : Finset V) (hub : J → Finset V) : Finset V :=
  root ∪ Finset.univ.biUnion hub

omit [Fintype V] [DecidableEq J] in
@[simp] theorem mem_phaseTwoPool {x : V} :
    x ∈ phaseTwoPool root hub ↔ x ∈ root ∨ ∃ j, x ∈ hub j := by
  simp [phaseTwoPool]

omit [Fintype V] [DecidableEq J] in
theorem piece_subset_phaseTwoPool (h : IsRootFactorFamily G root hub base) (j : J) :
    piece hub base j ⊆ phaseTwoPool root hub := by
  intro x hx
  rw [RD09PhaseII.mem_piece] at hx
  rcases hx with hx | hx
  · exact mem_phaseTwoPool.mpr (Or.inr ⟨j, hx⟩)
  · exact mem_phaseTwoPool.mpr (Or.inl (h.baseSubRoot j x hx))

variable {I : Type*} [Fintype I] [DecidableEq I] {z : I → V} {E : I → Finset (Sym2 V)}

structure IsRootHostSeparated (z : I → V) (E : I → Finset (Sym2 V)) (root : Finset V)
    (hub : J → Finset V) : Prop where
  hostExterior : ∀ i, z i ∉ phaseTwoPool root hub
  baseMeetPool : ∀ i, ∀ e ∈ E i, (e.toFinset ∩ phaseTwoPool root hub).card ≤ 1

namespace IsRootHostSeparated

omit [Fintype V] [Fintype I] [DecidableEq I] [DecidableEq J] in
theorem isPhaseCompatible (h : IsRootFactorFamily G root hub base)
    (hs : IsRootHostSeparated z E root hub) : IsPhaseCompatible z E hub base := by
  refine ⟨fun i j hmem => hs.hostExterior i (piece_subset_phaseTwoPool h j hmem), ?_⟩
  intro i j e he
  refine le_trans (Finset.card_le_card ?_) (hs.baseMeetPool i e he)
  exact Finset.inter_subset_inter_left (piece_subset_phaseTwoPool h j)

end IsRootHostSeparated

section Ledgers
variable (h1 : IsMultiExteriorHub G z E) (h : IsRootFactorFamily G root hub base)
  (hs : IsRootHostSeparated z E root hub)
include h1 h hs

omit [DecidableEq J] in
theorem isPacking_union_rootFactorPhases :
    IsPacking G (multiLiftedPacking z E ∪ phaseTwoPacking hub base) :=
  isPacking_union_phases h1 h.isPhaseTwoFamily (hs.isPhaseCompatible h)

omit [DecidableEq I] [DecidableEq J] in
theorem card_union_rootFactorPhases :
    (multiLiftedPacking z E ∪ phaseTwoPacking hub base).card = (∑ i, (E i).card) + Fintype.card J :=
  card_union_phases h1 h.isPhaseTwoFamily (hs.isPhaseCompatible h)

omit [DecidableEq I] [DecidableEq J] in
theorem totalGain_union_rootFactorPhases :
    totalGain (multiLiftedPacking z E ∪ phaseTwoPacking hub base) =
      2 * (∑ i, (E i).card) + (2 * (k3Indices hub).card + 5 * (k4Indices hub).card) :=
  totalGain_union_phases h1 h.isPhaseTwoFamily (hs.isPhaseCompatible h)

omit [DecidableEq J] in
theorem card_coveredEdges_union_rootFactorPhases :
    (coveredEdges (multiLiftedPacking z E ∪ phaseTwoPacking hub base)).card =
      3 * (∑ i, (E i).card) + (3 * (k3Indices hub).card + 6 * (k4Indices hub).card) :=
  card_coveredEdges_union_phases h1 h.isPhaseTwoFamily (hs.isPhaseCompatible h)

omit [Fintype V] [DecidableEq I] [DecidableEq J] h1 in
theorem disjoint_coveredEdges_rootFactorPhases :
    Disjoint (coveredEdges (multiLiftedPacking z E)) (coveredEdges (phaseTwoPacking hub base)) :=
  (hs.isPhaseCompatible h).disjoint_coveredEdges

omit [DecidableEq J] in
theorem isExactPartition_union_rootFactorPhases
    (hcov : coveredEdges (multiLiftedPacking z E) ∪ coveredEdges (phaseTwoPacking hub base) = graphEdges G) :
    IsExactPartition G (multiLiftedPacking z E ∪ phaseTwoPacking hub base) :=
  isExactPartition_union_phases h1 h.isPhaseTwoFamily (hs.isPhaseCompatible h) hcov
end Ledgers

namespace IsRootFactorFamily
variable (h : IsRootFactorFamily G root hub base)
include h
omit [DecidableEq J] in
theorem isPacking_phaseTwoPacking : IsPacking G (phaseTwoPacking hub base) :=
  h.isPhaseTwoFamily.isPacking_phaseTwoPacking
omit [DecidableEq J] in
theorem card_phaseTwoPacking : (phaseTwoPacking hub base).card = Fintype.card J :=
  h.isPhaseTwoFamily.card_phaseTwoPacking
omit [DecidableEq J] in
theorem totalGain_phaseTwoPacking : totalGain (phaseTwoPacking hub base) =
    2 * (k3Indices hub).card + 5 * (k4Indices hub).card :=
  h.isPhaseTwoFamily.totalGain_phaseTwoPacking
omit [DecidableEq J] in
theorem card_coveredEdges_phaseTwoPacking : (coveredEdges (phaseTwoPacking hub base)).card =
    3 * (k3Indices hub).card + 6 * (k4Indices hub).card :=
  h.isPhaseTwoFamily.card_coveredEdges_phaseTwoPacking
omit [DecidableEq J] in
theorem card_k3_add_card_k4 : (k3Indices hub).card + (k4Indices hub).card = Fintype.card J :=
  h.isPhaseTwoFamily.card_k3_add_card_k4
end IsRootFactorFamily

def factorEdges (base : J → Sym2 V) : Finset (Sym2 V) := Finset.univ.image base
omit [Fintype V] [DecidableEq J] in
@[simp] theorem mem_factorEdges {e : Sym2 V} : e ∈ factorEdges base ↔ ∃ j, base j = e := by
  simp [factorEdges]

namespace IsRootFactorFamily
variable (h : IsRootFactorFamily G root hub base)
include h
omit [DecidableEq J] in
theorem base_mem_coveredEdges (j : J) : base j ∈ coveredEdges (phaseTwoPacking hub base) :=
  h.isPhaseTwoFamily.base_mem_coveredEdges j
omit [DecidableEq J] in
theorem rootEdges_subset_coveredEdges {R : Finset (Sym2 V)} (hR : R = factorEdges base) :
    R ⊆ coveredEdges (phaseTwoPacking hub base) := by
  intro e he
  rw [hR, mem_factorEdges] at he
  obtain ⟨j, rfl⟩ := he
  exact h.base_mem_coveredEdges j
omit [Fintype V] [DecidableEq J] in
theorem card_rootEdges {R : Finset (Sym2 V)} (hR : R = factorEdges base) : R.card = Fintype.card J := by
  rw [hR, factorEdges, Finset.card_image_of_injective _ h.base_injective, Finset.card_univ]
omit [DecidableEq J] in
theorem rootEdges_subset_graphEdges {R : Finset (Sym2 V)} (hR : R = factorEdges base) :
    R ⊆ graphEdges G := by
  intro e he
  rw [hR, mem_factorEdges] at he
  obtain ⟨j, rfl⟩ := he
  exact h.base_mem_graphEdges j
end IsRootFactorFamily

omit [DecidableEq I] [DecidableEq J] in
theorem rootEdges_subset_coveredEdges_union_phases
    (h : IsRootFactorFamily G root hub base) {R : Finset (Sym2 V)}
    (hR : R = factorEdges base) :
    R ⊆ coveredEdges (multiLiftedPacking z E ∪ phaseTwoPacking hub base) := by
  intro e he
  rw [coveredEdges_union_phases]
  exact Finset.mem_union_right _ (h.rootEdges_subset_coveredEdges hR he)

omit [DecidableEq I] [DecidableEq J] in
theorem disjoint_phaseOne_rootEdges (h : IsRootFactorFamily G root hub base)
    (h1 : IsMultiExteriorHub G z E) (hs : IsRootHostSeparated z E root hub)
    {R : Finset (Sym2 V)} (hR : R = factorEdges base) (i : I) : Disjoint (E i) R := by
  classical
  rw [Finset.disjoint_left]
  intro e he heR
  have h1' : e ∈ coveredEdges (multiLiftedPacking z E) := base_mem_coveredEdges_multi h1 he
  have h2' : e ∈ coveredEdges (phaseTwoPacking hub base) := h.rootEdges_subset_coveredEdges hR heR
  exact Finset.disjoint_left.mp ((hs.isPhaseCompatible h).disjoint_coveredEdges) h1' h2'

end PaperIV.RD09RootFactorPhase
