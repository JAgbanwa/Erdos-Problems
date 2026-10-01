import PaperIV.RD09PaddedL1Mass
import PaperIV.RootEdgeSplit
import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# Literal root--exterior adapter for RD09

`RootedGraph.outsideGraph` deliberately keeps the root vertices in the
ambient type as isolated vertices.  That is convenient for edge colouring,
but it is not the literal exterior domain required by the phase-I interface.
This file supplies the canonical subtype and proves that no count changes.
-/

namespace PaperIV.RD09RootExteriorAdapter

open Finset PaperIV.Model PaperIV.RD09L1Adapter
open PaperIV.RootVocab

variable {V I : Type*} [Fintype V] [DecidableEq V]
variable [Fintype I] [DecidableEq I]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The literal vertices outside a root finset. -/
abbrev ExteriorVertex (P : Finset V) :=
  {x : V // x ∈ (outsideVertices P : Set V)}

/-- The graph induced on the literal exterior subtype. -/
def exteriorGraph (G : SimpleGraph V) (P : Finset V) :
    SimpleGraph (ExteriorVertex P) :=
  G.induce (outsideVertices P : Set V)

instance exteriorGraphDecidableAdj (P : Finset V) :
    DecidableRel (exteriorGraph G P).Adj :=
  fun x y => inferInstanceAs (Decidable (G.Adj x.1 y.1))

/-- The canonical embedding of the exterior subtype in the original graph. -/
def exteriorEmbedding (P : Finset V) : ExteriorVertex P ↪ V :=
  Function.Embedding.subtype (fun x => x ∈ (outsideVertices P : Set V))

@[simp] theorem exteriorGraph_adj (P : Finset V) (x y : ExteriorVertex P) :
    (exteriorGraph G P).Adj x y ↔ G.Adj x.1 y.1 :=
  Iff.rfl

@[simp] theorem exteriorEmbedding_not_mem (P : Finset V) (x : ExteriorVertex P) :
    exteriorEmbedding P x ∉ P :=
  mem_outsideVertices.mp x.2

/-- The induced exterior graph embeds both homomorphically and reflectively. -/
theorem exteriorEmbedding_hom (P : Finset V) {x y : ExteriorVertex P}
    (h : (exteriorGraph G P).Adj x y) :
    G.Adj (exteriorEmbedding P x) (exteriorEmbedding P y) :=
  h

theorem exteriorEmbedding_reflect (P : Finset V) {x y : ExteriorVertex P}
    (h : G.Adj (exteriorEmbedding P x) (exteriorEmbedding P y)) :
    (exteriorGraph G P).Adj x y :=
  h

/-- The literal exterior edge count is exactly the old exterior count.  This
is proved by the endpoint-preserving bijection, avoiding any dependence on
the chosen decidability proof for the induced graph. -/
theorem card_graphEdges_exteriorGraph (P : Finset V) :
    (graphEdges (exteriorGraph G P)).card = (outsideEdges G P).card := by
  classical
  apply Finset.card_bij
      (fun e _ => Sym2.map (exteriorEmbedding P) e)
  · intro e he
    revert he
    refine Sym2.inductionOn e ?_
    intro x y hxy
    apply Finset.mem_filter.mpr
    refine ⟨?_, ?_⟩
    · rw [Sym2.map_pair_eq]
      exact G.mem_edgeFinset.mpr
        (G.mem_edgeSet.mpr ((exteriorGraph_adj (G := G) P x y).mp
          ((mem_graphEdges (G := exteriorGraph G P)).mp hxy)))
    · rw [Sym2.map_pair_eq, Sym2.toFinset_mk_eq]
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact x.2
      · exact y.2
  · intro e₁ he₁ e₂ he₂ hEq
    exact (Sym2.map.injective (exteriorEmbedding P).injective) hEq
  · intro e he
    revert he
    refine Sym2.inductionOn e ?_
    intro x y hxy
    have hout := (Finset.mem_filter.mp hxy).2
    have hx : x ∈ outsideVertices P := by
      apply hout
      simp
    have hy : y ∈ outsideVertices P := by
      apply hout
      simp
    let x' : ExteriorVertex P := ⟨x, hx⟩
    let y' : ExteriorVertex P := ⟨y, hy⟩
    refine ⟨s(x', y'), ?_, ?_⟩
    · rw [mem_graphEdges, SimpleGraph.mem_edgeSet]
      exact (Finset.mem_filter.mp hxy).1 |> G.mem_edgeFinset.mp |>
        G.mem_edgeSet.mp
    · rw [Sym2.map_pair_eq, Sym2.eq, Sym2.rel_iff]
      exact Or.inl ⟨rfl, rfl⟩

/-- Passing from the ambient outside graph (where root vertices are isolated)
to the literal exterior subtype cannot increase maximum degree. -/
theorem maxDegree_exteriorGraph_le (P : Finset V) :
    (exteriorGraph G P).maxDegree ≤
      (PaperIV.RootVocab.outsideGraph G P).maxDegree := by
  classical
  apply SimpleGraph.maxDegree_le_of_forall_degree_le
  intro x
  have hsub :
      ((exteriorGraph G P).neighborFinset x).map (exteriorEmbedding P) ⊆
        (PaperIV.RootVocab.outsideGraph G P).neighborFinset x.1 := by
    intro y hy
    rw [Finset.mem_map] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    rw [SimpleGraph.mem_neighborFinset] at hz ⊢
    exact ⟨hz, mem_outsideVertices.mp x.2, mem_outsideVertices.mp z.2⟩
  calc
    (exteriorGraph G P).degree x =
        ((exteriorGraph G P).neighborFinset x).card := rfl
    _ = (((exteriorGraph G P).neighborFinset x).map
        (exteriorEmbedding P)).card := by simp
    _ ≤ (PaperIV.RootVocab.outsideGraph G P).degree x.1 :=
      Finset.card_le_card hsub
    _ ≤ (PaperIV.RootVocab.outsideGraph G P).maxDegree :=
      SimpleGraph.degree_le_maxDegree _ _

/-- Likewise every literal exterior clique embeds into the ambient outside
graph, so its clique number cannot increase. -/
theorem cliqueNum_exteriorGraph_le (P : Finset V) :
    (exteriorGraph G P).cliqueNum ≤
      (PaperIV.RootVocab.outsideGraph G P).cliqueNum := by
  classical
  obtain ⟨K, hK⟩ := (exteriorGraph G P).exists_isNClique_cliqueNum
  let L : Finset V := K.map (exteriorEmbedding P)
  have hL : (PaperIV.RootVocab.outsideGraph G P).IsClique (L : Set V) := by
    rw [SimpleGraph.isClique_iff]
    intro x hx y hy hxy
    change x ∈ L at hx
    change y ∈ L at hy
    change x ∈ K.map (exteriorEmbedding P) at hx
    change y ∈ K.map (exteriorEmbedding P) at hy
    rw [Finset.mem_map] at hx hy
    obtain ⟨x', hx', rfl⟩ := hx
    obtain ⟨y', hy', rfl⟩ := hy
    have hxy' : x' ≠ y' := fun h => hxy (congrArg Subtype.val h)
    exact ⟨hK.isClique hx' hy' hxy',
      mem_outsideVertices.mp x'.2, mem_outsideVertices.mp y'.2⟩
  rw [← hK.card_eq]
  have hcard : L.card = K.card := by simp [L]
  rw [← hcard]
  exact hL.card_le_cliqueNum

/-- Enumerate the root without changing its underlying vertices. -/
def rootVertex (P : Finset V) (r : I ≃ {x : V // x ∈ P}) (i : I) : V :=
  (r i).1

@[simp] theorem rootVertex_mem (P : Finset V) (r : I ≃ {x : V // x ∈ P}) (i : I) :
    rootVertex P r i ∈ P :=
  (r i).2

theorem rootVertex_injective (P : Finset V) (r : I ≃ {x : V // x ∈ P}) :
    Function.Injective (rootVertex P r) := by
  intro i j hij
  apply r.injective
  exact Subtype.ext hij

/-- Canonical cyclic index type for a nonempty root.  RD09 uses its group
law only to average over the literal translations. -/
abbrev RootIndex (P : Finset V) := Multiplicative (ZMod P.card)

/-- A finite root is canonically enumerable by a cyclic group of the same
cardinality.  The equivalence is chosen only after the two finite cardinality
computations have been proved equal. -/
noncomputable def cyclicRootEquiv (P : Finset V) [NeZero P.card] :
    RootIndex P ≃ {x : V // x ∈ P} :=
  Fintype.equivOfCardEq (by simp [RootIndex, ZMod.card])

@[simp] theorem card_RootIndex (P : Finset V) [NeZero P.card] :
    Fintype.card (RootIndex P) = P.card := by
  simp [RootIndex, ZMod.card]

/-- The RD09 phase-I missing-incidence set has exactly the cardinality of the
rooted-graph missing-incidence ledger.  The proof is a literal bijection of
pairs; there is no cardinality-only choice hidden here. -/
theorem card_missingIncidences_root_exterior
    (P : Finset V) (r : I ≃ {x : V // x ∈ P}) :
    (missingIncidences G (rootVertex P r) (exteriorEmbedding P)).card =
      PaperIV.RootVocab.missingIncidences G P := by
  classical
  rw [PaperIV.RootVocab.missingIncidences_eq_card_interedges]
  apply Finset.card_bij
      (fun q _ => (rootVertex P r q.1, (exteriorEmbedding P q.2)))
  · intro q hq
    rw [mem_missingIncidences] at hq
    apply Rel.mem_interedges_iff.mpr
    refine ⟨rootVertex_mem P r q.1, q.2.2, ?_⟩
    simp only [SimpleGraph.compl_adj]
    refine ⟨?_, hq⟩
    intro heq
    exact (exteriorEmbedding_not_mem P q.2) (heq ▸ rootVertex_mem P r q.1)
  · intro q₁ hq₁ q₂ hq₂ heq
    apply Prod.ext
    · apply rootVertex_injective P r
      exact congrArg Prod.fst heq
    · apply (exteriorEmbedding P).injective
      exact congrArg Prod.snd heq
  · intro xy hxy
    have hxy' := Rel.mem_interedges_iff.mp hxy
    have hx : xy.1 ∈ P := hxy'.1
    have hy : xy.2 ∈ outsideVertices P := hxy'.2.1
    let i : I := r.symm ⟨xy.1, hx⟩
    let a : ExteriorVertex P := ⟨xy.2, hy⟩
    refine ⟨(i, a), ?_, ?_⟩
    · rw [mem_missingIncidences]
      have hc := hxy'.2.2
      simp only [SimpleGraph.compl_adj] at hc
      simpa [i, a, rootVertex, exteriorEmbedding] using hc.2
    · apply Prod.ext
      · exact congrArg Subtype.val (r.apply_symm_apply ⟨xy.1, hx⟩)
      · rfl

section PhaseI

variable [Nonempty I] [Group I]

open PaperIV.MultiHostTriangleLift PaperIV.RD09PaddedL1Mass
open PaperIV.RootedEliminationOrder PaperIV.PaddedEquitableColouring

/-- Right translation is the permutation of the cyclic root index that is
selected by the phase-I averaging argument. -/
def rightMulEquiv (shift : I) : I ≃ I where
  toFun i := i * shift
  invFun i := i * shift⁻¹
  left_inv i := by simp [mul_assoc]
  right_inv i := by simp [mul_assoc]

/-- Every selected compatible phase-I base is a literal edge of the induced
exterior of the prescribed root. -/
theorem compatiblePaddedHostBase_subset_outsideEdges
    (P : Finset V) (z : V) (i : I) :
    PaperIV.RD09PaddedHostBase.compatiblePaddedHostBase G
        (exteriorGraph G P) I (exteriorEmbedding P) z i ⊆ outsideEdges G P := by
  intro e he
  have hepad := PaperIV.RD09PaddedHostBase.compatiblePaddedHostBase_subset
    (G := G) (H := exteriorGraph G P) (exteriorEmbedding P) z i he
  obtain ⟨d, hd, -, rfl⟩ :=
    PaperIV.RD09PaddedHostBase.mem_paddedHostBase.mp hepad
  apply Finset.mem_filter.mpr
  refine ⟨PaperIV.RD09LocalPhaseI.mem_graphEdges_map
    (fun _ _ h => exteriorEmbedding_hom (G := G) P h) hd, ?_⟩
  intro x hx
  obtain ⟨a, -, rfl⟩ := Sym2.mem_map.mp (Sym2.mem_toFinset.mp hx)
  exact a.2

/-- Consequently the number of literal phase-I triangles never exceeds the
number of exterior edges. -/
theorem card_multiLiftedPacking_le_outsideEdges
    (P : Finset V) (z : I → V) (E : I → Finset (Sym2 V))
    (hE : ∀ i, E i = PaperIV.RD09PaddedHostBase.compatiblePaddedHostBase G
      (exteriorGraph G P) I (exteriorEmbedding P) (z i) i)
    (hhub : IsMultiExteriorHub G z E) :
    (multiLiftedPacking z E).card ≤ (outsideEdges G P).card := by
  rw [card_multiLiftedPacking hhub]
  have hcard : (Finset.univ.biUnion E).card = ∑ i, (E i).card := by
    rw [Finset.card_biUnion]
    intro i _ j _ hij
    exact hhub.baseDisjoint i j hij
  rw [← hcard]
  apply Finset.card_le_card
  intro e he
  obtain ⟨i, -, hei⟩ := Finset.mem_biUnion.mp he
  rw [hE i] at hei
  exact compatiblePaddedHostBase_subset_outsideEdges P (z i) i hei

/-- Root-relative phase I with the physical root enumeration retained. -/
theorem exists_rooted_phaseI_with_L9_and_roots
    {P : Finset V} (O : Order G P)
    (r : I ≃ {x : V // x ∈ P})
    (hpalette : 40 * PaddedEquitableColouring.paddedPaletteSize (exteriorGraph G P) (Fintype.card I) ≤
      73 * Fintype.card I)
    (hwidth : 40 * ((exteriorGraph G P).cliqueNum - 1) ≤
      3 * Fintype.card I) :
    ∃ roots : I ≃ {x : V // x ∈ P},
      ∃ z : I → V, ∃ E : I → Finset (Sym2 V),
        (∀ i, z i = (roots i).1) ∧
        (∀ i, E i = PaperIV.RD09PaddedHostBase.compatiblePaddedHostBase G
          (exteriorGraph G P) I
          (exteriorEmbedding P) (z i) i) ∧
        IsMultiExteriorHub G z E ∧
        IsPacking G (multiLiftedPacking z E) ∧
        1600 * (outsideEdges G P).card ≤
          2920 * (multiLiftedPacking z E).card +
            219 * PaperIV.RootVocab.missingIncidences G P := by
  obtain ⟨shift, z, E, hz, hE, hhub, hpack, hL9⟩ :=
    exists_padded_phaseI_with_L9_and_roots O (exteriorEmbedding P) (rootVertex P r)
      (fun _ _ h => exteriorEmbedding_hom (G := G) P h)
      (fun _ _ h => exteriorEmbedding_reflect (G := G) P h)
      (rootVertex_injective P r) (rootVertex_mem P r)
      (exteriorEmbedding_not_mem P) hpalette hwidth
  let roots : I ≃ {x : V // x ∈ P} := (rightMulEquiv shift).trans r
  refine ⟨roots, z, E, ?_, hE, hhub, hpack, ?_⟩
  · intro i
    simpa [roots, rightMulEquiv, rootVertex] using hz i
  · rw [← card_graphEdges_exteriorGraph (G := G) P,
      ← card_missingIncidences_root_exterior (G := G) P r]
    exact hL9

/-- Phase I, now stated entirely with the root-relative physical ledgers
`outsideEdges` and `RootedGraph.missingIncidences`.  The only remaining
premises are the two explicit scalar range inequalities. -/
theorem exists_rooted_phaseI_with_L9
    {P : Finset V} (O : Order G P)
    (r : I ≃ {x : V // x ∈ P})
    (hpalette : 40 * PaddedEquitableColouring.paddedPaletteSize (exteriorGraph G P) (Fintype.card I) ≤
      73 * Fintype.card I)
    (hwidth : 40 * ((exteriorGraph G P).cliqueNum - 1) ≤
      3 * Fintype.card I) :
    ∃ z : I → V, ∃ E : I → Finset (Sym2 V),
      IsMultiExteriorHub G z E ∧
      IsPacking G (multiLiftedPacking z E) ∧
      1600 * (outsideEdges G P).card ≤
          2920 * (multiLiftedPacking z E).card +
            219 * PaperIV.RootVocab.missingIncidences G P := by
  obtain ⟨_, z, E, -, -, hhub, hpack, hL9⟩ :=
    exists_rooted_phaseI_with_L9_and_roots O r hpalette hwidth
  exact ⟨z, E, hhub, hpack, hL9⟩

end PhaseI

end PaperIV.RD09RootExteriorAdapter
