import PaperIV.RootedEliminationOrder
import PaperIV.RD09L1Adapter

/-!
# Rooted elimination orders discharge the RD09-L1 nesting hypothesis

This module is the narrow connector between the chordal structure proved in
`RootedEliminationOrder` and the geometric double count in `RD09L1Adapter`.
-/

namespace PaperIV.RD09RootedOrderAdapter

open PaperIV.Model PaperIV.RD09L1Adapter
open PaperIV.RootedEliminationOrder

variable {V A I : Type*} [Fintype V] [DecidableEq V]
variable [Fintype A] [DecidableEq A] [Fintype I]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable {H : SimpleGraph A} [DecidableRel H.Adj]

/-- Earlier endpoint of a core edge according to the rooted elimination order. -/
noncomputable def edgeEarlier {P : Finset V} (O : Order G P) (f : A ↪ V)
    (d : Sym2 A) : A :=
  if O.index (f d.out.1) < O.index (f d.out.2) then d.out.1 else d.out.2

/-- Later endpoint of a core edge according to the rooted elimination order. -/
noncomputable def edgeLater {P : Finset V} (O : Order G P) (f : A ↪ V)
    (d : Sym2 A) : A :=
  if O.index (f d.out.1) < O.index (f d.out.2) then d.out.2 else d.out.1

/-- Later core neighbours of `a`, using the ambient rooted order. -/
noncomputable def laterCoreNeighbors {P : Finset V} (O : Order G P)
    (f : A ↪ V) (H : SimpleGraph A) [DecidableRel H.Adj] (a : A) : Finset A :=
  Finset.univ.filter fun b => H.Adj a b ∧ O.index (f a) < O.index (f b)

theorem edge_eq_oriented {P : Finset V} (O : Order G P) (f : A ↪ V)
    (d : Sym2 A) : d = s(edgeEarlier O f d, edgeLater O f d) := by
  classical
  by_cases h : O.index (f d.out.1) < O.index (f d.out.2)
  · rw [edgeEarlier, edgeLater, if_pos h, if_pos h]
    simpa [Sym2.mk] using d.out_eq.symm
  · rw [edgeEarlier, edgeLater, if_neg h, if_neg h, Sym2.eq_swap]
    simpa [Sym2.mk] using d.out_eq.symm

theorem edgeEarlier_index_lt_edgeLater {P : Finset V} (O : Order G P)
    (f : A ↪ V) {d : Sym2 A} (hnd : ¬ d.IsDiag) :
    O.index (f (edgeEarlier O f d)) < O.index (f (edgeLater O f d)) := by
  classical
  have houtne : d.out.1 ≠ d.out.2 := by
    intro h
    apply hnd
    rw [← d.out_eq, Sym2.isDiag_iff_proj_eq]
    exact h
  have hidxne : O.index (f d.out.1) ≠ O.index (f d.out.2) := by
    intro h
    exact houtne (f.injective (O.index_injective h))
  unfold edgeEarlier edgeLater
  split_ifs with hlt
  · exact hlt
  · exact lt_of_le_of_ne (le_of_not_gt hlt) hidxne.symm

@[simp] theorem mem_laterCoreNeighbors {P : Finset V} (O : Order G P)
    (f : A ↪ V) {a b : A} :
    b ∈ laterCoreNeighbors O f H a ↔
      H.Adj a b ∧ O.index (f a) < O.index (f b) := by
  classical
  simp [laterCoreNeighbors]

theorem card_laterCoreNeighbors_le_maxDegree {P : Finset V} (O : Order G P)
    (f : A ↪ V) (a : A) :
    (laterCoreNeighbors O f H a).card ≤ H.maxDegree := by
  classical
  calc
    (laterCoreNeighbors O f H a).card ≤ (H.neighborFinset a).card :=
      Finset.card_le_card (by
        intro b hb
        rw [mem_laterCoreNeighbors] at hb
        simpa using hb.1)
    _ = H.degree a := SimpleGraph.card_neighborFinset_eq_degree H a
    _ ≤ H.maxDegree := H.degree_le_maxDegree a

/-- For an induced embedded core, later neighbours form a clique, so their
cardinality is controlled by clique number rather than maximum degree.  This
is the sharp width used by the RD09 charge. -/
theorem card_laterCoreNeighbors_le_cliqueNum_sub_one
    {P : Finset V} (O : Order G P) (f : A ↪ V)
    (hcore : ∀ a b : A, H.Adj a b → G.Adj (f a) (f b))
    (hreflect : ∀ a b : A, G.Adj (f a) (f b) → H.Adj a b)
    (a : A) :
    (laterCoreNeighbors O f H a).card ≤ H.cliqueNum - 1 := by
  classical
  let S := laterCoreNeighbors O f H a
  have haS : a ∉ S := by
    intro ha
    exact H.irrefl ((mem_laterCoreNeighbors O f).mp ha).1
  have hclique : H.IsClique (((insert a S : Finset A) : Set A)) := by
    intro x hx y hy hxy
    change x ∈ insert a S at hx
    change y ∈ insert a S at hy
    rw [Finset.mem_insert] at hx hy
    rcases hx with rfl | hx
    · rcases hy with rfl | hy
      · exact (hxy rfl).elim
      · exact ((mem_laterCoreNeighbors O f).mp hy).1
    · rcases hy with rfl | hy
      · exact (H.adj_comm _ _).mp ((mem_laterCoreNeighbors O f).mp hx).1
      · apply hreflect
        apply later_neighbors_isClique O (f a)
        · exact ⟨((mem_laterCoreNeighbors O f).mp hx).2,
            hcore _ _ ((mem_laterCoreNeighbors O f).mp hx).1⟩
        · exact ⟨((mem_laterCoreNeighbors O f).mp hy).2,
            hcore _ _ ((mem_laterCoreNeighbors O f).mp hy).1⟩
        · exact fun h => hxy (f.injective h)
  have hcard := hclique.card_le_cliqueNum
  have hinsert : (insert a S).card = S.card + 1 := by simp [haS]
  rw [hinsert] at hcard
  change S.card ≤ H.cliqueNum - 1
  omega

theorem edgeLater_mem_laterCoreNeighbors {P : Finset V} (O : Order G P)
    (f : A ↪ V) {d : Sym2 A} (hd : d ∈ graphEdges H) :
    edgeLater O f d ∈ laterCoreNeighbors O f H (edgeEarlier O f d) := by
  classical
  rw [mem_laterCoreNeighbors]
  constructor
  · have hedge : s(edgeEarlier O f d, edgeLater O f d) ∈ H.edgeSet := by
      rw [← edge_eq_oriented O f d, ← mem_graphEdges]
      exact hd
    rwa [SimpleGraph.mem_edgeSet] at hedge
  · exact edgeEarlier_index_lt_edgeLater O f
      (PaperIV.Model.not_isDiag_of_mem_graphEdges H hd)

/-- The PEO nesting condition required by `RD09L1Adapter` is automatic once
the core edge is oriented by a rooted elimination order. -/
theorem nesting_of_rooted_order
    {P : Finset V} (O : Order G P) (f : A ↪ V) (root : I → V)
    (earlier later : Sym2 A → A)
    (hroot : ∀ r, root r ∈ P)
    (houtEarlier : ∀ d ∈ graphEdges H, f (earlier d) ∉ P)
    (houtLater : ∀ d ∈ graphEdges H, f (later d) ∉ P)
    (hends : ∀ d ∈ graphEdges H, d = s(earlier d, later d))
    (horder : ∀ d ∈ graphEdges H, O.index (f (earlier d)) < O.index (f (later d)))
    (hedge : ∀ d ∈ graphEdges H, G.Adj (f (earlier d)) (f (later d))) :
    ∀ (r : I), ∀ d ∈ graphEdges H,
      ¬ IsCompatibleBase G (root r) (Sym2.map f d) →
        ¬ G.Adj (root r) (f (earlier d)) := by
  intro r d hd hbad hra
  have hea : G.Adj (f (earlier d)) (root r) :=
    (G.adj_comm (root r) (f (earlier d))).mp hra
  have hlr : G.Adj (f (later d)) (root r) :=
    root_neighbors_mono O (houtEarlier d hd) (houtLater d hd)
      (horder d hd) (hedge d hd) (hroot r) hea
  apply hbad
  rw [isCompatibleBase_iff]
  intro x hx
  rw [hends d hd] at hx
  simp only [Sym2.map_pair_eq, Sym2.mem_iff] at hx
  rcases hx with rfl | rfl
  · exact hra
  · exact (G.adj_comm (f (later d)) (root r)).mp hlr

/-- Complete structural package consumed by the L1 geometric charging lemma.
The width parameter is the canonical `H.maxDegree + 1`. -/
theorem rooted_order_geometry
    {P : Finset V} (O : Order G P) (f : A ↪ V) (root : I → V)
    (hroot : ∀ r, root r ∈ P)
    (hout : ∀ a : A, f a ∉ P)
    (hcore : ∀ a b : A, H.Adj a b → G.Adj (f a) (f b)) :
    (∀ d ∈ graphEdges H,
        d = s(edgeEarlier O f d, edgeLater O f d)) ∧
    (∀ d ∈ graphEdges H,
        edgeLater O f d ∈ laterCoreNeighbors O f H (edgeEarlier O f d)) ∧
    (∀ a : A, (laterCoreNeighbors O f H a).card ≤ (H.maxDegree + 1) - 1) ∧
    (∀ (r : I), ∀ d ∈ graphEdges H,
      ¬ IsCompatibleBase G (root r) (Sym2.map f d) →
        ¬ G.Adj (root r) (f (edgeEarlier O f d))) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro d hd
    exact edge_eq_oriented O f d
  · intro d hd
    exact edgeLater_mem_laterCoreNeighbors O f hd
  · intro a
    simpa using card_laterCoreNeighbors_le_maxDegree (H := H) O f a
  · apply nesting_of_rooted_order O f root (edgeEarlier O f) (edgeLater O f)
      hroot
      (fun d hd => hout (edgeEarlier O f d))
      (fun d hd => hout (edgeLater O f d))
      (fun d hd => edge_eq_oriented O f d)
      (fun d hd => edgeEarlier_index_lt_edgeLater O f
        (PaperIV.Model.not_isDiag_of_mem_graphEdges H hd))
    intro d hd
    exact hcore _ _ ((mem_laterCoreNeighbors O f).mp
      (edgeLater_mem_laterCoreNeighbors O f hd)).1

/-- Sharp induced-core version of `rooted_order_geometry`: the charge width
is `cliqueNum H - 1`, not `maxDegree H`. -/
theorem rooted_order_geometry_cliqueNum
    {P : Finset V} (O : Order G P) (f : A ↪ V) (root : I → V)
    (hroot : ∀ r, root r ∈ P)
    (hout : ∀ a : A, f a ∉ P)
    (hcore : ∀ a b : A, H.Adj a b → G.Adj (f a) (f b))
    (hreflect : ∀ a b : A, G.Adj (f a) (f b) → H.Adj a b) :
    (∀ d ∈ graphEdges H,
        d = s(edgeEarlier O f d, edgeLater O f d)) ∧
    (∀ d ∈ graphEdges H,
        edgeLater O f d ∈ laterCoreNeighbors O f H (edgeEarlier O f d)) ∧
    (∀ a : A, (laterCoreNeighbors O f H a).card ≤ H.cliqueNum - 1) ∧
    (∀ (r : I), ∀ d ∈ graphEdges H,
      ¬ IsCompatibleBase G (root r) (Sym2.map f d) →
        ¬ G.Adj (root r) (f (edgeEarlier O f d))) := by
  obtain ⟨hends, hlater, -, hnest⟩ :=
    rooted_order_geometry (H := H) O f root hroot hout hcore
  exact ⟨hends, hlater,
    card_laterCoreNeighbors_le_cliqueNum_sub_one O f hcore hreflect, hnest⟩

section Ledger

variable [DecidableEq I] [Nonempty I] [Group I]

/-- RD09-L1 with all PEO/orientation hypotheses eliminated.  The only inputs
left are the actual root/core embeddings and the injective colour selection. -/
theorem rd09L1_ledger_of_rooted_order
    {P : Finset V} (O : Order G P) (f : A ↪ V)
    (colourOf : I → Fin (H.maxDegree + 1)) (root : I → V)
    (hcore : ∀ a b : A, H.Adj a b → G.Adj (f a) (f b))
    (hrootInj : Function.Injective root)
    (hcolourInj : Function.Injective colourOf)
    (hroot : ∀ r, root r ∈ P)
    (hout : ∀ a : A, f a ∉ P) :
    ∃ s : I,
      ∃ z : I → V, ∃ E : I → Finset (Sym2 V),
        (∀ i, z i = root (i * s)) ∧
        (∀ i, E i = compatibleHostBase G H f colourOf (z i) i) ∧
        (∀ i, E i ⊆ PaperIV.RD09LocalPhaseI.hostBase H f colourOf i) ∧
        PaperIV.MultiHostTriangleLift.IsMultiExteriorHub G z E ∧
        PaperIV.Model.IsPacking G
          (PaperIV.MultiHostTriangleLift.multiLiftedPacking z E) ∧
        (PaperIV.MultiHostTriangleLift.multiLiftedPacking z E).card
            + ∑ i : I, incompatCount G H f colourOf (z i) i
          = ∑ i : I, (PaperIV.RD09LocalPhaseI.hostBase H f colourOf i).card ∧
        (PaperIV.MultiHostTriangleLift.multiLiftedPacking z E).card
          = (∑ i : I, (PaperIV.RD09LocalPhaseI.hostBase H f colourOf i).card)
              - ∑ i : I, incompatCount G H f colourOf (z i) i ∧
        Fintype.card I *
            ∑ i : I, (PaperIV.RD09LocalPhaseI.hostBase H f colourOf i).card
          ≤ Fintype.card I *
              (PaperIV.MultiHostTriangleLift.multiLiftedPacking z E).card
              + H.maxDegree * (missingIncidences G root f).card := by
  obtain ⟨hends, hlater, hwidth, hnest⟩ :=
    rooted_order_geometry (H := H) O f root hroot hout hcore
  have hrootcore : ∀ (r : I) (a : A), root r ≠ f a := by
    intro r a h
    have := hroot r
    rw [h] at this
    exact hout a this
  simpa using RD09L1Adapter.rd09L1_ledger f colourOf root hcore hrootInj
    hcolourInj hrootcore (H.maxDegree + 1) (edgeEarlier O f) (edgeLater O f)
    (laterCoreNeighbors O f H) hends hlater hwidth hnest

end Ledger

end PaperIV.RD09RootedOrderAdapter
