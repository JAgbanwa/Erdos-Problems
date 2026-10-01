import PaperIV.ClassCopyEdit
import PaperIV.Model
import PaperIV.RootEdgeSplit
import PaperIV.SplitUniformIncidence

/-!
# Literal edit accounting for a regularized split root

Let `S = K_C \vee I_(V \ C)` be a complete-split comparator and let `P \subseteq C`
be a clique retained as the physical root.  The RD09 defect is the disjoint
union of

* graph edges with both endpoints outside `P`, and
* absent root--outside spokes.

Every such defect edge is either an actual edit between `G` and `S`, or is
incident with a vertex of `C \ P`.  Consequently its cardinality is at most
`editDist(G,S) + |C \ P| |V|`.  This is the graph-theoretic bridge used by
the scalar calibration; it contains no asymptotic or fractional assumption.
-/

namespace PaperIV.RD09SplitEditAccount

open Finset
open scoped symmDiff
open PaperIV.EditMetric PaperIV.ClassCopyEdit PaperIV.SplitUniformIncidence
open PaperIV.Model
open PaperIV.RootVocab

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Missing root spokes represented as unordered physical edges. -/
noncomputable def missingSpokeEdges (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finset V) : Finset (Sym2 V) :=
  (Gᶜ.interedges P (outsideVertices P)).image fun xy => s(xy.1, xy.2)

theorem card_missingSpokeEdges (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finset V) :
    (missingSpokeEdges G P).card = missingIncidences G P := by
  classical
  rw [missingSpokeEdges, PaperIV.RootVocab.missingIncidences_eq_card_interedges]
  refine Finset.card_image_of_injOn ?_
  rw [← PaperIV.RootVocab.crossingPairs_eq_interedges]
  exact PaperIV.RootVocab.crossingPairs_edge_injOn Gᶜ P

theorem outsideEdges_disjoint_missingSpokeEdges
    (G : SimpleGraph V) [DecidableRel G.Adj] (P : Finset V) :
    Disjoint (outsideEdges G P) (missingSpokeEdges G P) := by
  classical
  rw [Finset.disjoint_left]
  intro e hout hmiss
  obtain ⟨he, hsub⟩ := Finset.mem_filter.mp hout
  obtain ⟨⟨x, y⟩, hxy, hEq⟩ := Finset.mem_image.mp hmiss
  have hxP : x ∈ P := (Rel.mem_interedges_iff.mp hxy).1
  have hxPair : x ∈ s(x, y).toFinset :=
    Sym2.mem_toFinset.mpr (Sym2.mem_mk_left x y)
  have hxOut : x ∈ outsideVertices P := hsub (hEq ▸ hxPair)
  exact (mem_outsideVertices.mp hxOut) hxP

/-- The literal union whose cardinality is the RD09 account `m + A`. -/
noncomputable def defectEdges (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finset V) : Finset (Sym2 V) :=
  outsideEdges G P ∪ missingSpokeEdges G P

theorem card_defectEdges (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finset V) :
    (defectEdges G P).card =
      (outsideEdges G P).card + missingIncidences G P := by
  classical
  rw [defectEdges, Finset.card_union_of_disjoint
    (outsideEdges_disjoint_missingSpokeEdges G P), card_missingSpokeEdges]

private theorem missingSpoke_mem_split
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {C P : Finset V} (hPC : P ⊆ C) {e : Sym2 V}
    (he : e ∈ missingSpokeEdges G P) :
    e ∈ (splitGraph C (Finset.univ \ C)).edgeSet := by
  classical
  obtain ⟨⟨x, y⟩, hxy, rfl⟩ := Finset.mem_image.mp he
  have hi := Rel.mem_interedges_iff.mp hxy
  have hxC : x ∈ C := hPC hi.1
  have hne : x ≠ y := by
    intro h
    have hc := hi.2.2
    simp only [SimpleGraph.compl_adj] at hc
    exact hc.1 h
  rw [SimpleGraph.mem_edgeSet]
  by_cases hyC : y ∈ C
  · exact splitGraph_adj_inner hxC hyC hne
  · have hd : Disjoint C (Finset.univ \ C) := by
      rw [Finset.disjoint_left]
      simp
    exact splitGraph_adj_cross hd hxC (by simp [hyC])

/-- Set-level form of the edit account.  The auxiliary graph `S` is required
to be literally the complete-split comparator on `C`; making it an argument
keeps the statement independent of the chosen decidability proof for its
adjacency relation. -/
theorem defectEdges_subset_edit_union_incident
    (G S : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel S.Adj]
    {C P : Finset V} (hPC : P ⊆ C)
    (hS : ∀ x y, S.Adj x y ↔ (splitGraph C (Finset.univ \ C)).Adj x y) :
    defectEdges G P ⊆
      (G.edgeFinset ∆ S.edgeFinset) ∪ incident (C \ P) := by
  classical
  intro e he
  rcases Finset.mem_union.mp he with hout | hmiss
  · have heG : e ∈ G.edgeFinset := (Finset.mem_filter.mp hout).1
    by_cases heS : e ∈ S.edgeFinset
    · apply Finset.mem_union.mpr (Or.inr ?_)
      induction e using Sym2.ind with
      | _ x y =>
        have houtSub := (Finset.mem_filter.mp hout).2
        have hxNotP : x ∉ P :=
          mem_outsideVertices.mp (houtSub (by simp))
        have hyNotP : y ∉ P :=
          mem_outsideVertices.mp (houtSub (by simp))
        have hsAdj : S.Adj x y := by
          simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using heS
        have hsplit := (hS x y).mp hsAdj
        rcases (splitGraph_adj_iff.mp hsplit).2 with hCC | hCH | hHC
        · refine Finset.mem_biUnion.mpr ⟨x, ?_, ?_⟩
          · exact Finset.mem_sdiff.mpr ⟨hCC.1, hxNotP⟩
          · simp [PaperIV.ClassCopyEdit.star]
        · refine Finset.mem_biUnion.mpr ⟨x, ?_, ?_⟩
          · exact Finset.mem_sdiff.mpr ⟨hCH.1, hxNotP⟩
          · simp [PaperIV.ClassCopyEdit.star]
        · refine Finset.mem_biUnion.mpr ⟨y, ?_, ?_⟩
          · exact Finset.mem_sdiff.mpr ⟨hHC.2, hyNotP⟩
          · simp [PaperIV.ClassCopyEdit.star]
    · apply Finset.mem_union.mpr (Or.inl ?_)
      exact Finset.mem_symmDiff.mpr (Or.inl ⟨heG, heS⟩)
  · apply Finset.mem_union.mpr (Or.inl ?_)
    have heSplit : e ∈ (splitGraph C (Finset.univ \ C)).edgeSet :=
      missingSpoke_mem_split G hPC hmiss
    have heS : e ∈ S.edgeFinset := by
      rw [SimpleGraph.mem_edgeFinset]
      revert heSplit
      refine Sym2.inductionOn e ?_
      intro x y hxy
      rw [SimpleGraph.mem_edgeSet] at hxy ⊢
      exact (hS x y).mpr hxy
    have heNotG : e ∉ G.edgeFinset := by
      intro heG
      obtain ⟨⟨x, y⟩, hxy, hEq⟩ := Finset.mem_image.mp hmiss
      have hcomp := (Rel.mem_interedges_iff.mp hxy).2.2
      simp only [SimpleGraph.compl_adj] at hcomp
      have hadj : G.Adj x y := by
        rw [← SimpleGraph.mem_edgeSet, ← SimpleGraph.mem_edgeFinset]
        exact hEq.symm ▸ heG
      exact hcomp.2 hadj
    exact Finset.mem_symmDiff.mpr (Or.inr ⟨heS, heNotG⟩)

/-- Cardinal form used by `NearH1Calibration`: the entire physical defect is
paid once by the edit set and once by the vertices removed from the comparator
core. -/
theorem outside_add_missing_le_edit_add_removed_mul
    (G S : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel S.Adj]
    {C P : Finset V} (hPC : P ⊆ C)
    (hS : ∀ x y, S.Adj x y ↔ (splitGraph C (Finset.univ \ C)).Adj x y) :
    (outsideEdges G P).card + missingIncidences G P ≤
      editDist G.edgeFinset S.edgeFinset + (C \ P).card * Fintype.card V := by
  classical
  rw [← card_defectEdges G P]
  calc
    (defectEdges G P).card
        ≤ ((G.edgeFinset ∆ S.edgeFinset) ∪ incident (C \ P)).card :=
      Finset.card_le_card (defectEdges_subset_edit_union_incident G S hPC hS)
    _ ≤ (G.edgeFinset ∆ S.edgeFinset).card + (incident (C \ P)).card :=
      Finset.card_union_le _ _
    _ ≤ editDist G.edgeFinset S.edgeFinset +
        (C \ P).card * Fintype.card V := by
      unfold editDist
      exact Nat.add_le_add_left (card_incident_le (C \ P)) _

/-- Rationally normalized form, ready to be passed to
`NearH1Calibration.calibration`. -/
theorem outside_add_missing_cast_le
    (G S : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel S.Adj]
    {C P : Finset V} (hPC : P ⊆ C)
    (hS : ∀ x y, S.Adj x y ↔ (splitGraph C (Finset.univ \ C)).Adj x y) :
    (((outsideEdges G P).card + missingIncidences G P : ℕ) : ℚ) ≤
      (editDist G.edgeFinset S.edgeFinset : ℚ) +
        ((C \ P).card : ℚ) * (Fintype.card V : ℚ) := by
  exact_mod_cast outside_add_missing_le_edit_add_removed_mul G S hPC hS

end PaperIV.RD09SplitEditAccount
