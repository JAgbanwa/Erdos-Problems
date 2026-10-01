import VertexEditBound
import PaperIV.DefectComparatorGraph

namespace FixedDefectStability
open Finset A4S1.TerminalPacking A4S1.IndepAll
open PaperIV.SplitEdgeCount PaperIV.DefectComparatorGraph PaperIV.EditMetric
open scoped symmDiff

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem missing_cross_card {S H : Finset V} (hd : Disjoint S H) :
    (crossEdges S H \ G.edgeFinset).card = S.card*H.card-crossCount G S H := by
  have hb : ((S ×ˢ H).filter fun p => ¬G.Adj p.1 p.2).card =
      (crossEdges S H \ G.edgeFinset).card := by
    apply card_bij (fun p _ => s(p.1,p.2))
    · intro p hp
      obtain ⟨⟨hpS,hpH⟩,hn⟩ := (show (p.1 ∈ S ∧ p.2 ∈ H) ∧ ¬G.Adj p.1 p.2 by
        simpa only [mem_filter,mem_product] using hp)
      exact mem_sdiff.2 ⟨mem_crossEdges.2 ⟨p.1,hpS,p.2,hpH,rfl⟩,
        by simpa only [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet] using hn⟩
    · rintro ⟨a,b⟩ hp ⟨c,d⟩ hq heq
      have hp' := mem_product.1 (mem_filter.1 hp).1
      have hq' := mem_product.1 (mem_filter.1 hq).1
      rcases Sym2.eq_iff.1 heq with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · rfl
      · exact False.elim (disjoint_left.1 hd hp'.1 hq'.2)
    · intro e he
      obtain ⟨he,hn⟩ := mem_sdiff.1 he
      obtain ⟨a,ha,b,hb,rfl⟩ := mem_crossEdges.1 he
      refine ⟨(a,b),mem_filter.2 ⟨mem_product.2 ⟨ha,hb⟩,?_⟩,rfl⟩
      simpa only [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet] using hn
  have hh := card_filter_add_card_filter_not (s := S ×ˢ H) (fun p => G.Adj p.1 p.2)
  rw [hb,card_product] at hh
  unfold crossCount
  omega

/-- Full-graph cost before moving the exceptional/extra defect vertices into the exterior.
The C-clique is already present in G; all missing cross edges are paid explicitly. -/
theorem template_distance_before_shift (S H W C : Finset V)
    (hSH : Disjoint S H) (hC : C ⊆ S) (hcl : G.IsClique (C : Set V))
    (hcover : ∀ x, x ∈ S ∨ x ∈ H ∨ x ∈ W) :
    editDist G.edgeFinset (defSplitGraph C (S \ C) H).edgeFinset ≤
      ((inEdges G S).card-C.card.choose 2) + (inEdges G H).card +
      (S.card*H.card-crossCount G S H) + W.card*Fintype.card V := by
  let T := defSplitGraph C (S \ C) H
  let I := W.biUnion (fun x => (⊤ : SimpleGraph V).incidenceFinset x)
  have hCS : C ∪ (S \ C) = S := union_sdiff_of_subset hC
  have htouch {a b : V} (hab : a ≠ b) (hw : a ∈ W ∨ b ∈ W) : s(a,b) ∈ I := by
    have ht : s(a,b) ∈ (⊤ : SimpleGraph V).edgeSet := by simpa using hab
    rcases hw with ha | hb
    · exact mem_biUnion.2 ⟨a,ha,by rw [SimpleGraph.mem_incidenceFinset]; exact ⟨ht,Sym2.mem_mk_left a b⟩⟩
    · exact mem_biUnion.2 ⟨b,hb,by rw [SimpleGraph.mem_incidenceFinset]; exact ⟨ht,Sym2.mem_mk_right a b⟩⟩
  have hdel : G.edgeFinset \ T.edgeFinset ⊆
      ((inEdges G S \ inEdges G C) ∪ inEdges G H) ∪ I := by
    intro e he
    induction e using Sym2.ind with
    | _ a b =>
      obtain ⟨hg,ht⟩ := mem_sdiff.1 he
      have hg' : G.Adj a b := by simpa using hg
      have ht' : ¬T.Adj a b := by simpa using ht
      by_cases haW : a ∈ W
      · exact mem_union_right _ (htouch hg'.ne (Or.inl haW))
      by_cases hbW : b ∈ W
      · exact mem_union_right _ (htouch hg'.ne (Or.inr hbW))
      have ha : a ∈ S ∨ a ∈ H := by
        rcases hcover a with hh | hh | hh
        · exact Or.inl hh
        · exact Or.inr hh
        · exact False.elim (haW hh)
      have hb : b ∈ S ∨ b ∈ H := by
        rcases hcover b with hh | hh | hh
        · exact Or.inl hh
        · exact Or.inr hh
        · exact False.elim (hbW hh)
      rcases ha with ha | ha <;> rcases hb with hb | hb
      · apply mem_union_left
        apply mem_union_left
        refine mem_sdiff.2 ⟨mk_mem_inEdges.2 ⟨hg',ha,hb⟩,?_⟩
        intro heC
        obtain ⟨_,haC,hbC⟩ := mk_mem_inEdges.1 heC
        exact ht' ⟨hg'.ne,Or.inl ⟨haC,hbC⟩⟩
      · exact False.elim (ht' ⟨hg'.ne,Or.inr (Or.inl ⟨hCS.symm ▸ ha,hb⟩)⟩)
      · exact False.elim (ht' ⟨hg'.ne,Or.inr (Or.inr ⟨ha,hCS.symm ▸ hb⟩)⟩)
      · exact mem_union_left _ (mem_union_right _ (mk_mem_inEdges.2 ⟨hg',ha,hb⟩))
  have hadd : T.edgeFinset \ G.edgeFinset ⊆ crossEdges S H \ G.edgeFinset := by
    intro e he
    induction e using Sym2.ind with
    | _ a b =>
      obtain ⟨ht,hg⟩ := mem_sdiff.1 he
      have ht' : T.Adj a b := by simpa using ht
      refine mem_sdiff.2 ⟨?_,hg⟩
      rcases ht'.2 with hh | hh | hh
      · exact False.elim (hg (by simpa using hcl hh.1 hh.2 ht'.1))
      · exact mem_crossEdges.2 ⟨a,hCS ▸ hh.1,b,hh.2,rfl⟩
      · exact mem_crossEdges.2 ⟨b,hCS ▸ hh.2,a,hh.1,Sym2.eq_swap⟩
  have hI : I.card ≤ W.card*Fintype.card V := by
    have h1 := card_biUnion_le (s := W) (t := fun x => (⊤ : SimpleGraph V).incidenceFinset x)
    have h2 : ∑ x ∈ W, ((⊤ : SimpleGraph V).incidenceFinset x).card ≤ W.card*Fintype.card V := by
      calc _ ≤ ∑ _x ∈ W, Fintype.card V := by
             apply sum_le_sum
             intro x _
             rw [SimpleGraph.card_incidenceFinset_eq_degree]
             exact ((⊤ : SimpleGraph V).degree_lt_card_verts x).le
           _ = _ := by simp
    exact h1.trans h2
  have hd := (card_le_card hdel).trans (card_union_le _ _)
  have hd' := card_union_le (inEdges G S \ inEdges G C) (inEdges G H)
  have ha := card_le_card hadd
  have hcore : (inEdges G S \ inEdges G C).card = (inEdges G S).card-C.card.choose 2 := by
    rw [card_sdiff_of_subset (inEdges_mono hC),card_inEdges_of_isClique hcl]
  rw [hcore] at hd'
  rw [missing_cross_card hSH] at ha
  change (G.edgeFinset ∆ T.edgeFinset).card ≤ _
  change ((G.edgeFinset \ T.edgeFinset) ∪ (T.edgeFinset \ G.edgeFinset)).card ≤ _
  have hh := card_union_le (G.edgeFinset \ T.edgeFinset) (T.edgeFinset \ G.edgeFinset)
  omega

end FixedDefectStability
#print axioms FixedDefectStability.missing_cross_card
#print axioms FixedDefectStability.template_distance_before_shift
