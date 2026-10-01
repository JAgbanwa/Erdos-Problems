import TemplateDistance

namespace FixedDefectStability
open Finset A4S1.TerminalPacking PaperIV.DefectComparatorGraph PaperIV.EditMetric

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Move W and the surplus defect vertices M into the exterior. Only edges
touching those vertices change; neither the clique nor the other adjacencies do. -/
theorem template_shift_distance (S H W C D : Finset V)
    (hC : C ⊆ S) (hD : D ⊆ S) :
    editDist (defSplitGraph C (S \ C) H).edgeFinset
      (defSplitGraph C D (H ∪ W ∪ (S \ (C ∪ D)))).edgeFinset ≤
      (W.card + (S \ (C ∪ D)).card)*Fintype.card V := by
  let M := S \ (C ∪ D)
  have hCS : C ∪ (S \ C)=S := union_sdiff_of_subset hC
  have hsub : C ∪ D ⊆ S := union_subset hC hD
  have heq : ∀ a ∉ W ∪ M, ∀ b ∉ W ∪ M,
      (defSplitGraph C (S \ C) H).Adj a b ↔
        (defSplitGraph C D (H ∪ W ∪ M)).Adj a b := by
    intro a ha b hb
    have haW : a ∉ W := fun hh => ha (mem_union_left _ hh)
    have hbW : b ∉ W := fun hh => hb (mem_union_left _ hh)
    have haM : a ∉ M := fun hh => ha (mem_union_right _ hh)
    have hbM : b ∉ M := fun hh => hb (mem_union_right _ hh)
    have hsame (x : V) (hx : x ∉ M) : x ∈ C ∪ D ↔ x ∈ S := by
      constructor
      · exact fun hh => hsub hh
      · intro hh
        by_contra hn
        exact hx (mem_sdiff.2 ⟨hh,hn⟩)
    simp only [defSplitGraph_adj_iff,hCS,hsame a haM,hsame b hbM]
    simp only [mem_union,haW,hbW,haM,hbM,or_false]
  have hh := editDist_le_touched_vertices (defSplitGraph C (S \ C) H)
    (defSplitGraph C D (H ∪ W ∪ M)) (W ∪ M) heq
  have hc := Nat.mul_le_mul_right (Fintype.card V) (card_union_le W M)
  exact hh.trans hc

variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Literal full-graph account: internal deletions, exterior edges, missing links,
and the incidences of exceptional or shifted vertices. -/
theorem template_distance_after_shift (S H W C D : Finset V)
    (hSH : Disjoint S H) (hC : C ⊆ S) (hD : D ⊆ S)
    (hcl : G.IsClique (C : Set V))
    (hcover : ∀ x, x ∈ S ∨ x ∈ H ∨ x ∈ W) :
    editDist G.edgeFinset (defSplitGraph C D (H ∪ W ∪ (S \ (C ∪ D)))).edgeFinset ≤
      ((inEdges G S).card-C.card.choose 2) + (inEdges G H).card +
      (S.card*H.card-crossCount G S H) +
      (2*W.card+(S \ (C ∪ D)).card)*Fintype.card V := by
  have h1 := template_distance_before_shift (G := G) S H W C hSH hC hcl hcover
  have h2 := template_shift_distance S H W C D hC hD
  have h3 := editDist_triangle G.edgeFinset (defSplitGraph C (S \ C) H).edgeFinset
    (defSplitGraph C D (H ∪ W ∪ (S \ (C ∪ D)))).edgeFinset
  nlinarith only [h1,h2,h3]

end FixedDefectStability
#print axioms FixedDefectStability.template_shift_distance
#print axioms FixedDefectStability.template_distance_after_shift
