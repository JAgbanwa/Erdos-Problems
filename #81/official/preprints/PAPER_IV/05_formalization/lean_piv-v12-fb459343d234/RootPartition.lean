import TemplateShift

namespace FixedDefectStability
open Finset A4S1.TerminalPacking PaperIV.DefectComparatorGraph PaperIV.EditMetric

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Retain exactly s defect vertices and move the surplus to the exterior.
The clique is preserved as a clique of the original graph. -/
theorem exists_root_partition (s r : ℕ) (S H W C : Finset V)
    (hSH : Disjoint S H) (hSW : Disjoint S W)
    (hcover : ∀ x, x ∈ S ∨ x ∈ H ∨ x ∈ W)
    (hC : C ⊆ S) (hcl : G.IsClique (C : Set V))
    (hcard : C.card+s+r=S.card) (htwo : 2 ≤ C.card)
    (hwindow : 2*C.card+s ≤ Fintype.card V) :
    ∃ D J : Finset V,
      Disjoint C D ∧ Disjoint C J ∧ Disjoint D J ∧
      (∀ x, x ∈ C ∨ x ∈ D ∨ x ∈ J) ∧ D.card=s ∧
      2 ≤ C.card ∧ C.card ≤ J.card ∧
      editDist G.edgeFinset (defSplitGraph C D J).edgeFinset ≤
        ((inEdges G S).card-C.card.choose 2) + (inEdges G H).card +
        (S.card*H.card-crossCount G S H) + (2*W.card+r)*Fintype.card V := by
  have hdiff : (S \ C).card=s+r := by rw [card_sdiff_of_subset hC]; omega
  obtain ⟨D,hD,hDcard⟩ := exists_subset_card_eq (show s ≤ (S \ C).card by omega)
  have hDS : D ⊆ S := hD.trans sdiff_subset
  have hCD : Disjoint C D := by
    rw [disjoint_left]
    intro x hx hd
    exact (mem_sdiff.1 (hD hd)).2 hx
  let M := S \ (C ∪ D)
  let J := H ∪ W ∪ M
  have hM : M.card=r := by
    dsimp [M]
    rw [card_sdiff_of_subset (union_subset hC hDS),card_union_of_disjoint hCD,hDcard]
    omega
  have hCJ : Disjoint C J := by
    rw [disjoint_left]
    intro x hx hj
    have hxS := hC hx
    simp only [J, M, mem_union, mem_sdiff] at hj
    rcases hj with (hh | hw) | ⟨_,hn⟩
    · exact (disjoint_left.1 hSH) hxS hh
    · exact (disjoint_left.1 hSW) hxS hw
    · exact hn (Or.inl hx)
  have hDJ : Disjoint D J := by
    rw [disjoint_left]
    intro x hx hj
    have hxS := hDS hx
    simp only [J, M, mem_union, mem_sdiff] at hj
    rcases hj with (hh | hw) | ⟨_,hn⟩
    · exact (disjoint_left.1 hSH) hxS hh
    · exact (disjoint_left.1 hSW) hxS hw
    · exact hn (Or.inr hx)
  have hcov : ∀ x, x ∈ C ∨ x ∈ D ∨ x ∈ J := by
    intro x
    rcases hcover x with hs | hh | hw
    · by_cases hc : x ∈ C
      · exact Or.inl hc
      · by_cases hd : x ∈ D
        · exact Or.inr (Or.inl hd)
        · exact Or.inr (Or.inr (mem_union_right _ (mem_sdiff.2
            ⟨hs,by simpa only [mem_union,not_or] using And.intro hc hd⟩)))
    · exact Or.inr (Or.inr (mem_union_left _ (mem_union_left _ hh)))
    · exact Or.inr (Or.inr (mem_union_left _ (mem_union_right _ hw)))
  have huniv : C ∪ D ∪ J = univ := by
    ext x
    simp only [mem_union,mem_univ,iff_true]
    rcases hcov x with hc | hd | hj
    · exact Or.inl (Or.inl hc)
    · exact Or.inl (Or.inr hd)
    · exact Or.inr hj
  have htotal : C.card+s+J.card=Fintype.card V := by
    have hh := congrArg Finset.card huniv
    rw [card_union_of_disjoint (disjoint_union_left.2 ⟨hCJ,hDJ⟩),
      card_union_of_disjoint hCD,card_univ,hDcard] at hh
    exact hh
  refine ⟨D,J,hCD,hCJ,hDJ,hcov,hDcard,htwo,by omega,?_⟩
  have hh := template_distance_after_shift (G := G) S H W C D hSH hC hDS hcl hcover
  simpa only [← hM] using hh

end FixedDefectStability
#print axioms FixedDefectStability.exists_root_partition
