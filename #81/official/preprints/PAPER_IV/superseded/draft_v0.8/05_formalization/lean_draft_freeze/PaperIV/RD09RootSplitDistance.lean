import PaperIV.RD09SplitEditAccount

/-! # Exact distance paid by the RD09 root accounts -/

namespace PaperIV.RD09RootSplitDistance

open Finset
open scoped symmDiff
open PaperIV.EditMetric PaperIV.SplitUniformIncidence
open PaperIV.RD09SplitEditAccount
open PaperIV.RootVocab

variable {V : Type*} [Fintype V] [DecidableEq V]

local instance (P : Finset V) :
    DecidableRel (splitGraph P (outsideVertices P)).Adj := by
  intro x y
  unfold splitGraph
  infer_instance

/-- For a clique root, every edit to its complete-split comparator is either
an exterior graph edge or a missing root--outside spoke. -/
theorem symmDiff_subset_defectEdges
    (G : SimpleGraph V) [DecidableRel G.Adj] (P : Finset V)
    (hP : G.IsClique (P : Set V)) :
    G.edgeFinset ∆ (splitGraph P (outsideVertices P)).edgeFinset ⊆
      defectEdges G P := by
  classical
  intro e he
  rcases Finset.mem_symmDiff.mp he with he | he
  · rcases he with ⟨heG, heS⟩
    apply Finset.mem_union.mpr
    left
    induction e using Sym2.ind with
    | _ x y =>
      have hGxy : G.Adj x y := by
        simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using heG
      have hne : x ≠ y := G.ne_of_adj hGxy
      have hx : x ∉ P := by
        intro hx
        by_cases hy : y ∈ P
        · apply heS
          rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
          exact splitGraph_adj_inner hx hy hne
        · apply heS
          rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
          have hd : Disjoint P (outsideVertices P) := by
            rw [Finset.disjoint_left]
            simp [outsideVertices]
          exact splitGraph_adj_cross hd hx (by simp [outsideVertices, hy])
      have hy : y ∉ P := by
        intro hy
        apply heS
        rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
        have hd : Disjoint P (outsideVertices P) := by
          rw [Finset.disjoint_left]
          simp [outsideVertices]
        exact (splitGraph_adj_cross hd hy (by simp [outsideVertices, hx])).symm
      apply Finset.mem_filter.mpr
      refine ⟨heG, ?_⟩
      intro z hz
      simp only [Sym2.toFinset_mk_eq, Finset.mem_insert,
        Finset.mem_singleton] at hz
      rcases hz with rfl | rfl <;> simp [outsideVertices, hx, hy]
  · rcases he with ⟨heS, heG⟩
    apply Finset.mem_union.mpr
    right
    induction e using Sym2.ind with
    | _ x y =>
      have hSxy : (splitGraph P (outsideVertices P)).Adj x y := by
        simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using heS
      have hnG : ¬ G.Adj x y := by
        simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using heG
      rcases (splitGraph_adj_iff.mp hSxy).2 with hPP | hPO | hOP
      · exact False.elim (hnG (hP hPP.1 hPP.2 hSxy.1))
      · apply Finset.mem_image.mpr
        refine ⟨(x, y), ?_, rfl⟩
        exact Rel.mem_interedges_iff.mpr
          ⟨hPO.1, hPO.2, by
            rw [SimpleGraph.compl_adj]
            exact ⟨hSxy.1, hnG⟩⟩
      · apply Finset.mem_image.mpr
        refine ⟨(y, x), ?_, Sym2.eq_swap⟩
        exact Rel.mem_interedges_iff.mpr
          ⟨hOP.2, hOP.1, by
            rw [SimpleGraph.compl_adj]
            exact ⟨hSxy.1.symm, fun h => hnG h.symm⟩⟩

/-- Cardinal form consumed by S02. -/
theorem editDist_splitRoot_le_accounts
    (G : SimpleGraph V) [DecidableRel G.Adj] (P : Finset V)
    (hP : G.IsClique (P : Set V)) :
    editDist G.edgeFinset (splitGraph P (outsideVertices P)).edgeFinset ≤
      (outsideEdges G P).card + missingIncidences G P := by
  classical
  unfold editDist
  rw [← card_defectEdges G P]
  exact Finset.card_le_card (symmDiff_subset_defectEdges G P hP)

end PaperIV.RD09RootSplitDistance
