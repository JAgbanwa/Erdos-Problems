import CoreRepair
import PaperIV.EditMetric

namespace FixedDefectStability
open Finset
open scoped symmDiff

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Changing adjacency only on edges touching X costs at most |X|*|V| edits. -/
theorem editDist_le_touched_vertices (G J : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel J.Adj] (X : Finset V)
    (heq : ∀ a ∉ X, ∀ b ∉ X, G.Adj a b ↔ J.Adj a b) :
    PaperIV.EditMetric.editDist G.edgeFinset J.edgeFinset ≤ X.card*Fintype.card V := by
  have hsub : G.edgeFinset ∆ J.edgeFinset ⊆
      X.biUnion (fun x => (⊤ : SimpleGraph V).incidenceFinset x) := by
    intro e he
    induction e using Sym2.ind with
    | _ a b =>
      have hdiff : (G.Adj a b ∧ ¬J.Adj a b) ∨ (J.Adj a b ∧ ¬G.Adj a b) := by
        simpa only [mem_symmDiff, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using he
      have hab : a ≠ b := by
        rcases hdiff with h | h
        · exact h.1.ne
        · exact h.1.ne
      have hX : a ∈ X ∨ b ∈ X := by
        by_contra hh
        push_neg at hh
        rcases hdiff with h | h
        · exact h.2 ((heq a hh.1 b hh.2).mp h.1)
        · exact h.2 ((heq a hh.1 b hh.2).mpr h.1)
      have ht : s(a,b) ∈ (⊤ : SimpleGraph V).edgeSet := by
        simpa only [SimpleGraph.mem_edgeSet, SimpleGraph.top_adj] using hab
      rcases hX with ha | hb
      · refine mem_biUnion.2 ⟨a,ha,?_⟩
        rw [SimpleGraph.mem_incidenceFinset]
        exact ⟨ht,Sym2.mem_mk_left a b⟩
      · refine mem_biUnion.2 ⟨b,hb,?_⟩
        rw [SimpleGraph.mem_incidenceFinset]
        exact ⟨ht,Sym2.mem_mk_right a b⟩
  have h1 := card_le_card hsub
  have h2 := card_biUnion_le (s := X) (t := fun x => (⊤ : SimpleGraph V).incidenceFinset x)
  have h3 : ∑ x ∈ X, ((⊤ : SimpleGraph V).incidenceFinset x).card ≤
      X.card*Fintype.card V := by
    calc _ ≤ ∑ _x ∈ X, Fintype.card V := by
           apply sum_le_sum
           intro x _
           rw [SimpleGraph.card_incidenceFinset_eq_degree]
           exact ((⊤ : SimpleGraph V).degree_lt_card_verts x).le
         _ = _ := by simp
  exact h1.trans (h2.trans h3)

end FixedDefectStability
#print axioms FixedDefectStability.editDist_le_touched_vertices
