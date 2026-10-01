module

public import RequestProject.AS.Defs

/-!
# Edit distance as a count of ordered pairs

`2 · editDist G G'` is the number of ordered pairs `(u, v)` on which `G` and `G'` disagree.
-/

@[expose] public section

open Finset

open scoped Classical symmDiff

namespace AlonShapira

/-- Disagreement indicator of two graphs at an ordered pair. -/
noncomputable def disagree {n : ℕ} (G G' : SimpleGraph (Fin n)) (u v : Fin n) : ℝ :=
  if (G.Adj u v ↔ G'.Adj u v) then 0 else 1

theorem two_mul_editDist {n : ℕ} (G G' : SimpleGraph (Fin n)) :
    2 * (editDist G G' : ℝ) = ∑ u, ∑ v, disagree G G' u v := by
  set D := G ∆ G' with hD
  have hadj : ∀ u v, D.Adj u v ↔ ¬ (G.Adj u v ↔ G'.Adj u v) := by
    intro u v
    simp only [hD, symmDiff_def, SimpleGraph.sup_adj, SimpleGraph.sdiff_adj]
    tauto
  have hE : D.edgeFinset = symmDiff G.edgeFinset G'.edgeFinset := by
    ext e
    induction e using Sym2.ind with
    | _ u v =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, hadj, Finset.mem_symmDiff,
        SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
        SimpleGraph.mem_edgeSet]
      tauto
  have h2 := D.sum_degrees_eq_twice_card_edges
  unfold editDist
  rw [← hE]
  have : (∑ v, (D.degree v : ℝ)) = ∑ u, ∑ v, disagree G G' u v := by
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter,
      Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl fun v _ => ?_
    unfold disagree
    by_cases h : D.Adj u v
    · rw [if_pos h, if_neg ((hadj u v).1 h)]
    · rw [if_neg h, if_pos (not_not.1 (fun hh => h ((hadj u v).2 hh)))]
  rw [← this]
  exact_mod_cast h2.symm

end AlonShapira
