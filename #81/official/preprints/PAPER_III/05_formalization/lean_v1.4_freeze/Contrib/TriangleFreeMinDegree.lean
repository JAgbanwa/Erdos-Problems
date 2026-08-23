/-
# Mantel-type leaf: a triangle-free graph has a vertex of degree `≤ n/2`

A triangle-free (`CliqueFree 3`) graph on a nonempty finite vertex set has a vertex of degree at most
half the order (stated as `2·deg v ≤ |V|`) — the degree half of Mantel's theorem. Two adjacent
vertices have disjoint neighborhoods in a triangle-free graph, so `deg u + deg v ≤ n`, and the smaller
of the two degrees is `≤ n/2`.

* `Contrib.TriangleFree.exists_low_degree_of_triangleFree`.

Sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib

namespace Contrib.TriangleFree

open SimpleGraph Finset

/-- **Mantel-type leaf.** If `G` is triangle-free (`CliqueFree 3`) on a nonempty finite
vertex set, some vertex has degree at most `|V|/2` (stated as `2·deg v ≤ |V|`). -/
theorem exists_low_degree_of_triangleFree {V : Type*} [Fintype V] [DecidableEq V]
    [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.CliqueFree 3) :
    ∃ v : V, 2 * G.degree v ≤ Fintype.card V := by
  let v : V := Classical.choice ‹Nonempty V›
  by_cases hv : G.neighborFinset v = ∅
  · refine ⟨v, ?_⟩
    rw [← G.card_neighborFinset_eq_degree, hv]
    simp
  · have hvn : (G.neighborFinset v).Nonempty := Finset.nonempty_iff_ne_empty.mpr hv
    obtain ⟨u, hu⟩ := hvn
    have huv : G.Adj v u := (G.mem_neighborFinset v u).mp hu
    have hdisj : Disjoint (G.neighborFinset u) (G.neighborFinset v) := by
      rw [Finset.disjoint_left]
      intro w hwu hwv
      have huw : G.Adj u w := (G.mem_neighborFinset u w).mp hwu
      have hvw : G.Adj v w := (G.mem_neighborFinset v w).mp hwv
      exact hG {u, v, w}
        ((SimpleGraph.is3Clique_iff).2 ⟨u, v, w, huv.symm, huw, hvw, rfl⟩)
    have hsum : G.degree u + G.degree v ≤ Fintype.card V := by
      rw [← G.card_neighborFinset_eq_degree, ← G.card_neighborFinset_eq_degree,
        ← Finset.card_union_of_disjoint hdisj, ← Finset.card_univ]
      exact Finset.card_le_card (Finset.subset_univ _)
    rcases le_total (G.degree u) (G.degree v) with huvdeg | hvudeg
    · exact ⟨u, by omega⟩
    · exact ⟨v, by omega⟩

end Contrib.TriangleFree
