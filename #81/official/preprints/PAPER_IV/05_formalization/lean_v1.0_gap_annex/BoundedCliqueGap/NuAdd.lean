import BoundedCliqueGap.SteinerTools

/-
`BoundedCliqueGap.NuAdd` — declaration-level extract of the Route B
triangle-packing development.  Only the declarations in the constant cone of
`BoundedCliqueGap.chordal_gap_linear_cliqueFree` were kept (plus the few that
the retained sources need in order to elaborate); the module documentation
below is the original one and may advertise results that were pruned away.
-/

/-
# `ν₃` is superadditive over edge-disjoint subgraphs

A generic assembly tool: packings of pairwise edge-disjoint subgraphs of `G`
can be unioned into a packing of `G`, so `ν₃` adds up.  Unlike
`nu3_sum_disjoint_cliques` (which needs *vertex*-disjoint cliques) the pieces
here may share arbitrarily many vertices; only their edge sets must be
disjoint.
-/

namespace BoundedCliqueGap

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Superadditivity of `ν₃` over a family of pairwise edge-disjoint
subgraphs.** -/
theorem nu3_sum_le_of_edgeDisjoint {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (G : SimpleGraph V) (H : ι → SimpleGraph V)
    (hle : ∀ i ∈ s, H i ≤ G)
    (hdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∀ u v, (H i).Adj u v → ¬ (H j).Adj u v) :
    ∑ i ∈ s, nu3 (H i) ≤ nu3 G := by
  classical
  choose P hP hcard using fun i => exists_packing_card_eq_nu3 (H i)
  -- the endpoints of an edge of a triangle lie in the triangle
  have hends : ∀ (T : Finset V) (u v : V), s(u, v) ∈ triEdges T → u ∈ T ∧ v ∈ T := by
    intro T u v he
    obtain ⟨a, ha, b, hb, hab, hee⟩ := mem_triEdges_iff.1 he
    rw [Sym2.eq_iff] at hee
    rcases hee with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨ha, hb⟩
    · exact ⟨hb, ha⟩
  -- no triangle can belong to two of the pieces
  have hdisjP : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (P i) (P j) := by
    intro i hi j hj hij
    rw [Finset.disjoint_left]
    intro T hTi hTj
    have h3 : 1 < T.card := by rw [((hP i).1 T hTi).1]; norm_num
    obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.1 h3
    exact hdisj i hi j hj hij u v (((hP i).1 T hTi).2 u hu v hv huv)
      (((hP j).1 T hTj).2 u hu v hv huv)
  set Q := s.biUnion P with hQ
  have hQpack : IsPacking G Q := by
    constructor
    · intro T hT
      obtain ⟨i, hi, hTi⟩ := Finset.mem_biUnion.1 hT
      exact ⟨((hP i).1 T hTi).1, fun u hu v hv huv => hle i hi (((hP i).1 T hTi).2 u hu v hv huv)⟩
    · intro T hT T' hT' hne
      obtain ⟨i, hi, hTi⟩ := Finset.mem_biUnion.1 hT
      obtain ⟨j, hj, hTj⟩ := Finset.mem_biUnion.1 hT'
      by_cases hij : i = j
      · subst hij
        exact (hP i).2 T hTi T' hTj hne
      · rw [Finset.disjoint_left]
        intro e heT heT'
        obtain ⟨u, hu, v, hv, huv, rfl⟩ := mem_triEdges_iff.1 heT
        obtain ⟨hu', hv'⟩ := hends T' u v heT'
        exact hdisj i hi j hj hij u v (((hP i).1 T hTi).2 u hu v hv huv)
          (((hP j).1 T' hTj).2 u hu' v hv' huv)
  calc ∑ i ∈ s, nu3 (H i) = ∑ i ∈ s, (P i).card :=
        Finset.sum_congr rfl (fun i _ => (hcard i).symm)
    _ = Q.card := (Finset.card_biUnion (fun i hi j hj hij => hdisjP i hi j hj hij)).symm
    _ ≤ nu3 G := card_le_nu3 hQpack

/-! ## Axiom audit -/

end BoundedCliqueGap
