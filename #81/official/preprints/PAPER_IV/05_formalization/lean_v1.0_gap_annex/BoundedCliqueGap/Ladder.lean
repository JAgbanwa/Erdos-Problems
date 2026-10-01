import BoundedCliqueGap.Defs

/-
`BoundedCliqueGap.Ladder` — declaration-level extract of the Route B
triangle-packing development.  Only the declarations in the constant cone of
`BoundedCliqueGap.chordal_gap_linear_cliqueFree` were kept (plus the few that
the retained sources need in order to elaborate); the module documentation
below is the original one and may advertise results that were pruned away.
-/

/-
# Eslabón-4 ladder, rungs N1 and N2

* N1 — consumable forms of the fractional Tuza bound `ν* ≤ 2ν`
  (`gap_le_nu3`, `value_le_of_nu3_le`).
* N2 — the local fractional peeling bound: the fractional mass of the
  triangles through a vertex `v` is at most `deg(v)/2` (`mass_at_vertex_le`),
  and consequently a fractional packing can be peeled at `v`, losing at most
  `deg(v)/2` of its value (`exists_peel`).

The file also sets up two tools that are reused on the higher rungs:
`FracPacking.restrict` (restricting a fractional packing to a subfamily of
triangles that survives in a smaller graph) and monotonicity of `nu3`.
-/

namespace BoundedCliqueGap

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Generic tools -/

omit [Fintype V] in
/-- Every edge of a triangle of `G` is an edge of `G`. -/
lemma mem_edgeSet_of_mem_triEdges {G : SimpleGraph V} {T : Finset V}
    (hT : IsTriangle G T) {e : Sym2 V} (he : e ∈ triEdges T) : e ∈ G.edgeSet := by
  obtain ⟨u, hu, v, hv, huv, rfl⟩ := mem_triEdges_iff.1 he
  exact hT.2 u hu v hv huv

namespace FracPacking

variable {G : SimpleGraph V}

open scoped Classical in
/-- Restricting a fractional packing of `G` to the triangles satisfying `p`,
viewed as a fractional packing of a graph `H` in which all the surviving
support triangles are triangles. -/
noncomputable def restrict (F : FracPacking G) (p : Finset V → Prop)
    (H : SimpleGraph V) (hH : ∀ T, F.x T ≠ 0 → p T → IsTriangle H T) :
    FracPacking H where
  x := fun T => if p T then F.x T else 0
  nonneg T := by split_ifs; exacts [F.nonneg T, le_refl 0]
  supp T hT := by
    by_cases hp : p T
    · rw [if_pos hp] at hT; exact hH T hT hp
    · rw [if_neg hp] at hT; exact absurd rfl hT
  edge_le_one e he := by
    have hsub : (Finset.univ.filter fun T =>
          e ∈ triEdges T ∧ (if p T then F.x T else 0) ≠ 0) ⊆
        Finset.univ.filter fun T => e ∈ triEdges T ∧ F.x T ≠ 0 := by
      intro T hT
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hT ⊢
      refine ⟨hT.1, ?_⟩
      by_cases hp : p T
      · rw [if_pos hp] at hT; exact hT.2
      · rw [if_neg hp] at hT; exact absurd rfl hT.2
    calc ∑ T ∈ Finset.univ.filter (fun T =>
              e ∈ triEdges T ∧ (if p T then F.x T else 0) ≠ 0),
            (if p T then F.x T else 0)
        = ∑ T ∈ Finset.univ.filter (fun T =>
              e ∈ triEdges T ∧ (if p T then F.x T else 0) ≠ 0), F.x T := by
          refine Finset.sum_congr rfl (fun T hT => ?_)
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hT
          by_cases hp : p T
          · rw [if_pos hp]
          · rw [if_neg hp] at hT ⊢; exact absurd rfl hT.2
      _ ≤ ∑ T ∈ Finset.univ.filter (fun T => e ∈ triEdges T ∧ F.x T ≠ 0), F.x T :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => F.nonneg i)
      _ ≤ 1 := F.edge_le_one e he

open scoped Classical in
lemma restrict_value (F : FracPacking G) (p : Finset V → Prop) (H : SimpleGraph V)
    (hH : ∀ T, F.x T ≠ 0 → p T → IsTriangle H T) :
    (F.restrict p H hH).value =
      ∑ T ∈ Finset.univ.filter (fun T => F.x T ≠ 0 ∧ p T), F.x T := by
  have hset : (Finset.univ.filter fun T => (F.restrict p H hH).x T ≠ 0) =
      Finset.univ.filter fun T => F.x T ≠ 0 ∧ p T := by
    ext T
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, restrict]
    by_cases hp : p T <;> simp [hp]
  rw [value, hset]
  refine Finset.sum_congr rfl (fun T hT => ?_)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hT
  show (if p T then F.x T else 0) = F.x T
  rw [if_pos hT.2]

end FracPacking

/-! ## Rung N1 — sparse dischargers, consumable form -/

/-! ## Rung N2 — the fractional peeling bound -/

namespace FracPacking

variable {G : SimpleGraph V}

end FracPacking

end BoundedCliqueGap
