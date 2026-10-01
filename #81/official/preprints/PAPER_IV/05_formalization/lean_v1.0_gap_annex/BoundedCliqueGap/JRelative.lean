import BoundedCliqueGap.Shell

/-
`BoundedCliqueGap.JRelative` — declaration-level extract of the Route B
triangle-packing development.  Only the declarations in the constant cone of
`BoundedCliqueGap.chordal_gap_linear_cliqueFree` were kept (plus the few that
the retained sources need in order to elaborate); the module documentation
below is the original one and may advertise results that were pruned away.
-/

/-
# Rung J2 — the RELATIVE shell: reserved edges at unit cost

Two general facts about `ν₃` and edge covers, and the relative form of the
shell theorem.

* `nu3_le_card_of_edgeCover` — if every triangle of `G` uses an edge of `D`,
  then `ν₃ G ≤ |D|` (the integral companion of `value_le_card_of_edgeCover`).
* `nu3_le_nu3_deleteEdges_add_card` — **reservation costs at most one per
  reserved edge**: deleting a set `R` of edge slots decreases `ν₃` by at most
  `|R|`.
* `shell_gap_rel` — the shell gap theorem in which a prescribed set `R` of
  edge slots is RESERVED (the integral packing produced may not use them),
  the reservation being charged at exactly `1` per reserved edge:
  `value ≤ ν₃(shell ∖ R) + 10·(κ − |S₀|) + (1/2)·Σᵢ pᵢsᵢ + |R|`.
* `shell_gap_rel_linear` — its linear form under the cross-mass bound.

This is what the clique-tree accounting needs: a separator edge can be
reserved at one of its two incident levels, and the level that gives it up
pays `1` for it, once.
-/

namespace BoundedCliqueGap

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The sets `triEdges T ∩ D`, for `T` ranging over an edge-disjoint family
each of whose members meets `D`, are nonempty and pairwise disjoint subsets of
`D`; hence the family has at most `|D|` members. -/
private lemma card_le_card_of_meets {G : SimpleGraph V} {P : Finset (Finset V)}
    (hP : IsPacking G P) (D : Finset (Sym2 V))
    (hmeet : ∀ T ∈ P, ((triEdges T) ∩ D).Nonempty) : P.card ≤ D.card := by
  classical
  have hdisj : ∀ T ∈ P, ∀ T' ∈ P, T ≠ T' →
      Disjoint (triEdges T ∩ D) (triEdges T' ∩ D) := by
    intro T hT T' hT' hne
    exact Finset.disjoint_of_subset_left Finset.inter_subset_left
      (Finset.disjoint_of_subset_right Finset.inter_subset_left (hP.2 T hT T' hT' hne))
  have hcard : P.card ≤ ∑ T ∈ P, (triEdges T ∩ D).card := by
    refine le_trans (le_of_eq (Finset.card_eq_sum_ones P)) (Finset.sum_le_sum (fun T hT => ?_))
    exact Finset.card_pos.2 (hmeet T hT)
  have hbi : ∑ T ∈ P, (triEdges T ∩ D).card = (P.biUnion (fun T => triEdges T ∩ D)).card :=
    (Finset.card_biUnion (fun T hT T' hT' hne => hdisj T hT T' hT' hne)).symm
  have hsub : P.biUnion (fun T => triEdges T ∩ D) ⊆ D := by
    intro e he
    obtain ⟨T, -, heT⟩ := Finset.mem_biUnion.1 he
    exact (Finset.mem_inter.1 heT).2
  calc P.card ≤ ∑ T ∈ P, (triEdges T ∩ D).card := hcard
    _ = (P.biUnion (fun T => triEdges T ∩ D)).card := hbi
    _ ≤ D.card := Finset.card_le_card hsub

/-- **Reservation costs at most one per reserved edge.**  Forbidding the edge
slots of `R` costs at most `|R|` triangles. -/
theorem nu3_le_nu3_deleteEdges_add_card (G : SimpleGraph V) (R : Finset (Sym2 V)) :
    nu3 G ≤ nu3 (G.deleteEdges ↑R) + R.card := by
  classical
  obtain ⟨P, hP, hcard⟩ := exists_packing_card_eq_nu3 G
  set P1 : Finset (Finset V) := P.filter (fun T => ∀ e ∈ triEdges T, e ∉ R) with hP1
  set P2 : Finset (Finset V) := P.filter (fun T => ¬ ∀ e ∈ triEdges T, e ∉ R) with hP2
  have hsplit : P1.card + P2.card = P.card := by
    rw [hP1, hP2]; exact Finset.card_filter_add_card_filter_not ..
  -- the triangles avoiding `R` form a packing of the reduced graph
  have hP1pack : IsPacking (G.deleteEdges ↑R) P1 := by
    constructor
    · intro T hT
      obtain ⟨hTP, hTR⟩ := Finset.mem_filter.1 hT
      refine ⟨(hP.1 T hTP).1, fun u hu v hv huv => ?_⟩
      rw [SimpleGraph.deleteEdges_adj]
      exact ⟨(hP.1 T hTP).2 u hu v hv huv,
        fun hmem => hTR s(u, v) (mk_mem_triEdges hu hv huv) (Finset.mem_coe.1 hmem)⟩
    · intro T hT T' hT' hne
      exact hP.2 T (Finset.mem_filter.1 hT).1 T' (Finset.mem_filter.1 hT').1 hne
  -- the triangles meeting `R` are at most `|R|` in number
  have hP2card : P2.card ≤ R.card := by
    refine card_le_card_of_meets ⟨fun T hT => hP.1 T (Finset.mem_filter.1 hT).1,
      fun T hT T' hT' hne => hP.2 T (Finset.mem_filter.1 hT).1 T'
        (Finset.mem_filter.1 hT').1 hne⟩ R (fun T hT => ?_)
    have hTR := (Finset.mem_filter.1 hT).2
    push_neg at hTR
    obtain ⟨e, heT, heR⟩ := hTR
    exact ⟨e, Finset.mem_inter.2 ⟨heT, heR⟩⟩
  have h1 : P1.card ≤ nu3 (G.deleteEdges ↑R) := card_le_nu3 hP1pack
  omega

section ShellRel

variable {kappa t m : ℕ} (S0 : Finset (Fin kappa)) (terr : Fin t → Fin m)
  (S : Fin m → Finset (Fin kappa))

end ShellRel

/-! ## Axiom audit -/

end BoundedCliqueGap
