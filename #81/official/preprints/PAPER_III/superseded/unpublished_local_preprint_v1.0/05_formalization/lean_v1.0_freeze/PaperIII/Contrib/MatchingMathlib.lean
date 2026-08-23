/-
Copyright (c) 2026 Paper III contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import PaperIII.DiracMatching

/-!
# Dirac-type matchings from high minimum degree

This file records, in idiomatic `SimpleGraph.Subgraph` matching vocabulary, that a finite
simple graph whose minimum degree is at least half the number of vertices contains a
(near-)perfect matching.  These are the graph-theoretic analogues of Dirac's theorem for
Hamiltonicity.

## Main results

* `SimpleGraph.exists_isPerfectMatching_of_minDegree`: if `V` has an even number of vertices
  and `|V| ≤ 2 · δ(G)`, then `G` has a perfect matching (`Subgraph.IsPerfectMatching`).
* `SimpleGraph.exists_isMatching_compl_singleton_of_minDegree`: if `V` has an odd number of
  vertices and `|V| ≤ 2 · δ(G) + 1`, then `G` has a matching covering all but exactly one
  vertex, i.e. a matching `M` whose vertex set is the complement `{w}ᶜ` of a single vertex
  `w` (a *near-perfect* matching).

## Implementation notes

The proofs bridge to the development in `PaperIII.DiracMatching`, which establishes the
core statements through Mathlib's Tutte theorem (`SimpleGraph.tutte`): a minimum degree of
at least `|V| / 2` rules out any Tutte violator in the even case, while the odd case is
reduced to the even case by adjoining a universal apex vertex.  Here we merely re-express
those results with the standard `Subgraph.IsMatching` / `Subgraph.IsPerfectMatching` API and
in the `SimpleGraph` namespace, so that they are ready for upstreaming to Mathlib.
-/

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Dirac-type perfect matching (even case).**  A finite simple graph on an even number of
vertices whose minimum degree satisfies `|V| ≤ 2 · δ(G)` has a perfect matching. -/
theorem exists_isPerfectMatching_of_minDegree (G : SimpleGraph V) [DecidableRel G.Adj]
    (heven : Even (Fintype.card V))
    (hδ : Fintype.card V ≤ 2 * G.minDegree) :
    ∃ M : G.Subgraph, M.IsPerfectMatching :=
  PaperIII.exists_isPerfectMatching_of_minDegree G heven hδ

/-- **Dirac-type near-perfect matching (odd case).**  A finite simple graph on an odd number
of vertices whose minimum degree satisfies `|V| ≤ 2 · δ(G) + 1` has a matching covering all
but exactly one vertex: there is a vertex `w` and a matching `M` with vertex set `{w}ᶜ`. -/
theorem exists_isMatching_compl_singleton_of_minDegree (G : SimpleGraph V) [DecidableRel G.Adj]
    (hodd : Odd (Fintype.card V))
    (hδ : Fintype.card V ≤ 2 * G.minDegree + 1) :
    ∃ (M : G.Subgraph) (w : V), M.IsMatching ∧ M.verts = {w}ᶜ := by
  classical
  obtain ⟨M, hM, hcard⟩ := PaperIII.exists_near_perfect_matching G hδ
  have heven : Even M.verts.toFinset.card := hM.even_card
  have hle : M.verts.toFinset.card ≤ Fintype.card V := by
    simpa using Finset.card_le_univ M.verts.toFinset
  have hcompl : M.verts.toFinsetᶜ.card = 1 := by
    rw [Finset.card_compl, Set.toFinset_card]
    rw [Set.toFinset_card] at hle hcard heven
    rcases hodd with ⟨k, hk⟩
    rcases heven with ⟨t, ht⟩
    omega
  obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hcompl
  refine ⟨M, w, hM, ?_⟩
  ext x
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
  constructor
  · rintro hx rfl
    have hxc : x ∈ M.verts.toFinsetᶜ := by rw [hw]; simp
    simp only [Finset.mem_compl, Set.mem_toFinset] at hxc
    exact hxc hx
  · intro hx
    by_contra hxv
    have hxc : x ∈ M.verts.toFinsetᶜ := by
      simp only [Finset.mem_compl, Set.mem_toFinset]; exact hxv
    rw [hw, Finset.mem_singleton] at hxc
    exact hx hxc

end SimpleGraph
