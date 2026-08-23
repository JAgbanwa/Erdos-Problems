/-
# Yuster (edge-based) — the edge triangle-degree equals the graph codegree

Standalone, Mathlib-only. The foundational identity for the EDGE-based near-regularity (the encoding
whose matchings are edge-disjoint triangle packings, i.e. `ν₃`). The hypergraph degree of an edge `e`
in `triangleHypergraphE G` is the number of triangles containing `e`, which — for `e = {a,b}` — equals
the number of common neighbours of `a` and `b` (each triangle on `e` is `e ∪ {c}` for a common
neighbour `c`). This is the edge-analogue of `triangleHypergraph_degree_eq_edgesInside`, and the anchor
for the codegree-based near-regularity that the `ν₃` nibble consumes.

* `triangleHypergraphE_degree_eq_codegree` — `deg_E(e) = #{c : c adjacent to every vertex of e}`.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.YusterEdge

open Finset SimpleGraph Hypergraph

namespace Nibble.YusterE

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **Edge triangle-degree = common-neighbour count.** For an edge `e` (a `2`-clique), the number of
triangles containing `e` equals the number of common neighbours of `e`'s vertices. Bijection:
`c ↦ insert c e` maps common neighbours to the triangles on `e`. -/
theorem triangleHypergraphE_degree_eq_codegree {e : Finset V} (he : e ∈ G.cliqueFinset 2) :
    degree (triangleHypergraphE G) e
      = (Finset.univ.filter (fun c => ∀ x ∈ e, G.Adj x c)).card := by
  have he2 : G.IsNClique 2 e := (SimpleGraph.mem_cliqueFinset_iff).mp he
  rw [triangleHypergraphE_degree]
  symm
  refine Finset.card_bij (fun c _ => insert c e) ?_ ?_ ?_
  · intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
    have hce : c ∉ e := fun hcin => (hc c hcin).ne rfl
    have hclique : G.IsNClique 3 (insert c e) := by
      refine ⟨?_, ?_⟩
      · intro x hx y hy hxy
        simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hx hy
        rcases hx with rfl | hx <;> rcases hy with rfl | hy
        · exact absurd rfl hxy
        · exact (hc y hy).symm
        · exact hc x hx
        · exact he2.isClique hx hy hxy
      · rw [Finset.card_insert_of_notMem hce, he2.card_eq]
    rw [Finset.mem_filter, SimpleGraph.mem_cliqueFinset_iff]
    refine ⟨hclique, ?_⟩
    rw [Finset.mem_powersetCard]
    exact ⟨Finset.subset_insert _ _, he2.card_eq⟩
  · intro c1 hc1 c2 hc2 heq
    dsimp only at heq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc1 hc2
    have h1 : c1 ∉ e := fun h => (hc1 c1 h).ne rfl
    have hmem : c1 ∈ insert c2 e := by rw [← heq]; exact Finset.mem_insert_self c1 e
    rcases Finset.mem_insert.mp hmem with h | h
    · exact h
    · exact absurd h h1
  · intro t ht
    rw [Finset.mem_filter, SimpleGraph.mem_cliqueFinset_iff, Finset.mem_powersetCard] at ht
    obtain ⟨htclique, hsub, _⟩ := ht
    have hcard : (t \ e).card = 1 := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub, htclique.card_eq, he2.card_eq]
    obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hcard
    have hcmem : c ∈ t \ e := hc ▸ Finset.mem_singleton_self c
    have hct : c ∈ t := (Finset.mem_sdiff.mp hcmem).1
    have hce : c ∉ e := (Finset.mem_sdiff.mp hcmem).2
    refine ⟨c, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro x hx
      exact htclique.isClique (hsub hx) hct (fun h => hce (h ▸ hx))
    · have hun : t \ e ∪ e = t := Finset.sdiff_union_of_subset hsub
      rw [hc, Finset.singleton_union] at hun
      exact hun

end Nibble.YusterE
