/-
# Nibble — Yuster assembly (start) : the triangle hypergraph

Standalone, Mathlib-only. The **Yuster route** de-axiomatizes AX1 (`ν₃*(G) − ν₃(G) = o(n²)`) by
applying the nibble theorem (`NibbleTheorem`, the T3 interface) to the *triangle hypergraph* of a
graph `G`: its 3-cliques form a 3-uniform hypergraph whose matchings are exactly the triangle
packings of `G`. Under the regularity/counting hypotheses (Szemerédi + partite counting), that
hypergraph is near-regular with small codegree, so the nibble rounds the fractional triangle packing
to an integral one within `o(n²)`.

This file starts the assembly with the T3-*independent* foundation: the triangle hypergraph and its
`3`-uniformity. The full route (Y1–Y7) is roadmapped below.

ROADMAP (Y1–Y7, consuming `NibbleTheorem` as a black box):
* Y1 Szemerédi regularity partition of `G` (✓ Mathlib `SimpleGraph.Regularity`).
* Y2 partite triangle counting (uniform #triangles through each edge in regular pairs).
* Y3 the triangle hypergraph is near-regular with small codegree (from Y1+Y2).
* Y4 fractional triangle packing `ν₃*` and integral `ν₃`; weak duality.
* Y5 apply `NibbleTheorem` to the triangle hypergraph ⇒ integral packing `≥ (1-β)·ν₃*`.
* Y6 assemble ⇒ `ν₃* − ν₃ ≤ β·ν₃* + o(n²)` ⇒ AX1.
* Y7 tidy to the Paper III statement of AX1.
-/
import Nibble.Basic
import Nibble.Interface
import Mathlib.Combinatorics.SimpleGraph.Clique

open Hypergraph SimpleGraph

namespace Nibble.Yuster

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The **triangle hypergraph** of `G`: its 3-cliques, viewed as a hypergraph. Its matchings are the
triangle packings of `G`; the nibble (T3) applied here rounds the fractional packing to integral. -/
def triangleHypergraph : Finset (Finset V) := G.cliqueFinset 3

/-- **Y (foundation) — the triangle hypergraph is 3-uniform.** -/
theorem triangleHypergraph_uniform : IsUniform (triangleHypergraph G) 3 := by
  intro e he
  rw [triangleHypergraph, SimpleGraph.mem_cliqueFinset_iff] at he
  exact he.card_eq

/-- **Y2 — codegree of the triangle hypergraph is bounded by common neighbours.**
For distinct `u ≠ v`, every triangle through both is `{u, v, w}` for a common neighbour `w`, so the
number of triangles containing the pair is at most the number of common neighbours. (The diagonal
`u = v` version is *false* — an Aristotle-verified counterexample on `K₅` gives `codegree 0 0 = 6`
against `4` common neighbours — hence the `u ≠ v` hypothesis.) This feeds Y3 (small codegree). -/
theorem triangleHypergraph_codegree_le {u v : V} (huv : u ≠ v) :
    codegree (triangleHypergraph G) u v
      ≤ (G.neighborFinset u ∩ G.neighborFinset v).card := by
  rw [codegree]
  have hsubset : (triangleHypergraph G).filter (fun e => u ∈ e ∧ v ∈ e)
      ⊆ (G.neighborFinset u ∩ G.neighborFinset v).image (fun w => ({w, u, v} : Finset V)) := by
    intro e he
    rw [Finset.mem_filter, triangleHypergraph, SimpleGraph.mem_cliqueFinset_iff] at he
    obtain ⟨hclique, hu, hv⟩ := he
    have hsub : ({u, v} : Finset V) ⊆ e := by
      intro x hx
      rcases Finset.mem_insert.mp hx with h | h
      · exact h ▸ hu
      · exact (Finset.mem_singleton.mp h) ▸ hv
    have hcard : (e \ {u, v}).card = 1 := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub, hclique.card_eq,
        Finset.card_pair huv]
    obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hcard
    have hwmem : w ∈ e \ {u, v} := hw ▸ Finset.mem_singleton_self w
    have hwe : w ∈ e := (Finset.mem_sdiff.mp hwmem).1
    have hwuv : w ∉ ({u, v} : Finset V) := (Finset.mem_sdiff.mp hwmem).2
    have hwu : w ≠ u := fun h => hwuv (by simp [h])
    have hwv : w ≠ v := fun h => hwuv (by simp [h])
    have heq : e = {w, u, v} := by
      have hu' := Finset.sdiff_union_of_subset hsub
      rw [hw] at hu'
      rw [← hu', Finset.singleton_union]
    have hadju : G.Adj u w :=
      hclique.isClique (Finset.mem_coe.mpr hu) (Finset.mem_coe.mpr hwe) (fun h => hwu h.symm)
    have hadjv : G.Adj v w :=
      hclique.isClique (Finset.mem_coe.mpr hv) (Finset.mem_coe.mpr hwe) (fun h => hwv h.symm)
    refine Finset.mem_image.mpr ⟨w, ?_, heq.symm⟩
    rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset, SimpleGraph.mem_neighborFinset]
    exact ⟨hadju, hadjv⟩
  exact (Finset.card_le_card hsubset).trans Finset.card_image_le

/-- **Y3 (degree side) — degree of the triangle hypergraph ≤ `C(deg v, 2)`.** Each triangle through
`v` is `{v, a, b}` with `a, b` distinct neighbours of `v`; erasing `v` injects triangles-through-`v`
into `2`-subsets of `N(v)`. So the number of triangles through `v` is at most `binom(deg v, 2)`.
Together with `triangleHypergraph_codegree_le` this gives the near-regularity/codegree data Y3 needs. -/
theorem triangleHypergraph_degree_le (v : V) :
    degree (triangleHypergraph G) v ≤ (G.neighborFinset v).card.choose 2 := by
  rw [Hypergraph.degree, ← Finset.card_powersetCard 2 (G.neighborFinset v)]
  refine Finset.card_le_card_of_injOn (fun e => e.erase v) ?_ ?_
  · intro e he
    simp only [Finset.mem_coe, Finset.mem_filter, triangleHypergraph,
      SimpleGraph.mem_cliqueFinset_iff] at he
    obtain ⟨hclique, hv⟩ := he
    simp only [Finset.mem_coe, Finset.mem_powersetCard]
    refine ⟨fun a ha => ?_, ?_⟩
    · have hae : a ∈ e := Finset.mem_of_mem_erase ha
      have hav : a ≠ v := Finset.ne_of_mem_erase ha
      rw [SimpleGraph.mem_neighborFinset]
      exact hclique.isClique (Finset.mem_coe.mpr hv) (Finset.mem_coe.mpr hae) (fun h => hav h.symm)
    · rw [Finset.card_erase_of_mem hv, hclique.card_eq]
  · intro e he f hf hef
    simp only [Finset.mem_coe, Finset.mem_filter] at he hf
    have hef' : e.erase v = f.erase v := hef
    have := congrArg (insert v) hef'
    rwa [Finset.insert_erase he.2, Finset.insert_erase hf.2] at this

end Nibble.Yuster
