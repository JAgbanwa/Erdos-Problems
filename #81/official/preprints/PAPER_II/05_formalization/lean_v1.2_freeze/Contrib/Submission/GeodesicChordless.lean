/-
Copyright (c) 2026 Juan Pablo Traverso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso
-/
import Mathlib

/-!
# Geodesics and induced paths are chordless

This module collects a few general (non-chordal) facts about **shortest walks** and **induced
paths** in a simple graph. The overarching theme is that a shortest walk is *chordless*: any two
of its vertices that happen to be adjacent in the graph are already joined by an edge that appears
on the walk. As a consequence, from any walk staying inside a set `K` one can extract an *induced*
(chordless) path staying inside `K`.

These lemmas are self-contained, depend only on Mathlib, and are useful independently of chordal
graph theory (they are candidates for a separate Mathlib PR).

## Main results
* `SimpleGraph.geodesic_adj_imp_edge` — on a shortest walk, any two adjacent support vertices are
  joined by an edge of the walk.
* `SimpleGraph.exists_induced_path_of_walk` — from a walk staying inside `K`, extract an induced
  (chordless) path staying inside `K`.
-/

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- From a `G`-walk `x → y` all of whose vertices lie in `K`, the endpoints are reachable in the
induced subgraph `G.induce K`. -/
theorem reachable_induce_of_walk (K : Set V) {x y : V}
    (hx : x ∈ K) (hy : y ∈ K) (P : G.Walk x y) (hsupp : ∀ w ∈ P.support, w ∈ K) :
    (G.induce K).Reachable ⟨x, hx⟩ ⟨y, hy⟩ := by
  induction' P with x y hxy ih
  · exact ⟨SimpleGraph.Walk.nil⟩
  · rename_i p hp
    specialize hp (by aesop) hy (by aesop)
    exact SimpleGraph.Reachable.trans (SimpleGraph.Adj.reachable <| by aesop) hp

/-- **Geodesics are chordless.** On a shortest walk, any two adjacent support vertices are joined
by an edge of the walk. -/
theorem geodesic_adj_imp_edge {u v : V}
    (p : G.Walk u v) (hp : p.length = G.dist u v)
    {s t : V} (hs : s ∈ p.support) (ht : t ∈ p.support) (hadj : G.Adj s t) :
    s(s, t) ∈ p.edges := by
  by_contra h
  obtain ⟨q₁, q₂, hq⟩ : ∃ q₁ : G.Walk u s, ∃ q₂ : G.Walk s v, p = q₁.append q₂ := by
    grind +suggestions
  -- If `t ∈ q₁.support`, split `q₁` at `t`; otherwise `t ∈ q₂.support`, split `q₂` at `t`.
  by_cases ht₁ : t ∈ q₁.support
  · obtain ⟨q₁', q₂', hq'⟩ : ∃ q₁' : G.Walk u t, ∃ q₂' : G.Walk t s, q₁ = q₁'.append q₂' := by
      grind +suggestions
    simp_all +decide [SimpleGraph.Walk.edges_append]
    have h_dist : G.dist u v ≤ q₁'.length + 1 + q₂.length := by
      have h_dist : G.dist u v ≤ (q₁'.append (SimpleGraph.Walk.cons hadj.symm q₂)).length := by
        exact SimpleGraph.dist_le _
      exact h_dist.trans (by simp +decide [add_assoc])
    have h_dist : q₂'.length ≥ 2 := by
      rcases q₂' with (_ | ⟨_, _, q₂'⟩) <;> simp_all +decide
    grind
  · obtain ⟨q₂₁, q₂₂, hq₂⟩ : ∃ q₂₁ : G.Walk s t, ∃ q₂₂ : G.Walk t v, q₂ = q₂₁.append q₂₂ := by
      grind +suggestions
    have h_dist : G.dist u v ≤ q₁.length + 1 + q₂₂.length := by
      have h_dist : G.dist u v ≤
          (q₁.append (SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil)).length + q₂₂.length := by
        have h_walk : ∃ w : G.Walk u v, w.length =
            (q₁.append (SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil)).length + q₂₂.length := by
          exact ⟨(q₁.append (SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil)).append q₂₂,
            by simp +decide⟩
        exact h_walk.choose_spec ▸ SimpleGraph.dist_le _
      exact h_dist.trans (by simp +decide [SimpleGraph.Walk.length_append])
    rcases q₂₁ with (_ | ⟨_, _, q₂₁⟩) <;> simp_all +decide [SimpleGraph.Walk.length]
    linarith

/-- From a `G`-walk `x → y` staying inside `K`, extract an induced (chordless) `G`-path `x → y`
staying inside `K`. The resulting path `Q` is chordless: any two of its support vertices that are
adjacent in `G` are joined by an edge of `Q`. -/
theorem exists_induced_path_of_walk (K : Set V) {x y : V}
    (hx : x ∈ K) (hy : y ∈ K) (P : G.Walk x y) (hsupp : ∀ w ∈ P.support, w ∈ K) :
    ∃ Q : G.Walk x y, Q.IsPath ∧ (∀ w ∈ Q.support, w ∈ K) ∧
      (∀ s ∈ Q.support, ∀ t ∈ Q.support, G.Adj s t → s(s, t) ∈ Q.edges) := by
  obtain ⟨Q, hQ⟩ : ∃ Q : (G.induce K).Walk ⟨x, hx⟩ ⟨y, hy⟩,
      Q.IsPath ∧ Q.length = (G.induce K).dist ⟨x, hx⟩ ⟨y, hy⟩ := by
    apply_rules [SimpleGraph.Reachable.exists_path_of_dist]
    convert reachable_induce_of_walk K hx hy P hsupp using 1
  refine ⟨Q.map (SimpleGraph.Hom.comap _ _), ?_, ?_, ?_⟩ <;> simp_all +decide
  · simp_all +decide [SimpleGraph.Walk.isPath_def]
    exact List.Nodup.map (fun x y => by aesop) hQ.1
  · intro s hs hs' t ht ht' hst
    have := geodesic_adj_imp_edge Q hQ.2 hs' ht' hst
    aesop

end SimpleGraph
