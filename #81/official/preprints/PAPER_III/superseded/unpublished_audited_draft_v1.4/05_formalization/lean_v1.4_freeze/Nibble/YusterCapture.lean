/-
# Yuster Y1c (capturing vertices) — per-vertex triangle degree from a uniform pair

Standalone, Mathlib-only. The formalizable half of Y1c: bridging a *global* `ε`-uniform pair of parts
`(s, t)` (from `exists_uniform_pair`) to a *per-vertex* triangle-degree lower bound. For a vertex `v`
whose neighbourhood captures an `ε`-fraction of both parts (`ε|s| ≤ |s ∩ N(v)|`, `ε|t| ≤ |t ∩ N(v)|`),
the sub-pair `(s ∩ N(v), t ∩ N(v))` is `ε`-dense — directly from the definition of `IsUniform`
(large sub-pairs have density within `ε` of the pair) — and lies inside `N(v)`, so the number of
triangles through `v` is at least `ε · |s ∩ N(v)| · |t ∩ N(v)| ≥ ε³·|s|·|t|`.

The remaining (non-local) half of Y1c is the counting that MOST vertices are capturing — a density
argument. This file supplies the clean structural bridge; that counting is the residual gap.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.YusterCounting

open Finset SimpleGraph Hypergraph

namespace Nibble.Yuster

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **Edge count from density.** If `d ≤ edgeDensity s t`, the pair has `≥ d·|s|·|t|` interedges. -/
theorem interedges_lower_of_density {d : ℝ} {s t : Finset V}
    (hd : d ≤ (G.edgeDensity s t : ℝ)) :
    d * (s.card : ℝ) * (t.card : ℝ) ≤ (G.interedges s t).card := by
  by_cases h : (s.card : ℝ) * t.card = 0
  · have hz : d * (s.card : ℝ) * (t.card : ℝ) = 0 := by
      rcases mul_eq_zero.mp h with h0 | h0 <;> simp [h0]
    rw [hz]; exact Nat.cast_nonneg _
  · have hpos : 0 < (s.card : ℝ) * t.card :=
      lt_of_le_of_ne (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (Ne.symm h)
    have hdef : (G.edgeDensity s t : ℝ)
        = ((G.interedges s t).card : ℝ) / ((s.card : ℝ) * (t.card : ℝ)) := by
      simp only [SimpleGraph.edgeDensity, Rel.edgeDensity, SimpleGraph.interedges, Rel.interedges]
      push_cast
      ring
    rw [hdef, le_div_iff₀ hpos] at hd
    have hassoc : d * (s.card : ℝ) * (t.card : ℝ) = d * ((s.card : ℝ) * t.card) := by ring
    rw [hassoc]; exact hd

/-- **Y1c (capturing vertex) — per-vertex triangle degree lower bound.** If `(s, t)` is an `ε`-uniform,
`2ε`-dense, disjoint pair and the neighbourhood of `v` captures an `ε`-fraction of each part, then the
triangle degree at `v` is at least `ε · |s ∩ N(v)| · |t ∩ N(v)|`. The sub-pair inside `N(v)` inherits
`ε`-density from `IsUniform`; the interedges are triangles through `v`. -/
theorem triangleHypergraph_degree_lower_of_capture {ε : ℝ} {v : V} {s t : Finset V}
    (hunif : G.IsUniform ε s t) (hdense : 2 * ε ≤ (G.edgeDensity s t : ℝ)) (hst : Disjoint s t)
    (hscap : (s.card : ℝ) * ε ≤ ((s ∩ G.neighborFinset v).card : ℝ))
    (htcap : (t.card : ℝ) * ε ≤ ((t ∩ G.neighborFinset v).card : ℝ)) :
    ε * ((s ∩ G.neighborFinset v).card : ℝ) * ((t ∩ G.neighborFinset v).card : ℝ)
      ≤ (degree (triangleHypergraph G) v : ℝ) := by
  set s' := s ∩ G.neighborFinset v with hs'
  set t' := t ∩ G.neighborFinset v with ht'
  -- density of the captured sub-pair is `≥ ε`, from IsUniform
  have hunif' := hunif (Finset.inter_subset_left (s₂ := G.neighborFinset v))
    (Finset.inter_subset_left (s₂ := G.neighborFinset v)) hscap htcap
  have hdens' : ε ≤ (G.edgeDensity s' t' : ℝ) := by
    have := (abs_lt.mp hunif').1
    linarith only [hdense, this]
  -- interedges of the sub-pair lower-bounded, and it lies inside N(v)
  have hie : ε * (s'.card : ℝ) * (t'.card : ℝ) ≤ (G.interedges s' t').card :=
    interedges_lower_of_density G hdens'
  have hdisj' : Disjoint s' t' :=
    Finset.disjoint_of_subset_left Finset.inter_subset_left
      (Finset.disjoint_of_subset_right Finset.inter_subset_left hst)
  have hin : (G.interedges s' t').card ≤ (degree (triangleHypergraph G) v) := by
    rw [triangleHypergraph_degree_eq_edgesInside]
    exact card_interedges_le_edgesInside G hdisj' Finset.inter_subset_right Finset.inter_subset_right
  calc ε * (s'.card : ℝ) * (t'.card : ℝ)
      ≤ (G.interedges s' t').card := hie
    _ ≤ (degree (triangleHypergraph G) v : ℝ) := by exact_mod_cast hin

end Nibble.Yuster
