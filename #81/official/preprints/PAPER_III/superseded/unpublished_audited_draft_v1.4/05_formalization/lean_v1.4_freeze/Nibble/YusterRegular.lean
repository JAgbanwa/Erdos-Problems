/-
# Yuster Y3 assembly — near-regularity and codegree bound of the triangle hypergraph

Standalone, Mathlib-only. Assembles the near-regularity / codegree-bounded interface that
`NibbleTheorem` consumes for the triangle hypergraph, from:

* the degree UPPER bound `triangleHypergraph_degree_le` (`deg ≤ C(deg_G v, 2)`),
* the degree LOWER bound `triangleHypergraph_degree_lower_of_uniform_pair` (a disjoint `2ε`-dense
  uniform pair inside `N(v)` yields `≥ ε|s||t|` triangles), and
* the codegree UPPER bound `triangleHypergraph_codegree_le` (`codeg ≤ |N(u) ∩ N(v)|`).

The per-vertex regular-pair data (`spair v, tpair v`) and the numeric windows are taken as hypotheses
— they are exactly what a Szemerédi regularity partition supplies (the remaining Y1 input). Given them,
`NearlyRegular` and `CodegreeBounded` follow by packaging.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.YusterCounting
import Nibble.Regular

open Finset Hypergraph SimpleGraph

namespace Nibble.Yuster

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **Y3 codegree bound.** If every distinct pair has at most `C` common neighbours, then the triangle
hypergraph is `CodegreeBounded C` (via `triangleHypergraph_codegree_le`). -/
theorem triangleHypergraph_codegreeBounded_of {C : ℝ}
    (hC : ∀ u v : V, u ≠ v → ((G.neighborFinset u ∩ G.neighborFinset v).card : ℝ) ≤ C) :
    CodegreeBounded (triangleHypergraph G) C := by
  intro u v huv
  exact le_trans (by exact_mod_cast triangleHypergraph_codegree_le G huv) (hC u v huv)

/-- **Y3 near-regularity.** Given, for every vertex `v`, a disjoint `2ε`-dense `ε`-uniform pair
`(spair v, tpair v)` inside `N(v)` whose triangle count `ε|spair v||tpair v|` is at least `(1-μ)d`, and
the choose-`2` upper bound `C(|N(v)|,2) ≤ (1+μ)d`, the triangle hypergraph is `NearlyRegular d μ`. The
lower half is `triangleHypergraph_degree_lower_of_uniform_pair`; the upper half is
`triangleHypergraph_degree_le`. -/
theorem triangleHypergraph_nearlyRegular_of_pairs {d μ ε : ℝ}
    (spair tpair : V → Finset V)
    (hunif : ∀ v, G.IsUniform ε (spair v) (tpair v))
    (hdense : ∀ v, 2 * ε ≤ (G.edgeDensity (spair v) (tpair v) : ℝ))
    (hdisj : ∀ v, Disjoint (spair v) (tpair v))
    (hsv : ∀ v, spair v ⊆ G.neighborFinset v)
    (htv : ∀ v, tpair v ⊆ G.neighborFinset v)
    (hlo : ∀ v, (1 - μ) * d ≤ ε * (spair v).card * (tpair v).card)
    (hhi : ∀ v, ((G.neighborFinset v).card.choose 2 : ℝ) ≤ (1 + μ) * d) :
    NearlyRegular (triangleHypergraph G) d μ := by
  intro v
  refine ⟨?_, ?_⟩
  · exact le_trans (hlo v)
      (triangleHypergraph_degree_lower_of_uniform_pair G (hunif v) (hdense v)
        (hdisj v) (hsv v) (htv v))
  · exact le_trans (by exact_mod_cast triangleHypergraph_degree_le G v) (hhi v)

/-- **Y3 combined** — near-regularity together with the codegree bound, the exact pair of hypotheses
`NibbleTheorem` consumes for the triangle hypergraph. -/
theorem triangleHypergraph_nearlyRegular_codegreeBounded {d μ ε C : ℝ}
    (spair tpair : V → Finset V)
    (hunif : ∀ v, G.IsUniform ε (spair v) (tpair v))
    (hdense : ∀ v, 2 * ε ≤ (G.edgeDensity (spair v) (tpair v) : ℝ))
    (hdisj : ∀ v, Disjoint (spair v) (tpair v))
    (hsv : ∀ v, spair v ⊆ G.neighborFinset v)
    (htv : ∀ v, tpair v ⊆ G.neighborFinset v)
    (hlo : ∀ v, (1 - μ) * d ≤ ε * (spair v).card * (tpair v).card)
    (hhi : ∀ v, ((G.neighborFinset v).card.choose 2 : ℝ) ≤ (1 + μ) * d)
    (hC : ∀ u v : V, u ≠ v → ((G.neighborFinset u ∩ G.neighborFinset v).card : ℝ) ≤ C) :
    NearlyRegular (triangleHypergraph G) d μ ∧ CodegreeBounded (triangleHypergraph G) C :=
  ⟨triangleHypergraph_nearlyRegular_of_pairs G spair tpair hunif hdense hdisj hsv htv hlo hhi,
   triangleHypergraph_codegreeBounded_of G hC⟩

end Nibble.Yuster
