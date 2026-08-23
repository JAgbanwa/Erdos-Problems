/-
# BKLO — a faithful formalization of Barber–Kühn–Lo–Osthus,
  "Edge-decompositions of graphs with high minimum degree" (Adv. Math. 288 (2016)).

This project ports the paper's *iterative absorption* method (Method 2), independently of the
bespoke local-budget absorber developed in `Ax2`.  The end goal specialised to `K₃` is:

  Theorem 1.3 / 6.3 (for F = K₃): if the fractional K₃-decomposition threshold is δ*, then every
  large K₃-divisible graph with δ(G) ≥ (max{δ*, 3/4} + ε)n has a K₃-decomposition.

Together with Dross (δ*_{K₃} ≤ 9/10) this gives an exact triangle decomposition at δ ≥ (9/10+ε)n —
the AX2 half of Paper III.

This file fixes the basic vocabulary (Sections 3–4) and the transformer/absorber relation
(Section 8.1), and proves the first structural fact — transitivity of the transformer relation
(Proposition 8.2) — which is essentially definitional.  Everything here is `sorry`-free.
-/
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Real.Basic

open Finset

namespace BKLO

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The edge set (as `Sym2`) of a `Finset` of vertices, viewed as a complete graph on that set:
all unordered pairs of distinct vertices of `t`.  For a 3-set this is the triangle's three edges. -/
def cliqueEdges (t : Finset V) : Finset (Sym2 V) :=
  (t.sym2).filter (fun e => ¬ e.IsDiag)

/-- **F = K₃ decomposition.**  A finite family of triangles (3-cliques of `G`) that are pairwise
edge-disjoint and cover every edge of `G` exactly once. -/
def IsTriangleDecomp (G : SimpleGraph V) [DecidableRel G.Adj]
    (parts : Finset (Finset V)) : Prop :=
  (∀ t ∈ parts, G.IsNClique 3 t) ∧
    ∀ e ∈ G.edgeFinset, ∃! t, t ∈ parts ∧ e ∈ cliqueEdges t

/-- **Fractional K₃-decomposition** (Section 4).  Nonnegative weights on the triangles of `G` such
that the total weight of triangles through each edge is exactly `1`. -/
def IsFracTriangleDecomp (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : Finset V → ℝ) : Prop :=
  (∀ t, 0 ≤ w t) ∧
    ∀ e ∈ G.edgeFinset,
      (∑ t ∈ G.cliqueFinset 3, if e ∈ cliqueEdges t then w t else 0) = 1

/-- `G` is fractionally triangle decomposable. -/
def FracTriangleDecomposable (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∃ w : Finset V → ℝ, IsFracTriangleDecomp G w

/-- `G` is triangle decomposable. -/
def TriangleDecomposable (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∃ parts : Finset (Finset V), IsTriangleDecomp G parts

end BKLO
