/-
  AX2 formalization — shared definitions.

  Target (Paper III, Theorem 2.3 / AX2): for every ε>0 there is n₀ such that every
  triangle-divisible graph on n ≥ n₀ vertices with δ(G) ≥ (9/10+ε)n admits a triangle
  (K₃-) decomposition.

  Route: AX2 = Part A (Dross, fractional threshold ≤ 9/10, formalizable)
             ∘ Part B (BKLO transfer, kept axiomatic — missing Mathlib infrastructure).

  This file fixes the graph-theoretic vocabulary used across the project.
-/
import Mathlib

namespace Ax2

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The (off-diagonal) edges spanned by a vertex set `t`, as a `Finset (Sym2 V)`. For a
3-clique this is its three edges. -/
def triEdges (t : Finset V) : Finset (Sym2 V) :=
  t.sym2.filter (fun e => ¬ e.IsDiag)

/-- `G` is **triangle-divisible**: `3 ∣ e(G)` and every degree is even. -/
def TriangleDivisible (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  3 ∣ G.edgeFinset.card ∧ ∀ v, Even (G.degree v)

/-- `G` has a **fractional triangle decomposition**: nonnegative weights on the 3-cliques so
that every edge carries total weight exactly `1`. -/
def FractionalTriangleDecomp (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∃ w : Finset V → ℝ, (∀ t, 0 ≤ w t) ∧
    ∀ e ∈ G.edgeFinset,
      (∑ t ∈ G.cliqueFinset 3, if e ∈ triEdges t then w t else 0) = 1

/-- `G` has an **(integral) triangle decomposition**: a finset of 3-cliques such that every
edge lies in exactly one of them. -/
def TriangleDecomposable (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∃ parts : Finset (Finset V), (∀ t ∈ parts, G.IsNClique 3 t) ∧
    ∀ e ∈ G.edgeFinset, ∃! t, t ∈ parts ∧ e ∈ triEdges t

end Ax2
