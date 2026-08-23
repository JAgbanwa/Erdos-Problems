/-
# BKLO Section 10 — the near-optimal decomposition, as an interface.

Section 10 is the *iterative absorption* half of the engine: one iterates the approximate
decomposition (`FracToApprox`, fed by `FracTriangleThreshold`) down a nested "vortex" of vertex
subsets, covering down at each step, so that the uncovered edges are eventually confined to a
bounded set of vertices; the low-degree remainder is covered using `PerfectMatchingDirac` (the
`r = 2` case of the `Kᵣ`-factor input).  Its conclusion is recorded here as `NearOptimalConclusion`
and the whole section as the implication `NearOptimalDecomp` from the three external inputs.

Two points about the exact shape of the statement, both forced by the way §11 consumes it.

* The bounded set `U` must be produced **before** the absorbing structure `A`, because the absorbers
  are built for all divisible graphs on `U` and only then reserved inside `G`.  Hence the quantifier
  order `∃ U, ∀ A`.
* The reserved structure `A` is a *bounded* edge set (`A.card ≤ K`, with `K` quantified before the
  threshold `n₀`) which spans no edge inside `U`; the decomposition is then required of `G - A`,
  whose divisibility is a hypothesis (it holds in §11 because the absorbing structure is itself
  triangle-decomposable, hence divisible).

`NearOptimalConclusion` is **satisfiable**: it is implied by the (true) theorem it is used to prove,
already with `C = 0` and `U = ∅` — for `n` large a bounded `A` changes the minimum degree by at most
`K`, so `G - A` is a large divisible graph of minimum degree `≥ (9/10 + ε/2)n` and therefore
triangle-decomposable, leaving no uncovered edge at all.  It is genuinely weaker than the theorem:
it allows an arbitrary uncovered remainder inside a bounded vertex set, which is precisely the part
that the §8.1 absorbers take care of.
-/
import BKLO.Inputs
import BKLO.Absorber

open Finset

namespace BKLO

/-- **The conclusion of §10.**  For every `ε > 0` there is a bound `C` such that every large graph
of minimum degree at least `(9/10 + ε)n` has a set `U` of at most `C` vertices with the following
property: after deleting any bounded edge set `A` spanning no edge inside `U` and leaving a
divisible graph, the rest can be covered by edge-disjoint triangles up to a remainder inside `U`. -/
def NearOptimalConclusion : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℕ, ∀ K : ℕ, ∃ n₀ : ℕ,
    ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      n₀ ≤ Fintype.card V → (9 / 10 + ε) * (Fintype.card V : ℝ) ≤ (G.minDegree : ℝ) →
      ∃ U : Finset V, U.card ≤ C ∧
        ∀ A : Finset (Sym2 V), A ⊆ G.edgeFinset → A.card ≤ K →
          Disjoint A (cliqueEdges U) → TriDivisible (G.edgeFinset \ A) →
          ∃ P : Finset (Finset V),
            (∀ t ∈ P, t.card = 3) ∧
            (∀ t ∈ P, cliqueEdges t ⊆ G.edgeFinset \ A) ∧
            (∀ t ∈ P, ∀ t' ∈ P, t ≠ t' → Disjoint (cliqueEdges t) (cliqueEdges t')) ∧
            ((G.edgeFinset \ A) \ famEdges P ⊆ cliqueEdges U)

/-- **§10 (interface).**  The three external inputs yield the near-optimal decomposition. -/
def NearOptimalDecomp : Prop :=
  FracTriangleThreshold → FracToApprox → PerfectMatchingDirac → NearOptimalConclusion

end BKLO
