/-
# BKLO — the external inputs (Section 4), stated as interfaces.

The iterative-absorption engine (Sections 5–11) consumes three external results.  For `F = K₃` all
three are ALREADY available to us and are recorded here as explicit `Prop`-level interfaces, so the
engine can be developed and assembled against them.  Discharging each is a separate, already-solved
task:

* `FracTriangleThreshold` — Dross's theorem (SIAM JDM 30 (2016), Thm 5): every graph with
  `δ(G) ≥ (9/10)|V|` is fractionally triangle decomposable.  **Formalized in `Ax2.DrossNet`
  (`dross_fractional_flow_exact`), sorry-free.**

* `FracToApprox` — Haxell–Rödl (Combinatorica 21 (2001); BKLO Thm 4.3): a fractionally triangle
  decomposable graph has, for every `η > 0` and large `|V|`, an `η`-approximate triangle
  decomposition (edge-disjoint triangles missing `≤ η|V|²` edges).  **This is exactly the Rödl
  nibble developed in the `Nibble` project (spread rounding).**

* `PerfectMatchingDirac` — for `F = K₃` (which is `2`-regular) the `Kᵣ`-factors that Section 10
  needs are `K₂`-factors, i.e. perfect matchings; Dirac's theorem (`δ ≥ |V|/2`) supplies them.
  **Available in Mathlib.**  (This is why the triangle case avoids the general Hajnal–Szemerédi
  theorem, BKLO Thm 10.2.)

Section 10 needs two further external results — the probabilistic existence of the vortex and the
cover-down lemma.  They are stated, in the same style, in `BKLO/InputsVortex.lean`, which has to
sit downstream of `BKLO/Vortex.lean` because it uses the edge-set vocabulary developed there.

Everything here is `sorry`-free: these are definitions of the interface predicates, not claims.
-/
import BKLO.Basic
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Tactic.Bound

open Finset

namespace BKLO

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- An `η`-approximate triangle decomposition: edge-disjoint triangles covering all but `≤ η|V|²`
edges of `G`. -/
def IsApproxTriangleDecomp (G : SimpleGraph V) [DecidableRel G.Adj]
    (parts : Finset (Finset V)) (η : ℝ) : Prop :=
  (∀ t ∈ parts, G.IsNClique 3 t) ∧
  (∀ t ∈ parts, ∀ t' ∈ parts, t ≠ t' → Disjoint (cliqueEdges t) (cliqueEdges t')) ∧
  ((G.edgeFinset \ parts.biUnion cliqueEdges).card : ℝ) ≤ η * (Fintype.card V : ℝ) ^ 2

/-- **Input 1 (Dross).** The fractional triangle decomposition threshold at `9/10`. -/
def FracTriangleThreshold : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    9 * Fintype.card V ≤ 10 * G.minDegree → FracTriangleDecomposable G

/-- **Input 2 (Haxell–Rödl / Rödl nibble).** A fractional triangle decomposition can be turned into
an `η`-approximate one, for every `η > 0` once `|V|` is large. -/
def FracToApprox : Prop :=
  ∀ η : ℝ, 0 < η → ∃ n₀ : ℕ,
    ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      n₀ ≤ Fintype.card V → FracTriangleDecomposable G →
      ∃ parts : Finset (Finset V), IsApproxTriangleDecomp G parts η

/-- An `η`-approximate triangle decomposition **with bounded maximum leftover degree**:
edge-disjoint triangles such that every vertex meets at most `η|V|` uncovered edges.  This is the
conclusion of the nibble in its Pippenger–Spencer / Haxell–Rödl form, which is strictly stronger
than `IsApproxTriangleDecomp` (see `BKLO.isApproxTriangleDecomp_of_maxDeg`). -/
def IsApproxTriangleDecompMaxDeg (G : SimpleGraph V) [DecidableRel G.Adj]
    (parts : Finset (Finset V)) (η : ℝ) : Prop :=
  (∀ t ∈ parts, G.IsNClique 3 t) ∧
  (∀ t ∈ parts, ∀ t' ∈ parts, t ≠ t' → Disjoint (cliqueEdges t) (cliqueEdges t')) ∧
  ∀ v : V, (((G.edgeFinset \ parts.biUnion cliqueEdges).filter (fun e => v ∈ e)).card : ℝ)
      ≤ η * (Fintype.card V : ℝ)

/-- **Input 2′ (Pippenger–Spencer / Haxell–Rödl, maximum-degree form; BKLO Thm 4.3 as it is
actually used in §10).**  A fractionally triangle decomposable graph has, for every `η > 0` and
large `|V|`, an approximate triangle decomposition whose *leftover has maximum degree at most*
`η|V|` — not merely `η|V|²` leftover edges in total.

This is the standard conclusion of the semi-random (nibble) method: Pippenger–Spencer's theorem on
near-perfect matchings in nearly regular hypergraphs of small codegree gives a matching of the
triangle hypergraph leaving every *vertex of the hypergraph* — i.e. every edge of `G` — uncovered
only rarely, and the standard iterated form (Rödl nibble, cf. Alon–Spencer, *The Probabilistic
Method*, Ch. 4.7, and Haxell–Rödl, Combinatorica 21 (2001)) upgrades this to the bounded
*maximum degree* statement recorded here.  `FracToApproxMaxDeg` implies `FracToApprox`
(`BKLO.fracToApprox_of_maxDeg`), so replacing Input 2 by it does not add any independent
assumption beyond the strengthening of the leftover bound.

It is a statement about *approximate* decompositions only: it never produces an exact
decomposition of any graph, so it does not imply the main theorem. -/
def FracToApproxMaxDeg : Prop :=
  ∀ η : ℝ, 0 < η → ∃ n₀ : ℕ,
    ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      n₀ ≤ Fintype.card V → FracTriangleDecomposable G →
      ∃ parts : Finset (Finset V), IsApproxTriangleDecompMaxDeg G parts η

/-- **Input 3 (Dirac perfect matching, the `r = 2` case of the Kᵣ-factor input).** Every graph on an
even number of vertices with minimum degree `≥ |V|/2` has a perfect matching. -/
def PerfectMatchingDirac : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    Even (Fintype.card V) → Fintype.card V ≤ 2 * G.minDegree →
    ∃ M : G.Subgraph, M.IsPerfectMatching

end BKLO
