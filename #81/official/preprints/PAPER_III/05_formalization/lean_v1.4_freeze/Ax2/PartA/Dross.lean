/-
  Part A — Dross's fractional triangle-decomposition threshold.

  F. Dross, *Fractional triangle decompositions in graphs with large minimum degree*,
  SIAM J. Discrete Math. 30 (2016), no. 1, 36–42, Theorem 5.

  STATUS: reduced to the dual "no separating potential" core.

  Architecture: Mathlib has no max-flow/min-cut, so we do NOT follow Dross's flow argument
  literally. Instead we use the LP-duality (Farkas) bridge `decomp_of_no_farkas` (A5, proved
  sorry-free in `Ax2.PartA.FarkasSplit`): a fractional decomposition exists iff there is no
  edge-potential `y` that is nonnegative on every triangle yet has negative total. So
  `dross_fractional` reduces to proving, from `δ(G) ≥ (9/10)n`, that no such `FarkasPotential`
  exists. That dual statement is exactly the content of Dross's §2 (his no-deficient-cut
  argument, transposed): its arithmetic core — K₄ counting (`k4_lower_bound`, A6), the
  extremization `dross_7_to_8` (A7), and the closing contradiction (`DrossArith`,
  `TriangleFreeBound`, A8) — is already formalized and gate-verified. The remaining `sorry` is
  the reduction assembling those into "no `FarkasPotential`".
-/
import Ax2.PartA.FarkasSplit
import Ax2.Explore.DrossNet

namespace Ax2

open SimpleGraph

/-- **THE ATOM (Dross §2, min-cut core).** If `δ(G) ≥ (9/10)·n`, no edge-potential is a
separating (Farkas) certificate. This is the dual of Dross's flow-feasibility claim: a
`FarkasPotential` is exactly a deficient cut of the auxiliary network `Ĝ`, and the K₄ counting
(A6), the extremization (A7 `dross_7_to_8`), and the triangle-free/closing contradiction (A8
`DrossArith`, `TriangleFreeBound`) rule it out. Replacing this `sorry` closes `dross_fractional`,
hence Part A. See `DROSS_FLOW_ROUTE.md`. -/
theorem no_deficient_cut {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : 9 * Fintype.card V ≤ 10 * G.minDegree) :
    ∀ y : Sym2 V → ℝ, ¬ FarkasPotential G y := by
  exact not_farkas_of_fractional G (DrossNet.dross_fractional_flow_exact G h)

/-- **Part A (Dross, Thm 5).** If `δ(G) ≥ (9/10)·n`, then `G` has a fractional triangle
decomposition. The route is machine-verified: it reduces, via the Farkas bridge A5
(`decomp_of_no_farkas`, sorry-free), to the single atom `no_deficient_cut`. -/
theorem dross_fractional {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : 9 * Fintype.card V ≤ 10 * G.minDegree) :
    FractionalTriangleDecomp G :=
  decomp_of_no_farkas G (no_deficient_cut G h)

end Ax2
