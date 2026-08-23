/-
# Bridge: Ax2 ⇄ BKLO (Method 2) model compatibility.

The BKLO Method-2 library (in the `nibble` package, namespace `BKLO`) was built on an edge-set model
that matches `Ax2.Basic` verbatim: `BKLO.cliqueEdges = Ax2.triEdges` (both `t.sym2.filter (¬ IsDiag)`),
so `BKLO.TriangleDecomposable`, `BKLO.FracTriangleDecomposable` and the divisibility predicate coincide
with the `Ax2` ones definitionally.  This file records those identifications and, crucially, discharges
the first BKLO input — Dross's fractional threshold — from the already-proved
`Ax2.DrossNet.dross_fractional_flow_exact`.
-/
import Ax2.Explore.DrossNet
import Ax2.Basic
import BKLO.Inputs
import BKLO.DiracMatching
import BKLO.TwoSidedUsedClassMatched

namespace Ax2.BKLOBridge

open scoped Classical

variable {V : Type} [Fintype V] [DecidableEq V]

/-- `Ax2.triEdges` and `BKLO.cliqueEdges` are the same function. -/
theorem triEdges_eq_cliqueEdges (t : Finset V) : Ax2.triEdges t = BKLO.cliqueEdges t := rfl

/-- The two fractional-decomposition predicates coincide. -/
theorem fracDecomp_iff (G : SimpleGraph V) [DecidableRel G.Adj] :
    Ax2.FractionalTriangleDecomp G ↔ BKLO.FracTriangleDecomposable G := Iff.rfl

/-- The two integral-decomposition predicates coincide. -/
theorem triDecomp_iff (G : SimpleGraph V) [DecidableRel G.Adj] :
    Ax2.TriangleDecomposable G ↔ BKLO.TriangleDecomposable G := Iff.rfl

/-- **Dross input discharged.**  BKLO's `FracTriangleThreshold` is exactly
`Ax2.DrossNet.dross_fractional_flow_exact`. -/
theorem fracTriangleThreshold_holds : BKLO.FracTriangleThreshold := by
  intro V _ _ G _ h
  exact (fracDecomp_iff G).1 (Ax2.DrossNet.dross_fractional_flow_exact G h)

/-- **AX2 via BKLO Method 2.**  The full absorber half of Paper III, routed through the BKLO
iterative-absorption engine instead of the (refuted) bespoke absorber.  Dross and Dirac are
discharged internally (`fracTriangleThreshold_holds`, `BKLO.perfectMatchingDirac_holds`); the two
remaining genuine analytic inputs — the max-degree nibble `hNib` and the fused §10 vortex/reservoir
interface `hEng` — are carried as honest hypotheses (they are being closed separately).  No `sorry`;
the bespoke `globalFreePivotFamily_holds`/`approxDegBounded_holds` route is bypassed entirely. -/
theorem ax2_of_bklo_inputs (hNib : BKLO.FracToApproxMaxDeg)
    (hRes : BKLO.TwoSidedUsedClassMatchedInvariantPairing) :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ,
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        n₀ ≤ Fintype.card V → Ax2.TriangleDivisible G →
        (9 / 10 + ε) * (Fintype.card V : ℝ) ≤ (G.minDegree : ℝ) →
        Ax2.TriangleDecomposable G := by
  intro ε hε
  obtain ⟨n₀, H⟩ := BKLO.triangle_decomposition_of_inputs_and_twoSidedUsedClassMatchedInvariant
    fracTriangleThreshold_holds hNib BKLO.perfectMatchingDirac_holds hRes ε hε
  refine ⟨n₀, ?_⟩
  intro V _ _ G _ hn hdiv hδ
  exact (triDecomp_iff G).2 (H G hn hdiv hδ)

end Ax2.BKLOBridge
