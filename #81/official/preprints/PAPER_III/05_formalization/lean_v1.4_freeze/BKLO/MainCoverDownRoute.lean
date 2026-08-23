/-
# The FAITHFUL cover-down / nested-vortex route to the main theorem, and its exact residual.

This file is the end of the reservoir-free route.  It wires

  `BKLO.CoverDownStepResidualLarge`
    →  `BKLO.VortexCoverDownEngineR3`            (`vortexCoverDownEngineR3_of_residual`)
    →  `BKLO.NearOptimalConclusion`              (`nearOptimalConclusion_of_coverDownEngineR3`)
    →  the dense main theorem                    (`triangle_decomposition_of_nearOptimal`, §11)

and records the exact residual.

**What is discharged.**  Along the whole route the following are *proved* in this project, and are
therefore not hypotheses of `BKLO.triangle_decomposition_dense_of_coverDownStep`:

* the schedule window and the bottom clause of the vortex (`BKLO.powerSchedule_window`,
  `BKLO.vortexBottomClauseR2_of_schedule_window`);
* the thrice-repaired **descent clause** `BKLO.vortexDescentClauseR3_of_powerSchedule` — the naive
  `BKLO.VortexScheduleSlack` and `BKLO.VortexDescentClauseR2` are both refuted in this project,
  `BKLO.VortexDescentClauseR3` is a theorem — consumed by the recursion through
  `BKLO.descent_of_R3`;
* §8.1 and §5, i.e. the absorbers and their placement (`BKLO.sparseAbsorberExistence_nine`,
  `BKLO.exists_placement`), which §11 uses to absorb the bounded-core leftover of §10;
* the two classical inputs that `BKLO/MainR4.lean` still carries — Dross's fractional threshold and
  the max-degree nibble — because they were used there *only* to manufacture the cover-down step
  out of the reservoir clause, which is exactly the clause this route takes as its interface;
* Dirac's theorem, proved here as `BKLO.perfectMatchingDirac_holds`, which on this route is not
  needed as a hypothesis at all;
* the bounded-core absorber `BKLO.coreAbsorberExistence_holds` /
  `BKLO.boundedLeftover_confined`, proved in this project: a leftover confined to a bounded vertex
  set is absorbable.  It is *not* assumed here, and the route never needs a sparse reservoir
  absorbing a spread leftover — the leftover of §10 is confined to the bounded core `U` and §11
  absorbs it with the placed absorbers.

**What is left.**  Exactly one clause, `BKLO.CoverDownStepResidualLarge`: one cover-down step of the
vortex, for every small `ε`, for some large ratio `K`, for every schedule in the window
`[9/10 + ε/2, 9/10 + 3ε/4]` and every scale above a threshold.  Its protected level is either empty
or of size at least the scale — the restriction forced by `BKLO.not_reservoirClauseResidual`, which
refutes the unrestricted form.

For comparison, `BKLO.triangle_decomposition_dense_of_reservoir` below re-derives the same
conclusion from the inputs of the reservoir route — Dross, the **dense** max-degree nibble
(`BKLO.FracToApproxMaxDegDense`; the general `BKLO.FracToApproxMaxDeg` assumed in
`BKLO/MainR4.lean` is false, so that derivation is vacuous as it stands), and
`BKLO.ReservoirClauseResidual4`.  So the residual of this route is no stronger than the residual of
the reservoir route, and `BKLO.coverDownK3Div_of_coverDownStep` shows it is at least as strong as
the classical cover-down input `BKLO.CoverDownK3Div`.

This route does **not** use `ClusterUsageRouting` and is not subject to the sparse-cluster
impossibility results of this project: it never asks for a vertex-sparse reservoir at all.

Everything here is `sorry`-free.
-/
import BKLO.CoverDownEngineR3
import BKLO.TriDecompDenseFromInputs
import BKLO.DiracMatching
import BKLO.BoundedLeftoverConfined

open Finset

namespace BKLO

/-- **§10 from the residual cover-down step.**  All three vortex clauses — window, bottom and the
proved thrice-repaired descent clause — are supplied by the power-law schedule. -/
theorem nearOptimalConclusion_of_coverDownStep (h : CoverDownStepResidualLarge) :
    NearOptimalConclusion :=
  nearOptimalConclusion_of_coverDownEngineR3 (vortexCoverDownEngineR3_of_residual h)

/-- **Main theorem (AX2 half of Erdős #81) on the cover-down / nested-vortex route.**

For every `ε > 0`, every sufficiently large triangle-divisible graph with
`δ(G) ≥ (9/10 + ε)|V|` has a triangle decomposition — from the single residual clause
`BKLO.CoverDownStepResidualLarge`. -/
theorem triangle_decomposition_dense_of_coverDownStep (h : CoverDownStepResidualLarge) :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ,
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        n₀ ≤ Fintype.card V →
        (3 ∣ G.edgeFinset.card ∧ ∀ v, Even (G.degree v)) →
        (9 / 10 + ε) * (Fintype.card V : ℝ) ≤ (G.minDegree : ℝ) →
        TriangleDecomposable G :=
  triangle_decomposition_of_nearOptimal (nearOptimalConclusion_of_coverDownStep h)

/-- **The same, in the edge-set form `BKLO.TriDecompDense`.** -/
theorem triDecompDense_of_coverDownStep (h : CoverDownStepResidualLarge) : TriDecompDense :=
  triDecompDense_of_nearOptimal (nearOptimalConclusion_of_coverDownStep h)

/-- **The residual is of theorem strength.**  It implies the repaired §10 cover-down input
`BKLO.CoverDownK3Div`, which is the classical cover-down statement this project measures the vortex
against.  So `BKLO.CoverDownStepResidualLarge` is not weaker than `BKLO.CoverDownK3Div`: the route
reduces the theorem to *a* cover-down step, not to something strictly stronger in disguise. -/
theorem coverDownK3Div_of_coverDownStep (h : CoverDownStepResidualLarge) : CoverDownK3Div :=
  coverDownK3Div_of_triDecompDense (triDecompDense_of_coverDownStep h)

/-- **The old residual still works.**  The same conclusion from the inputs of the reservoir route:
Dross's fractional threshold, the *dense* max-degree nibble, and the reservoir clause at a large
protected level `BKLO.ReservoirClauseResidual4`.  Dirac's theorem is not needed: it is proved in
this project (`BKLO.perfectMatchingDirac_holds`) and, on this route, never used. -/
theorem triangle_decomposition_dense_of_reservoir (hDross : FracTriangleThreshold)
    (hNib : FracToApproxMaxDegDense) (hRes : ReservoirClauseResidual4) :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ,
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        n₀ ≤ Fintype.card V →
        (3 ∣ G.edgeFinset.card ∧ ∀ v, Even (G.degree v)) →
        (9 / 10 + ε) * (Fintype.card V : ℝ) ≤ (G.minDegree : ℝ) →
        TriangleDecomposable G :=
  triangle_decomposition_dense_of_coverDownStep
    (coverDownStepResidualLarge_of_reservoir4 hDross hNib hRes)

end BKLO
