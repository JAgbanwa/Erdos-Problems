/-
# Dense triangle decomposition from the shell cover-down residual.

This is the current capstone of the faithful BKLO route.  It chains the two proved reductions

* `BKLO.coverDownStepResidualLarge_of_shellCoverDown : ShellCoverDown → CoverDownStepResidualLarge`
  (the faithful §10.1 cover-down assembly of `BKLO/CoverDownStepFaithful.lean`), and
* `BKLO.triangle_decomposition_dense_of_coverDownStep :
    CoverDownStepResidualLarge → TriangleDecomposable`
  (the iterative-absorption route of `BKLO/MainCoverDownRoute.lean`),

reducing the dense triangle-decomposition theorem to the **single** residual `BKLO.ShellCoverDown`.

`ShellCoverDown` is BKLO's §10.1 cover-down step for the shell of one vortex level.  It is *not*
the sparse-reservoir clause (it does not quantify over link systems nor demand apex abundance), so
the sparse-reservoir refutations of this project do not apply to it.  Its approximate form
`BKLO.ShellCoverDownApprox` is discharged from the nibble in
`BKLO.shellCoverDownApprox_of_approxTriDecomp`; the only remaining gap is confining the spread
leftover to a bounded core.
-/
import BKLO.CoverDownStepFaithful
import BKLO.MainCoverDownRoute

namespace BKLO

/-- **Dense triangle decomposition from the shell cover-down residual.**
The dense (`δ ≥ 9/10 + ε`) triangle-decomposition theorem (`BKLO.TriDecompDense`) holds given the
single residual `BKLO.ShellCoverDown` (the faithful §10.1 cover-down step). -/
theorem triDecompDense_of_shellCoverDown
    (hcd : ShellCoverDown) : TriDecompDense :=
  triDecompDense_of_coverDownStep
    (coverDownStepResidualLarge_of_shellCoverDown hcd)

end BKLO
