/-
# The exact obstruction of the cover-down vehicle.

`BKLO/CoverDownVortexEngine.lean` discharges the AX2 §10 conclusion along BKLO's own route — a
vortex whose levels are covered down one onto the next — from the three classical inputs together
with three residual hypotheses: the repaired cover-down step `BKLO.CoverDownK3Div`, the vortex
schedule `BKLO.VortexScheduleSlack` and the divisibility fix `BKLO.LevelDivFixProp`.

This file measures the first of these exactly.  `BKLO/CoverDownFromDecomp.lean` already shows

  `TriDecompDense → CoverDownK3Div`   (`BKLO.coverDownK3Div_of_triDecompDense`),

`TriDecompDense` being the triangle decomposition theorem for dense divisible graphs in edge-set
form — that is, the very statement §10 is used to prove.  The converse is proved here by running
the cover-down vehicle:

  `CoverDownK3Div → TriDecompDense`   (`BKLO.triDecompDense_of_coverDownK3Div`),

modulo the three classical inputs, the schedule and the fix.  Together
(`BKLO.coverDownK3Div_iff_triDecompDense`) they say that the repaired cover-down step is **of
exactly the same strength** as the theorem the vehicle uses it to prove.

The consequence for the AX2 programme is unambiguous, and is stated here rather than left implicit:
the cover-down vehicle **relocates** the §10 obstruction into `CoverDownK3Div`; it does not
discharge it.  Any unconditional proof of the §10 conclusion along this route must prove
`CoverDownK3Div` by means that do not themselves invoke a triangle decomposition of a dense
divisible graph at the same scale — for instance by the reservoir construction of
`BKLO/CoverDownFused.lean`, which is where the routed sweep's density conflict arose.

Note also that the schedule hypothesis `VortexScheduleSlack` carried by the two theorems below is
itself **false** (`BKLO.not_vortexScheduleSlack`, `BKLO/VortexScheduleRefutation.lean`), so they
are vacuously conditional.  The forward direction is recorded all the same: it is the exact
measurement of `CoverDownK3Div` that the cover-down vehicle was built to obtain, and it remains
the right statement once the schedule interface is repaired.

Everything here is `sorry`-free.
-/
import BKLO.CoverDownVortexEngine
import BKLO.TriDecompDenseFromInputs

open Finset

namespace BKLO

/-- **The decomposition theorem for dense divisible graphs follows from the repaired cover-down
step**, via the cover-down vortex vehicle.  This is the converse of
`BKLO.coverDownK3Div_of_triDecompDense`. -/
theorem triDecompDense_of_coverDownK3Div
    (hDross : FracTriangleThreshold) (hNib : FracToApproxMaxDeg) (hDirac : PerfectMatchingDirac)
    (hFix : LevelDivFixProp) (hSched : VortexScheduleSlack) (hCoverDown : CoverDownK3Div) :
    TriDecompDense :=
  triDecompDense_of_inputs hDross (fracToApprox_of_maxDeg hNib) hDirac
    (nearOptimalDecomp_of_coverDownDiv hFix hSched hCoverDown)

/-- **The repaired cover-down step is of exactly the same strength as the theorem it is used to
prove.**  Modulo the three classical inputs, the vortex schedule and the divisibility fix, the §10
cover-down input `BKLO.CoverDownK3Div` and the triangle decomposition theorem for dense divisible
graphs `BKLO.TriDecompDense` are equivalent.

This is the exact obstruction of the cover-down vehicle: assuming `CoverDownK3Div` is assuming the
conclusion. -/
theorem coverDownK3Div_iff_triDecompDense
    (hDross : FracTriangleThreshold) (hNib : FracToApproxMaxDeg) (hDirac : PerfectMatchingDirac)
    (hFix : LevelDivFixProp) (hSched : VortexScheduleSlack) :
    CoverDownK3Div ↔ TriDecompDense :=
  ⟨fun hCD => triDecompDense_of_coverDownK3Div hDross hNib hDirac hFix hSched hCD,
    coverDownK3Div_of_triDecompDense⟩

end BKLO
