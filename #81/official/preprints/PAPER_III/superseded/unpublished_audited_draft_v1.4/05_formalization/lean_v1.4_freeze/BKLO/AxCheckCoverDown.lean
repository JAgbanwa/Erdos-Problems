/-
# Axiom audit for the cover-down vortex vehicle.

Every declaration listed here must depend on `[propext, Classical.choice, Quot.sound]` only.
-/
import BKLO.CoverDownEquivalence
import BKLO.VortexScheduleRefutation

namespace BKLO

-- The assembled vehicle.
#print axioms coverDown_step_fixed
#print axioms coverDown_vortex_fix
#print axioms vortexEngineRatio_of_coverDownDiv
#print axioms nearOptimalDecomp_of_coverDownDiv
#print axioms triangle_decomposition_of_inputs_via_coverdown

-- The exact obstruction: the repaired cover-down input is equivalent to its own conclusion.
#print axioms triDecompDense_of_coverDownK3Div
#print axioms coverDownK3Div_iff_triDecompDense

-- The refutation of the vortex-schedule interfaces.
#print axioms descent_clause_false
#print axioms not_vortexScheduleExists
#print axioms not_vortexScheduleSlack

end BKLO
