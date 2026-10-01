import FarExploration.ThresholdCalculus
import FarExploration.TowerHeight
import FarExploration.CodegreeCleanup
import FarExploration.CleanupVerdict
import FarExploration.CleanupThreshold
import FarExploration.CleanupRigidVerdict
import FarExploration.CleanupDense
import FarExploration.CleanupTriangleRegular

/-!
# Huella axiomática de la exploración

Los cuatro enunciados que se entregan, con su huella.  Debe salir
`[propext, Classical.choice, Quot.sound]` en todos.
-/

#print axioms FarExploration.ThresholdCalculus.chordalTargetFrom_max
#print axioms FarExploration.ThresholdCalculus.chordalTargetAt_of_single_rounding
#print axioms FarExploration.ThresholdCalculus.chordalTargetFrom_calibrated
#print axioms FarExploration.TowerHeight.deltaFar_eq
#print axioms FarExploration.TowerHeight.k0Far_eq
#print axioms FarExploration.TowerHeight.heightFar_ge
#print axioms FarExploration.TowerHeight.tower_le_bound
#print axioms FarExploration.TowerHeight.bound_ge_tower_of_height
#print axioms FarExploration.CodegreeCleanup.uniformRoundingTarget_of_codegreeCleanup

/-! ## Dualización LP de la limpieza

El veredicto: en el régimen de la aplicación el enunciado LP abstracto es **falso**, con
certificado dual explícito, y habría implicado el concreto.  Ninguna demostración que use sólo el
programa lineal puede cerrar `CodegreeCleanupAt`.  Y sobre una familia **realizable por grafos**
—triángulos disjuntos— todo umbral válido supera `1/eps`. -/

#print axioms FarExploration.CleanupLP.abstractCleanupAt_of_scale
#print axioms FarExploration.CleanupBridge.codegreeCleanupAt_of_abstract
#print axioms FarExploration.CleanupDuality.not_feasible_of_dualCertificate
#print axioms FarExploration.CleanupDuality.dualCertificate_of_not_feasible
#print axioms FarExploration.CleanupDuality.cleanupFeasible_iff
#print axioms FarExploration.CleanupObstruction.not_abstractCleanupAt
#print axioms FarExploration.CleanupCertificate.rigid_not_cleanupFeasible
#print axioms FarExploration.CleanupVerdict.codegreeCleanupAt_of_scale
#print axioms FarExploration.CleanupVerdict.abstractCleanup_dichotomy
#print axioms FarExploration.CleanupVerdict.obstruction_value_bound
#print axioms FarExploration.CleanupVerdict.lp_route_insufficient
#print axioms FarExploration.CleanupVerdict.not_abstractCleanupAt_applicationParameters
#print axioms FarExploration.CleanupThreshold.codegreeCleanupAt_iff_exists_threshold
#print axioms FarExploration.CleanupThreshold.threshold_gt
#print axioms FarExploration.CleanupThreshold.application_threshold_gt

/-! ## Rigidez y masa: la familia de Ruzsa–Szemerédi

La hipótesis de que la rigidez obligue a masa lineal es **falsa**: el grafo tripartito de
Ruzsa–Szemerédi es rígido —cada arista en un único triángulo— y tiene `(2M+1)·|s|` triángulos
sobre `6M+3` vértices.  De ahí una cota inferior del umbral de la limpieza que es
superpolinómica en `1/eps`. -/

#print axioms FarExploration.RuzsaSzemeredi.item_card_eq_three
#print axioms FarExploration.RuzsaSzemeredi.item_eq_tri
#print axioms FarExploration.RuzsaSzemeredi.graphSystem_rigid
#print axioms FarExploration.RuzsaSzemeredi.card_supports_ge
#print axioms FarExploration.RigidThreshold.rigid_threshold_gt
#print axioms FarExploration.CleanupRigidVerdict.rs_rigid_mass_ge
#print axioms FarExploration.CleanupRigidVerdict.rs_threshold_gt
#print axioms FarExploration.CleanupRigidVerdict.application_threshold_gt
#print axioms FarExploration.CleanupRigidVerdict.application_threshold_gt_behrend
#print axioms FarExploration.CleanupRigidVerdict.threshold_gt_exp
#print axioms FarExploration.CleanupRigidVerdict.threshold_superpolynomial
#print axioms FarExploration.CleanupRigidVerdict.threshold_gt_exp_seventy_two
#print axioms FarExploration.CleanupRigidVerdict.rigid_card_le_of_cleanup

/-! ## El extremo denso

En `K_n` la limpieza se consigue con el reparto uniforme sobre todos los `K₄` más una fracción
`θ = min 1 (12·xi)` de reparto uniforme sobre los triángulos, sin hipótesis de masa sobre `x`. -/

#print axioms FarExploration.CleanupDense.value_le_edges
#print axioms FarExploration.CleanupDense.densePacking_mass
#print axioms FarExploration.CleanupDense.densePacking_value
#print axioms FarExploration.CleanupDense.densePacking_codeg_le
#print axioms FarExploration.CleanupDense.dense_cleanup

/-! ## El medio: grafos sin `K₄` triangularmente regulares

Si cada arista de `G` está exactamente en `q` triángulos y `G` no tiene `K₄`, el reparto uniforme
`1/q` sobre los triángulos tiene codegrado `≤ 1/q`, masa `|E|/3` y valor `2|E|/3`, que es el
óptimo de la clase: la limpieza sale con **pérdida cero** en cuanto `1/q ≤ gam`. -/

#print axioms FarExploration.CleanupTriangleRegular.value_le_two_thirds_edges
#print axioms FarExploration.CleanupTriangleRegular.three_mul_card_items_eq_sum
#print axioms FarExploration.CleanupTriangleRegular.three_mul_card_items
#print axioms FarExploration.CleanupTriangleRegular.three_mul_card_items_ge
#print axioms FarExploration.CleanupTriangleRegular.uniform_codeg_le
#print axioms FarExploration.CleanupTriangleRegular.uniform_mass
#print axioms FarExploration.CleanupTriangleRegular.uniform_value
#print axioms FarExploration.CleanupTriangleRegular.triangleRegular_cleanup
#print axioms FarExploration.CleanupTriangleRegular.nearRegular_cleanup
