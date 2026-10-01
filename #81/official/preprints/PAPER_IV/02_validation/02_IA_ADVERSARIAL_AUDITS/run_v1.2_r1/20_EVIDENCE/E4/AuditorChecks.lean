import PaperIV
import PaperIV.DefectExplicitPublication
import PaperIV.OptimalTemplateObstruction
import PaperIV.ExplicitThreshold
import E35.Theorem
import E35.Main
import E32.Comparison
import E34.L11Main
import PublicationStability
import ExplicitFixedStability
import SmallOrderFractional
import RefinedRounding
import ArbitraryOrderSequences
import RootedCliqueRecovery
import EditRootRecovery
import Lean.Elab.Command

/-! Auditor-written independent checks (run_v1.2_r1, E3/E4). Not part of the author's cut.
  1. `#check` of every public declaration cited in the manuscript tables (elaborated types).
  2. `#print axioms` for each.
  3. An independent cone traversal (type + value, transitive) reporting, for each declaration:
     axioms in the cone, whether any constant has root `Erdos81`, any constant named `sorryAx`,
     and which `AlonShapira.*` / `AFKS.*` / `EditRoute.*` constants occur (for the removal-provenance claim). -/

open Lean Elab Command

namespace AuditorChecks

partial def cone (env : Environment) : List Name → NameSet → NameSet
  | [], acc => acc
  | n :: rest, acc =>
    if acc.contains n then cone env rest acc else
      let acc := acc.insert n
      match env.find? n with
      | none => cone env rest acc
      | some ci => cone env (ci.type.getUsedConstants.toList ++
          (ci.value?.map (·.getUsedConstants.toList)).getD [] ++ rest) acc

def publicDecls : List Name := [
  `PaperIV.Erdos81AllOrders.erdos81_all_orders_additive,
  `PaperIV.Erdos81Unconditional.erdos81_cliquePartition,
  `PaperIV.PaperTheorems.erdos81_max_eq,
  `PaperIV.RC01Final.rc01_uniformRoundingTarget,
  `PaperIV.FarRegimeAllGraphs.farRegime_cliquePartition_allGraphs,
  `PaperIV.HybridDichotomy.chordal_far_or_nearStructure,
  `PaperIV.NearH1LocalConstructor.exists_near_partition_paid_by_root_sharp,
  `PaperIV.NearCriticalDichotomy.chordal_far_or_criticalRoot,
  `PaperIV.NearCriticalDichotomy.chordal_far_or_edge_density,
  `PaperIV.SharpConstantOptimality.erdos81_quadratic_constant_optimal,
  `PaperIV.SharpConstantOptimality.erdos81_quadratic_constant_isLeast,
  `PaperIV.IntegralStability.chordal_linear_stability_sixteen,
  `PaperIV.RootPartitionStability.chordal_partition_stability,
  `PaperIV.RootPartitionStability.sum_rootPieceDefect_eq,
  `PaperIV.ExtremalClassification.chordal_extremal_classification,
  `PaperIV.SplitMixedGap.mixed_gap_zero,
  `PaperIV.LinearCoefficient.linear_coefficient_optimal,
  `PaperIV.LossBudget.budget_iff,
  `PaperIV.LossBudget.erdos81_cp_form_all_orders,
  `PaperIV.ReserveIdentity.targetSize_eq_baseline_add_reserve,
  `PaperIV.ExplicitThreshold.erdos81_sharp_explicit,
  `PaperIV.ExplicitThreshold.erdos81_all_orders_bounded_additive,
  `PaperIV.DefectExplicitPublication.rooted_defect_eventual,
  `PaperIV.DefectExplicitPublication.rooted_defect_maximum,
  `PaperIV.DefectSharpPublication.exists_defect_lower_witness,
  `PaperIV.DefectSharpPublication.order_three_insufficient,
  `PaperIV.SublinearResearch.chordal_joint_stability_real,
  `PaperIV.SublinearResearch.fixed_defect_joint_stability_real,
  `PaperIV.SublinearResearch.fixed_defect_exact_extremal_edit_real,
  `PaperIV.SublinearResearch.FixedExplicit.fixed_defect_stability_explicit,
  `PaperIV.SublinearResearch.certified_shifted_fractional_bound_all_orders,
  `PaperIV.SublinearResearch.certified_refined_fractional_bound_all_orders,
  `PaperIV.SublinearResearch.uniform_shifted_partition_bound,
  `PaperIV.SublinearResearch.uniform_refined_partition_bound,
  `PaperIV.SublinearResearch.sequence_arbitrary_orders_partition_bound,
  `PaperIV.SublinearResearch.sequence_arbitrary_orders_stability,
  `PaperIV.SublinearResearch.exists_clique_additive_defect,
  `PaperIV.SublinearResearch.recover_clique_from_edit,
  `E32.cp_classification_of_theoremCPrimeC,
  `E35.theoremC_tower,
  `E35.theoremC_tower_uniform,
  `E35.theoremC_tower_uniform_sMax,
  `E35.NfarE_le_tower_poly,
  `E35.Fexp_le_tower,
  `E34.theoremC_fully_explicit_final,
  `E34.lemma11_V,
  `PaperIV.OptimalTemplateObstruction.shifted_template_witness,
  `PaperIV.OptimalTemplateObstruction.shifted_template_sqrt_witness,
  `PaperIV.OptimalTemplateObstruction.no_linear_optimal_template_bound,
  `PaperIV.OptimalTemplateObstruction.optimal_family_nonempty]

def allowed : List Name := [`propext, `Classical.choice, `Quot.sound]

elab "auditorConeReport" : command => do
  let env ← getEnv
  let mut bad := 0
  for t in publicDecls do
    match env.find? t with
    | none => logError m!"MISSING {t}"; bad := bad + 1
    | some _ =>
      let used := (cone env [t] {}).toList
      let axs := used.filter fun n => match env.find? n with
        | some (.axiomInfo _) => true | _ => false
      let erd := used.filter fun n => n.getRoot == `Erdos81
      let rem := used.filter fun n => n.getRoot == `AlonShapira || n.getRoot == `AFKS ||
        (n.getRoot == `PaperIV && (n.toString.startsWith "PaperIV.EditRoute"))
      let remThm := rem.filter fun n => match env.find? n with
        | some (.thmInfo _) => true | _ => false
      let nonStd := axs.filter fun a => !allowed.contains a
      if !nonStd.isEmpty || !erd.isEmpty then bad := bad + 1
      logInfo m!"CONE {t}: {used.length} constants; axioms={axs}; nonstd={nonStd}; Erdos81={erd.length}; AS/AFKS/EditRoute constants={rem.length} (theorems {remThm.length}): {remThm.take 12}"
  logInfo m!"AUDITOR CONE SUMMARY: {publicDecls.length} declarations; problems={bad}"

auditorConeReport

end AuditorChecks

-- Elaborated types (literal)
#check @PaperIV.Erdos81AllOrders.erdos81_all_orders_additive
#check @PaperIV.Erdos81Unconditional.erdos81_cliquePartition
#check @PaperIV.PaperTheorems.erdos81_max_eq
#check @PaperIV.DefectExplicitPublication.rooted_defect_eventual
#check @PaperIV.DefectExplicitPublication.rooted_defect_maximum
#check @PaperIV.SublinearResearch.fixed_defect_joint_stability_real
#check @PaperIV.SublinearResearch.fixed_defect_exact_extremal_edit_real
#check @PaperIV.SublinearResearch.chordal_joint_stability_real
#check @PaperIV.SublinearResearch.sequence_arbitrary_orders_stability
#check @PaperIV.OptimalTemplateObstruction.shifted_template_sqrt_witness
#check @E35.theoremC_tower_uniform
#print PaperIV.RootedSimplicialDefect.RootedDefectAt
#print PaperIV.FarRounding.CliquePartition
#print E32.IsDefectRoot
#print E32.IsCanonicalPiece
#print PaperIV.DefectComparatorGraph.defSplitGraph

#print axioms PaperIV.Erdos81AllOrders.erdos81_all_orders_additive
#print axioms PaperIV.Erdos81Unconditional.erdos81_cliquePartition
#print axioms PaperIV.PaperTheorems.erdos81_max_eq
#print axioms PaperIV.DefectExplicitPublication.rooted_defect_eventual
#print axioms PaperIV.DefectExplicitPublication.rooted_defect_maximum
#print axioms PaperIV.SublinearResearch.fixed_defect_joint_stability_real
#print axioms PaperIV.SublinearResearch.fixed_defect_exact_extremal_edit_real
#print axioms PaperIV.SublinearResearch.chordal_joint_stability_real
#print axioms PaperIV.SublinearResearch.FixedExplicit.fixed_defect_stability_explicit
#print axioms PaperIV.SublinearResearch.sequence_arbitrary_orders_stability
#print axioms PaperIV.SublinearResearch.uniform_refined_partition_bound
#print axioms PaperIV.OptimalTemplateObstruction.shifted_template_sqrt_witness
#print axioms PaperIV.OptimalTemplateObstruction.no_linear_optimal_template_bound
#print axioms E35.theoremC_tower_uniform_sMax
#print axioms E35.NfarE_le_tower_poly
#print axioms PaperIV.ExplicitThreshold.erdos81_all_orders_bounded_additive
#print axioms PaperIV.DefectSharpPublication.order_three_insufficient
#print axioms E32.cp_classification_of_theoremCPrimeC
