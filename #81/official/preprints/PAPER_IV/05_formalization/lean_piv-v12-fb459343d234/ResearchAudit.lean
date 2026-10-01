import RootedCliqueRecovery
import SublinearPartitionBound
import DualBudgetArithmetic
import RootStepBudget
import SublinearLocalization
import SignedDualModel
import RefinedRounding
import SublinearSequences
import ExplicitFixedStability
import ArbitraryOrderSequences
import ExtremalEditStability
import FixedDefectPieceEdges
import PublicationStability
import Lean.Elab.Command

/-! Audit of the new declarations, the sublinear stability assembly, the
refined global F4 bound, and its uniform mixed-rounding consequences. -/
namespace PaperIV.SublinearResearch.Audit
open Lean Elab Command

private partial def cone (env : Environment) : List Name → NameSet → NameSet
  | [], acc => acc
  | n :: rest, acc =>
    if acc.contains n then cone env rest acc else
      let acc := acc.insert n
      match env.find? n with
      | none => cone env rest acc
      | some ci => cone env (ci.type.getUsedConstants.toList ++
          (ci.value?.map (·.getUsedConstants.toList)).getD [] ++ rest) acc

private def targets : List Name := [
  `PaperIV.SublinearResearch.exists_clique_additive_defect,
  `PaperIV.SublinearResearch.exists_clique_of_small_missing_mass,
  `PaperIV.SublinearResearch.edit_close_of_small_defect_ratio,
  `PaperIV.SublinearResearch.uniform_chordal_edit,
  `PaperIV.SublinearResearch.uniform_sublinear_partition_bound,
  `PaperIV.SublinearResearch.exists_root_step_with_capped_budget,
  `PaperIV.SublinearResearch.exception_charge_exact,
  `PaperIV.SublinearResearch.retained_star_shift,
  `PaperIV.SublinearResearch.low_star_refined_bound,
  `PaperIV.SublinearResearch.high_star_refined_margin,
  `PaperIV.SublinearResearch.refined_gain_over_old,
  `PaperIV.SublinearResearch.ordNE_le_twice_deleted,
  `PaperIV.SublinearResearch.recover_clique_from_edit,
  `PaperIV.SublinearResearch.partition_lower_bound_transfers,
  `PaperIV.SublinearResearch.baseline_loss_on_shrinking,
  `PaperIV.SublinearResearch.stability_via_chordal_edit,
  `PaperIV.SublinearResearch.integral_baseline_le_target,
  `PaperIV.SublinearResearch.uniform_sublinear_stability,
  `PaperIV.SublinearResearch.uniform_sublinear_localization,
  `PaperIV.SublinearResearch.uniform_sublinear_fractional_localization,
  `PaperIV.SublinearResearch.signedPrice_le_one,
  `PaperIV.SublinearResearch.signed_item_sum_le_one,
  `PaperIV.SublinearResearch.signed_value_eq,
  `PaperIV.SublinearResearch.exists_certified_signed_cover,
  `PaperIV.SublinearResearch.exists_maximum_signed_star,
  `PaperIV.SublinearResearch.sum_edgesWithin_erase,
  `PaperIV.SublinearResearch.exists_bounded_signed_row,
  `PaperIV.SublinearResearch.signed_elimination_bound,
  `PaperIV.SublinearResearch.sum_pairs_triangle_bound,
  `PaperIV.SublinearResearch.signed_root_triangle_bound,
  `PaperIV.SublinearResearch.signed_root_K4_bound,
  `PaperIV.SublinearResearch.certified_star_accounts,
  `PaperIV.SublinearResearch.certified_star_accounts_strict,
  `PaperIV.SublinearResearch.high_star_exact_envelope,
  `PaperIV.SublinearResearch.small_high_envelope_shifted,
  `PaperIV.SublinearResearch.small_high_envelope_refined,
  `PaperIV.SublinearResearch.certified_refined_fractional_bound,
  `PaperIV.SublinearResearch.certified_shifted_fractional_bound,
  `PaperIV.SublinearResearch.certified_shifted_fractional_bound_all_orders,
  `PaperIV.SublinearResearch.certified_refined_fractional_bound_all_orders,
  `PaperIV.SublinearResearch.uniform_shifted_partition_bound,
  `PaperIV.SublinearResearch.uniform_refined_partition_bound,
  `PaperIV.SublinearResearch.rational_isLittleO_iff,
  `PaperIV.SublinearResearch.exists_minimum_rootScore,
  `PaperIV.SublinearResearch.rootScore_components,
  `PaperIV.SublinearResearch.rootScore_le_of_localization,
  `PaperIV.SublinearResearch.noncanonical_le_rootScore,
  `PaperIV.SublinearResearch.exists_minimum_order_four_partition,
  `PaperIV.SublinearResearch.sequence_sublinear_partition_bound,
  `PaperIV.SublinearResearch.sequence_sublinear_stability,
  `PaperIV.SublinearResearch.FixedExplicit.stabilityGamma_pos,
  `PaperIV.SublinearResearch.FixedExplicit.minimumDegree_stability_explicit,
  `PaperIV.SublinearResearch.FixedExplicit.edit_stability_explicit,
  `PaperIV.SublinearResearch.FixedExplicit.fixed_defect_stability_explicit,
  `PaperIV.SublinearResearch.FixedExplicit.fixed_defect_edit_and_size_explicit,
  `PaperIV.SublinearResearch.piece_edges_le_ten_defect,
  `PaperIV.SublinearResearch.piece_edges_coefficient_sharp,
  `PaperIV.SublinearResearch.noncanonicalEdgeMass_le_sum_defect,
  `PaperIV.SublinearResearch.noncanonicalEdgeMass_le,
  `PaperIV.SublinearResearch.noncanonicalEdgeMass_le_rootScore,
  `PaperIV.SublinearResearch.chordal_partition_edge_stability,
  `PaperIV.SublinearResearch.sequence_arbitrary_orders_partition_bound,
  `PaperIV.SublinearResearch.sequence_arbitrary_orders_stability,
  `PaperIV.SublinearResearch.optimal_core_distance_sq,
  `PaperIV.SublinearResearch.fixed_defect_optimal_size_distance,
  `PaperIV.SublinearResearch.exists_resize_core,
  `PaperIV.SublinearResearch.comparator_resize_edit_le,
  `PaperIV.SublinearResearch.exists_optimal_comparator_near_root,
  `PaperIV.SublinearResearch.fixed_defect_exact_extremal_edit,
  `E32.noncanonical_edge_mass_le,
  `PaperIV.SublinearResearch.fixed_defect_partition_edge_stability,
  `PaperIV.SublinearResearch.lower_bound_floor_deficit,
  `PaperIV.SublinearResearch.fixed_defect_joint_stability_real,
  `PaperIV.SublinearResearch.fixed_defect_exact_extremal_edit_real,
  `PaperIV.SublinearResearch.chordal_joint_stability_real]

elab "auditSublinearResearch" : command => do
  let env ← getEnv
  for t in targets do
    unless (env.find? t).isSome do throwError "Missing target: {t}"
    let used := (cone env [t] {}).toList
    let mut axioms : List Name := []
    for n in used do
      if ["Erdos81", "GalvinRoute", "RouteB"].contains n.getRoot.toString then
        throwError "Forbidden namespace in {t}: {n}"
      match env.find? n with
      | some (.axiomInfo _) =>
        axioms := n :: axioms
        unless [`propext, `Classical.choice, `Quot.sound].contains n do
          throwError "Unapproved axiom in {t}: {n}"
      | _ => pure ()
    logInfo m!"PASS {t}: {used.length} constants; axioms {axioms}"
  logInfo m!"Sublinear research audit PASSED: {targets.length} targets."

auditSublinearResearch
end PaperIV.SublinearResearch.Audit
