import PaperIV.ExplicitThreshold
import Lean.Elab.Command

namespace E17Bridge.ExplicitAudit
open Lean Elab Command

private partial def cone (env : Environment) : List Name → NameSet → NameSet
  | [], acc => acc
  | n :: rest, acc =>
    if acc.contains n then cone env rest acc
    else
      let acc := acc.insert n
      match env.find? n with
      | none => cone env rest acc
      | some ci => cone env (ci.type.getUsedConstants.toList ++
          (ci.value?.map (·.getUsedConstants.toList)).getD [] ++ rest) acc

/-- Check the actual proof, not merely imported modules or its axiom fingerprint. -/
elab "auditExplicitB7" : command => do
  let env ← getEnv
  for t in [ `E17Bridge.ExplicitSchedule.uniformRoundingTarget_explicit,
      `E17Bridge.exists_improvedGateGap_explicit,
      `E17Bridge.improved_far_loss_explicit,
      `E17Bridge.ExplicitAssembly.uniformTransferAt_explicit,
      `E17Bridge.ExplicitAssembly.farRegime_allGraphs_explicit,
      `E17Bridge.ExplicitAssembly.farRegime_eta0_tower,
      `PaperIV.ExplicitThreshold.erdos81_sharp_explicit,
      `PaperIV.ExplicitThreshold.erdos81_all_orders_explicit,
      `PaperIV.ExplicitThreshold.erdos81_all_orders_bounded_additive ] do
    unless (env.find? t).isSome do throwError "Missing target: {t}"
    let used := cone env [t] {}
    for required in [ `E17Bridge.cleanedR3_original_triangle_le_profiles_oldBudget,
        `E17Bridge.cleanedR3_original_value_le_profiles_oldBudget ] do
      unless used.contains required do
        throwError "R3/F1 proof link missing in {t}: {required}"
    let mut axioms : List Name := []
    for n in used.toList do
      if [ `PaperIV.RC01Final.rc01_uniformRoundingTarget,
          `E18.rc01_uniformRoundingTarget_explicit,
          `E18.uniformTransferAt_explicit,
          `E18.farRegime_allGraphs_explicit,
          `E19.farRegime_eta0_tower ].contains n then
        throwError "Old final rounder used in {t}: {n}"
      if ["Erdos81", "GalvinRoute", "RouteB"].contains n.getRoot.toString ||
          n.toString.startsWith "E18.PartB." || n.toString.startsWith "E18.PartC." then
        throwError "Forbidden dependency in {t}: {n}"
      match env.find? n with
      | some (.axiomInfo _) =>
        axioms := n :: axioms
        unless [ `propext, `Classical.choice, `Quot.sound ].contains n do
          throwError "Unapproved axiom in {t}: {n}"
      | _ => pure ()
    logInfo m!"PASS B7 numerical link {t}: {used.toList.length} constants; axioms {axioms}"

auditExplicitB7
#print axioms E17Bridge.improved_far_loss_explicit
#print axioms PaperIV.ExplicitThreshold.erdos81_all_orders_bounded_additive
end E17Bridge.ExplicitAudit
