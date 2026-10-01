import PaperIV.ExplicitThreshold
import E19.AxiomCheck
import Lean.Elab.Command

namespace PaperIV.ExplicitThresholdAudit
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

elab "auditExplicitThreshold" : command => do
  let env ← getEnv
  for t in [ `E17Bridge.ExplicitSchedule.uniformRoundingTarget_explicit,
      `E17Bridge.ExplicitAssembly.farRegime_allGraphs_explicit,
      `E19.NfarE_eta0_le_tower,
      `PaperIV.ExplicitThreshold.nearThreshold_le,
      `PaperIV.ExplicitThreshold.erdos81_sharp_explicit,
      `PaperIV.ExplicitThreshold.additiveConstant_le_tower,
      `PaperIV.ExplicitThreshold.erdos81_all_orders_explicit,
      `PaperIV.ExplicitThreshold.erdos81_all_orders_bounded_additive ] do
    unless (env.find? t).isSome do throwError "Missing target: {t}"
    let used := (cone env [t] {}).toList
    let mut axioms : List Name := []
    for n in used do
      if ["Erdos81", "GalvinRoute", "RouteB"].contains n.getRoot.toString ||
          n.toString.startsWith "E18.PartB." || n.toString.startsWith "E18.PartC." then
        throwError "Forbidden dependency in {t}: {n}"
      match env.find? n with
      | some (.axiomInfo _) =>
        axioms := n :: axioms
        unless [ `propext, `Classical.choice, `Quot.sound ].contains n do
          throwError "Unapproved axiom in {t}: {n}"
      | _ => pure ()
    logInfo m!"PASS {t}: {used.length} transitive constants; axioms {axioms}"

auditExplicitThreshold

#print axioms PaperIV.ExplicitThreshold.erdos81_sharp_explicit
#print axioms PaperIV.ExplicitThreshold.erdos81_all_orders_bounded_additive

end PaperIV.ExplicitThresholdAudit
