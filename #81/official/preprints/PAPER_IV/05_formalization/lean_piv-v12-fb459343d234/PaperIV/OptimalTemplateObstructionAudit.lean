import PaperIV.OptimalTemplateObstruction
import Lean.Elab.Command

namespace PaperIV.OptimalTemplateObstructionAudit
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

private def targets : List Name := [
  `PaperIV.OptimalTemplateObstruction.optimal_family_nonempty,
  `PaperIV.OptimalTemplateObstruction.two_mul_displacementDeficit,
  `PaperIV.OptimalTemplateObstruction.deficit_bounds,
  `PaperIV.OptimalTemplateObstruction.shifted_template_witness,
  `PaperIV.OptimalTemplateObstruction.shifted_template_sqrt_witness,
  `PaperIV.OptimalTemplateObstruction.no_linear_optimal_template_bound]

elab "auditOptimalTemplateObstruction" : command => do
  let env ← getEnv
  for t in targets do
    unless (env.find? t).isSome do throwError "Missing target {t}"
  let used := cone env targets {}
  for n in used.toList do
    if ["Erdos81", "GalvinRoute", "RouteB"].contains n.getRoot.toString then
      throwError "Excluded provenance: {n}"
    match env.find? n with
    | some (.axiomInfo _) =>
      unless [`propext, `Classical.choice, `Quot.sound].contains n do
        throwError "Unapproved axiom: {n}"
    | _ => pure ()
  logInfo m!"PASS: {targets.length} obstruction declarations; union of type/value cones {used.size} constants; standard axioms only."

auditOptimalTemplateObstruction
end PaperIV.OptimalTemplateObstructionAudit
