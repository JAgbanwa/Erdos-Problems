import PaperIV.DefectExplicitPublication
import PublicationStability
import ArbitraryOrderSequences
import Lean.Elab.Command

/-! Provenance check for the current publication chain, not a ban on definitions
whose historical namespace is AlonShapira. The legacy route is reported separately. -/
namespace FDCheck.ASCheck
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

private def removalKeys : List Name := [
  `AlonShapira.lemma_4_2, `AlonShapira.near_chordal_of_few_induced_cycles',
  `AlonShapira.near_chordal_of_induced_cycles_littleO', `PaperIV.EditRoute.editApproxAt_all,
  `PaperIV.EditRoute.fixedL4Localization_unconditional, `AFKS.strong_regularity]

private def selected : List Name := [
  `PaperIV.DefectExplicitPublication.rooted_defect_eventual,
  `PaperIV.DefectExplicitPublication.rooted_defect_maximum,
  `E35.theoremC_tower,
  `PaperIV.SublinearResearch.FixedExplicit.fixed_defect_stability_explicit,
  `PaperIV.SublinearResearch.fixed_defect_joint_stability_real,
  `PaperIV.SublinearResearch.sequence_arbitrary_orders_stability]

elab "checkPublicationRemoval" : command => do
  let env ← getEnv
  for t in selected do
    unless (env.find? t).isSome do throwError "Missing target: {t}"
    let used := cone env [t] {}
    let found := removalKeys.filter used.contains
    unless found.isEmpty do throwError "Removal dependency in {t}: {found}"
    for n in used.toList do
      match env.find? n with
      | some (.axiomInfo _) =>
        unless [`propext, `Classical.choice, `Quot.sound].contains n do
          throwError "Unapproved axiom in {t}: {n}"
      | _ => pure ()
    logInfo m!"PASS {t}: {used.size} constants; no listed Alon–Shapira removal lemmas; standard axioms only."
  let historical := cone env [`PaperIV.DefectSharpPublication.rooted_defect_eventual] {}
  logInfo m!"HISTORICAL route removal dependencies: {removalKeys.filter historical.contains}"

checkPublicationRemoval
#print axioms PaperIV.DefectExplicitPublication.rooted_defect_eventual
#print axioms PaperIV.DefectExplicitPublication.rooted_defect_maximum

end FDCheck.ASCheck

