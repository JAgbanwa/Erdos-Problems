import PaperIV.DefectSharpPublication
import Lean.Elab.Command

#print axioms PaperIV.DefectSharpPublication.rooted_defect_eventual
#print axioms PaperIV.DefectSharpPublication.comparator_baseline_eq_target
#print axioms PaperIV.DefectSharpPublication.exists_defect_lower_witness
#print axioms PaperIV.DefectSharpPublication.rooted_defect_maximum
#print axioms PaperIV.DefectSharpPublication.order_three_insufficient
#print axioms PaperIV.RootedDefectZero.rootedDefect_zero_iff_isChordal
#print axioms PaperIV.DefectComparatorLower.cliquePartition_size_ge_defect_baseline
#print axioms PaperIV.DefectComparatorRootedDefect.rootedDefectAt_defSplitGraph

namespace PaperIV.PublicationIncrementAudit
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
  `PaperIV.DefectSharpPublication.rooted_defect_eventual,
  `PaperIV.DefectSharpPublication.comparator_baseline_eq_target,
  `PaperIV.DefectSharpPublication.exists_defect_lower_witness,
  `PaperIV.DefectSharpPublication.rooted_defect_maximum,
  `PaperIV.DefectSharpPublication.order_three_insufficient,
  `PaperIV.RootedDefectZero.rootedDefect_zero_iff_isChordal,
  `PaperIV.DefectComparatorLower.cliquePartition_size_ge_defect_baseline,
  `PaperIV.DefectComparatorRootedDefect.rootedDefectAt_defSplitGraph]

elab "auditPublicationIncrement" : command => do
  let env ← getEnv
  for t in targets do
    unless (env.find? t).isSome do throwError "Missing target: {t}"
    let used := (cone env [t] {}).toList
    let mut axioms : List Name := []
    for n in used do
      if n.toString.startsWith "Erdos81." then throwError "Forbidden namespace in {t}: {n}"
      match env.find? n with
      | some (.axiomInfo _) =>
        axioms := n :: axioms
        unless [ `propext, `Classical.choice, `Quot.sound ].contains n do
          throwError "Unapproved axiom in {t}: {n}"
      | _ => pure ()
    logInfo m!"PASS {t}: {used.length} transitive constants; axioms {axioms}"
  for n in env.header.moduleNames do
    let s := n.toString
    if s.startsWith "A4S1.T1" || s.startsWith "A4S1.TS" ||
        s == "A4S1.TerminalTwoPhase" || s.startsWith "A4S1.TerminalTolerant" ||
        s.startsWith "A4S1.OwnAll" then
      throwError "Forbidden historical module: {n}"
  logInfo "Publication increment: constant-cone, axiom whitelist and import checks PASSED."

auditPublicationIncrement
end PaperIV.PublicationIncrementAudit
