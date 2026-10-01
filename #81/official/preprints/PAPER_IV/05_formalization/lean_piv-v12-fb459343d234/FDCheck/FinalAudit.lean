import E34.L11Main
import FDCheck.Audit
import E34.L11Claim6
import E34.L11Glue
import E34.L11Claim5
import E34.L11Claim2
import E34.CoBipartite
import E34.NearlySimplicial
import E34.Gavril
import Lean.Elab.Command

/-! Independent axiom and constant-cone audit of the E34 return (Aristotle ran out of budget
before writing its own `E34/Audit.lean`). -/

#print axioms E34.lemma11_V
#print axioms E34.chordalEasyRemoval_final
#print axioms E34.editApproxExplicit_final
#print axioms E34.theoremC_fully_explicit_final
#print axioms E34.theoremC_fully_explicit_uniform_final

namespace FDCheck.FinalAudit
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

private def forbiddenConst (n : Name) : Bool :=
  let r := n.getRoot.toString
  r == "Erdos81" || r == "GalvinRoute" || r == "RouteB" || n.toString.startsWith "PaperV.B0"

private def forbiddenModule (m : Name) : Bool :=
  let s := m.toString
  let r := m.getRoot.toString
  r == "Erdos81" || r == "GalvinRoute" || r == "RouteB" || s.startsWith "PaperV.B0" ||
    s.startsWith "A4S1.T1" || s.startsWith "A4S1.TS" || s.startsWith "A4S1.OwnAll"

private def targets : List Name := [
  `E34.lemma11_V, `E34.chordalEasyRemoval_final, `E34.editApproxExplicit_final,
  `E34.theoremC_fully_explicit_final, `E34.theoremC_fully_explicit_uniform_final,
  `E33.theoremC_explicit, `FDCheck.theoremCPrime_implies_ref15Theorem11]

elab "auditFinal" : command => do
  let env ← getEnv
  for t in targets do
    unless (env.find? t).isSome do throwError "Missing target: {t}"
    let used := (cone env [t] {}).toList
    let mut axioms : List Name := []
    for n in used do
      if forbiddenConst n then throwError "Forbidden constant in {t}: {n}"
      match env.getModuleIdxFor? n with
      | some idx =>
        let m := env.header.moduleNames[idx.toNat]!
        if forbiddenModule m then throwError "Constant {n} of {t} lives in forbidden module {m}"
      | none => pure ()
      match env.find? n with
      | some (.axiomInfo _) =>
        axioms := n :: axioms
        unless [`propext, `Classical.choice, `Quot.sound].contains n do
          throwError "Unapproved axiom in {t}: {n}"
      | _ => pure ()
    logInfo m!"PASS {t}: {used.length} transitive constants; axioms {axioms}"
  for m in env.header.moduleNames do
    if forbiddenModule m then throwError "Forbidden module in the import closure: {m}"
  logInfo m!"FINAL audit PASSED: {targets.length} targets; {env.header.moduleNames.size} modules, none forbidden."

auditFinal

end FDCheck.FinalAudit
