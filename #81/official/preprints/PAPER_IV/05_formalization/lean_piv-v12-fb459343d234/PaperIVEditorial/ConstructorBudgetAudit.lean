import PaperIVEditorial.ConstructorBudget
import Lean.Elab.Command

#print axioms PaperIV.Editorial.ConstructorBudget.cancel_budget
#print axioms PaperIV.Editorial.ConstructorBudget.partition_with_net_budget

namespace PaperIV.Editorial.ConstructorBudgetAudit
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

elab "auditConstructorBudget" : command => do
  let env ← getEnv
  for t in [`PaperIV.Editorial.ConstructorBudget.cancel_budget,
      `PaperIV.Editorial.ConstructorBudget.partition_with_net_budget] do
    unless (env.find? t).isSome do throwError "Missing target: {t}"
    let used := (cone env [t] {}).toList
    for n in used do
      if n.toString.startsWith "Erdos81." then
        throwError "Forbidden namespace in {t}: {n}"
      match env.find? n with
      | some (.axiomInfo _) =>
        unless [`propext, `Classical.choice, `Quot.sound].contains n do
          throwError "Unapproved axiom in {t}: {n}"
      | _ => pure ()
    logInfo m!"PASS {t}: {used.length} transitive constants; axiom whitelist passed"
  for n in env.header.moduleNames do
    let s := n.toString
    if s.startsWith "A4S1.T1" || s.startsWith "A4S1.TS" ||
        s == "A4S1.TerminalTwoPhase" || s.startsWith "A4S1.TerminalTolerant" ||
        s.startsWith "A4S1.OwnAll" then
      throwError "Forbidden historical module: {n}"
  logInfo "Constructor budget: constant-cone, axiom and historical-import checks PASSED."

auditConstructorBudget
end PaperIV.Editorial.ConstructorBudgetAudit
