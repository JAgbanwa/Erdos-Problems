import E35.Theorem
import Lean.Elab.Command

/-! # E35 — axiom and constant-cone audit (cone walk copied from `FDCheck/FinalAudit.lean`) -/

#print axioms E35.NE_le_tower
#print axioms E35.NfarE_le_tower
#print axioms E35.NfarE_le_tower_poly
#print axioms E35.NeditE_le_tower
#print axioms E35.Fexp_le_tower
#print axioms E35.theoremC_tower
#print axioms E35.theoremC_tower_uniform
#print axioms E35.theoremC_tower_uniform_sMax

namespace E35.Audit
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
  let s := n.toString
  let r := n.getRoot.toString
  r == "Erdos81" || r == "GalvinRoute" || r == "RouteB" || s.startsWith "PaperV.B0" ||
    s.startsWith "A4S1.T1" || s.startsWith "A4S1.TS" || s.startsWith "A4S1.OwnAll"

private def forbiddenModule (m : Name) : Bool :=
  let s := m.toString
  let r := m.getRoot.toString
  r == "Erdos81" || r == "GalvinRoute" || r == "RouteB" || s.startsWith "PaperV.B0" ||
    s.startsWith "A4S1.T1" || s.startsWith "A4S1.TS" || s.startsWith "A4S1.OwnAll"

private def targets : List Name := [
  `E35.NE_le_tower, `E35.NfarE_le_tower, `E35.NfarE_le_tower_poly, `E35.NeditE_le_tower,
  `E35.Fexp_le_tower, `E35.theoremC_tower, `E35.theoremC_tower_uniform,
  `E35.theoremC_tower_uniform_sMax]

elab "auditE35" : command => do
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
  logInfo m!"E35 audit PASSED: {targets.length} targets; {env.header.moduleNames.size} modules, none forbidden."

auditE35

end E35.Audit
