import FixedDefectConclusion
import E32.Comparison
import Lean.Elab.Command

/-!
# FDCheck — independent reproduction of the fixed-defect closure

Reproduces, in a lake build of the Paper IV v1.0 release tree + E32, the research modules
of `research_fixed_defect_stability_20260928` (copied verbatim as the `FixedDefect` library),
and adds:

* `FDCheck.retainedTerminalStability_all` : `E32.RetainedTerminalStability s` for every `s`;
* `FDCheck.theoremCPrime_implies_ref15Theorem11` : the quoted statement of arXiv:2609.20871v1, Theorem 1.1
  (in E32's literal restatement `E32.Ref15Theorem11Statement`), for every `s`;
* a transitive constant-cone audit (as in `E32/Audit.lean`) of every target.
-/

namespace FDCheck

theorem retainedTerminalStability_all (s : ℕ) : E32.RetainedTerminalStability s :=
  ⟨A4S1.IndepAll.epsS s, 1, 40000 * ((s : ℚ) + 1) ^ 3, _,
    A4S1.IndepAll.epsS_pos (s := s), one_pos, by positivity,
    FixedDefectStability.retainedTerminal_all s⟩

/-- All three clauses of the quoted Theorem 1.1, for every rooted defect `s`. -/
theorem theoremCPrime_implies_ref15Theorem11 (s : ℕ) : E32.Ref15Theorem11Statement s :=
  E32.ref15Theorem11_of_retained (retainedTerminalStability_all s)

end FDCheck

#print axioms FixedDefectStability.normalized_stability
#print axioms FixedDefectStability.retainedTerminal_all
#print axioms FixedDefectStability.fixed_defect_stability_all
#print axioms FixedDefectStability.fixed_defect_edit_and_size
#print axioms FDCheck.retainedTerminalStability_all
#print axioms FDCheck.theoremCPrime_implies_ref15Theorem11

namespace FDCheck.Audit
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
  `FixedDefectStability.normalized_stability,
  `FixedDefectStability.retainedTerminal_all,
  `FixedDefectStability.fixed_defect_stability_all,
  `FixedDefectStability.fixed_defect_edit_and_size,
  `FDCheck.retainedTerminalStability_all,
  `FDCheck.theoremCPrime_implies_ref15Theorem11]

elab "auditFD" : command => do
  let env ← getEnv
  for t in targets do
    unless (env.find? t).isSome do throwError "Missing target: {t}"
    let used := (cone env [t] {}).toList
    let mut axioms : List Name := []
    let mut erdosUsed : Nat := 0
    for n in used do
      if forbiddenConst n then throwError "Forbidden constant in {t}: {n}"
      match env.getModuleIdxFor? n with
      | some idx =>
        let m := env.header.moduleNames[idx.toNat]!
        if forbiddenModule m then throwError "Constant {n} of {t} lives in forbidden module {m}"
        if m.toString.startsWith "PaperIV.Erdos81" then erdosUsed := erdosUsed + 1
      | none => pure ()
      match env.find? n with
      | some (.axiomInfo _) =>
        axioms := n :: axioms
        unless [`propext, `Classical.choice, `Quot.sound].contains n do
          throwError "Unapproved axiom in {t}: {n}"
      | _ => pure ()
    logInfo m!"PASS {t}: {used.length} transitive constants; axioms {axioms}; constants from PaperIV.Erdos81*: {erdosUsed}"
  for m in env.header.moduleNames do
    if forbiddenModule m then throwError "Forbidden module in the import closure: {m}"
  logInfo m!"FDCheck audit PASSED: {targets.length} targets; {env.header.moduleNames.size} modules in the import closure, none forbidden."

auditFD

end FDCheck.Audit
