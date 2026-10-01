import E34.L11Main
import Lean.Elab.Command

/-!
# E34 — audit

1. `#print axioms` for every E34 deliverable (expected: `[propext, Classical.choice,
   Quot.sound]`).
2. `auditE34`: for each target, walks the **transitive constant cone** (types and values)
   and fails if it meets `sorryAx`, a non-standard axiom, or a constant whose name has root
   `Erdos81`, `GalvinRoute`, `RouteB`, or prefix `PaperV.B0`, `A4S1.T1`, `A4S1.TS`,
   `A4S1.OwnAll`.  For information it also counts cone constants from the namespaces
   `PaperIV.Erdos81Unconditional` / `PaperIV.Erdos81AllOrders`.
3. An `#eval` over the **import cone** fails if a module has root `Erdos81`, `GalvinRoute`,
   `RouteB`, or prefix `PaperV.B0`, `A4S1.T1`, `A4S1.TS`, `A4S1.OwnAll`; it reports (without
   failing) the Paper IV modules whose name contains `Erdos81`.
-/

namespace E34.Audit
open Lean Elab Command

def forbiddenName (n : Name) : Bool :=
  let s := n.toString
  ["Erdos81", "GalvinRoute", "RouteB"].contains n.getRoot.toString ||
    s.startsWith "PaperV.B0" || s.startsWith "A4S1.T1" || s.startsWith "A4S1.TS" ||
    s.startsWith "A4S1.OwnAll"

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

elab "auditE34" : command => do
  let env ← getEnv
  for t in [`E34.lemma11_V, `E34.chordalEasyRemoval_final, `E34.editApproxExplicit_final,
      `E34.theoremC_fully_explicit_final, `E34.theoremC_fully_explicit_uniform_final,
      `E34.indCopies_cycle_le, `E34.coBipartite_edit_le, `E34.lemma3, `E34.thm1_of_lemma11,
      `E34.chordalEasyRemoval_V, `E34.editApproxExplicit_V, `E34.theoremC_fully_explicit,
      `E34.theoremC_fully_explicit_uniform, `E34.SetColoring.thm2, `E34.thm6,
      `E34.properOn_of_pinned, `E34.claim5_count, `E34.glueGraph_chordal,
      `E34.editDist_glue_le, `E34.thm2_ineq, `E34.block_ineq] do
    unless (env.find? t).isSome do throwError "Missing target: {t}"
    let used := (cone env [t] {}).toList
    let mut axioms : List Name := []
    let mut e81 : Nat := 0
    for n in used do
      if forbiddenName n then
        throwError "Forbidden dependency in {t}: {n}"
      if n.toString.startsWith "PaperIV.Erdos81Unconditional" ||
          n.toString.startsWith "PaperIV.Erdos81AllOrders" then
        e81 := e81 + 1
      match env.find? n with
      | some (.axiomInfo _) =>
        axioms := n :: axioms
        unless [`propext, `Classical.choice, `Quot.sound].contains n do
          throwError "Unapproved axiom in {t}: {n}"
      | _ => pure ()
    logInfo m!"PASS {t}: {used.length} transitive constants; axioms {axioms}; constants from PaperIV.Erdos81* namespaces: {e81}"

auditE34

end E34.Audit

open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  let mods := env.header.moduleNames
  let bad := mods.filter E34.Audit.forbiddenName
  let e81 := mods.filter fun m => (m.toString.splitOn "Erdos81").length > 1
  IO.println s!"modules in the import cone of E34.Audit: {mods.size}"
  IO.println s!"forbidden modules (roots Erdos81/GalvinRoute/RouteB, PaperV.B0*, A4S1.T1*, A4S1.TS*, A4S1.OwnAll*): {bad.toList}"
  IO.println s!"Paper IV modules whose name contains Erdos81 (informational): {e81.toList}"
  unless bad.isEmpty do throwError "E34 import-cone check FAILED"
  IO.println "E34 import-cone check PASSED"

#print axioms E34.lemma11_V
#print axioms E34.chordalEasyRemoval_final
#print axioms E34.editApproxExplicit_final
#print axioms E34.theoremC_fully_explicit_final
#print axioms E34.theoremC_fully_explicit_uniform_final
#print axioms E34.indCopies_cycle_le
#print axioms E34.coBipartite_edit_le
#print axioms E34.lemma3
#print axioms E34.thm1_of_lemma11
#print axioms E34.SetColoring.thm2
#print axioms E34.thm6
#print axioms E34.glueGraph_chordal
#print axioms E34.editDist_glue_le
