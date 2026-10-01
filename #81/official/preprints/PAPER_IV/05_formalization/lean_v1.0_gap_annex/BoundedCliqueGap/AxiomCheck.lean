import BoundedCliqueGap.Gap
import BoundedCliqueGap.SplitBridge
import Lean.Elab.Command

/-!
# Axiom audit of `BoundedCliqueGap/`

This module is the machine-checked audit of the library:

* every declaration of `BoundedCliqueGap/` has axiom footprint contained in
  `[propext, Classical.choice, Quot.sound]` — in particular none of them uses `sorryAx`, a
  new axiom, `native_decide` or `Lean.ofReduceBool`;
* no declaration introduced here lives under a root namespace beginning with `Erdos81`;
* the partial edge-colouring structure `Vizing.PEC` is declared exactly once in the whole
  import closure, by `PaperIV/Vizing.lean`.

Each check fails the build (`throwError`) if it is violated; the informative lines are
printed with `#print axioms` at the end.
-/

open Lean Elab Command

namespace BoundedCliqueGap.Audit

/-- The permitted axioms. -/
private def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Check the axiom footprint of every declaration of the library, the absence of new
`Erdos81*` names, and the uniqueness of `Vizing.PEC`. -/
elab "boundedCliqueGapAudit" : command => do
  let env ← getEnv
  let mut checked := 0
  let mut bad : Array (Name × Name) := #[]
  let mut erdos : Array Name := #[]
  for (nm, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? nm then
      let m := env.header.moduleNames[idx.toNat]!
      if m.getRoot == `BoundedCliqueGap then
        checked := checked + 1
        if nm.getRoot.toString.startsWith "Erdos81" then
          erdos := erdos.push nm
        for a in (← collectAxioms nm) do
          if !allowedAxioms.contains a then
            bad := bad.push (nm, a)
  if !erdos.isEmpty then
    throwError "declarations under an `Erdos81*` root namespace: {erdos.toList}"
  if !bad.isEmpty then
    throwError "declarations with a forbidden axiom: {bad.toList}"
  -- `Vizing.PEC` must be declared exactly once in the whole import closure
  let pecs := env.constants.toList.filterMap fun (nm, _) =>
    if nm == `Vizing.PEC then
      match env.getModuleIdxFor? nm with
      | some idx => some env.header.moduleNames[idx.toNat]!
      | none => some `«current file»
    else none
  if pecs.length != 1 then
    throwError "`Vizing.PEC` is declared {pecs.length} times: {pecs}"
  logInfo m!"BoundedCliqueGap: {checked} declarations audited; \
axioms ⊆ [propext, Classical.choice, Quot.sound]; no `Erdos81*` name; \
`Vizing.PEC` declared once, in {pecs}"

end BoundedCliqueGap.Audit

boundedCliqueGapAudit

#print axioms BoundedCliqueGap.chordal_gap_linear_cliqueFree
#print axioms BoundedCliqueGap.chordal_gap_linear_of_cliqueTree_width
#print axioms BoundedCliqueGap.exists_cliqueTree_width_le_iff_cliqueFree
#print axioms BoundedCliqueGap.gap_linear_of_revPES
#print axioms BoundedCliqueGap.exists_revPES_of_simpleGraph_isChordal
