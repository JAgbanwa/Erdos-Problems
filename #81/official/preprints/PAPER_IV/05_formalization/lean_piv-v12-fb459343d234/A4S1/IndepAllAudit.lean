import A4S1.IndepAllMain

/-!
# E14: axiom audit and machine check of the import cone

Every result below prints `[propext, Classical.choice, Quot.sound]` (no `sorryAx`, no
`Lean.ofReduceBool`, no new axiom).

The `#eval` at the end walks the **transitive** import closure of this file (hence of
`A4S1.IndepAllMain`, its only import), prints its size, and **fails the build** if the cone
contains a forbidden module:

* every `A4S1.T1*` and every `A4S1.TS*` module;
* `A4S1.TerminalTwoPhase`, `A4S1.TerminalTolerantTwoPhase`, every `A4S1.TerminalTolerant*`;
* every `A4S1.OwnAll*` module (in particular `OwnAllConstructor` and `OwnAllPairs`, which
  import `A4S1.T1Cases` / `A4S1.T1Tools`);
* any module of the cone that directly imports one of the above (checked separately, although
  it is implied by the closure of the cone under imports).

For information it also reports whether the note-§1 modules `A4S1.TerminalPhaseOne`,
`A4S1.TerminalColouring`, `A4S1.TerminalExactComparator` occur (they do not).
-/

open A4S1.Indep A4S1.IndepAll

-- G2 and the terminal
#print axioms a4Sharp_all_indep
#print axioms minDegTerminal_all_indep
#print axioms minDegTerminal_ge_two_indep
#print axioms AllInput.partition
#print axioms AllInput.params
#print axioms AllInput.hkey
-- G1 and its new ingredients
#print axioms caseA_indep
#print axioms exists_absorption_matchings
#print axioms min_le_of_selection
#print axioms exists_shift_lift_ge
#print axioms shiftCost_phaseOneGain
#print axioms sum_phaseOneGain
#print axioms exists_partition_of_three_families
#print axioms card_absorptionTriangles
#print axioms absorptionTriangles_inter
#print axioms card_edgeFinset_le_parts
#print axioms maxDegree_rowGraph_add_one_le
#print axioms abs_inter_lift
#print axioms abs_inter_hosted
#print axioms lift_inter_hosted
#print axioms abs_inter_abs
-- neutral helpers re-proved for the copied accounting
#print axioms A4S1.IndepAll.sum_card_filter_adj_le
#print axioms A4S1.IndepAll.card_inEdges_union_le
#print axioms A4S1.IndepAll.classCeiling_mul_le
#print axioms A4S1.IndepAll.crossCount_singleton
#print axioms A4S1.IndepAll.own_final_all

/-- The forbidden modules of E14. -/
def e14Forbidden (n : Lean.Name) : Bool :=
  let s := n.toString
  s.startsWith "A4S1.T1" || s.startsWith "A4S1.TS" ||
    s == "A4S1.TerminalTwoPhase" || s.startsWith "A4S1.TerminalTolerant" ||
    s.startsWith "A4S1.OwnAll"

open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  let mods := env.header.moduleNames
  let data := env.header.moduleData
  let mut bad : Array Name := #[]
  let mut badImporters : Array Name := #[]
  let mut a4 : Array Name := #[]
  for i in [0:mods.size] do
    let n := mods[i]!
    if n.toString.startsWith "A4S1." then a4 := a4.push n
    if e14Forbidden n then bad := bad.push n
    if h : i < data.size then
      for imp in data[i].imports do
        if e14Forbidden imp.module then badImporters := badImporters.push n
  IO.println s!"modules in the import cone of A4S1.IndepAllAudit: {mods.size}"
  IO.println s!"A4S1 modules in the cone ({a4.size}): {a4.toList}"
  for m in [`A4S1.TerminalPhaseOne, `A4S1.TerminalColouring, `A4S1.TerminalExactComparator] do
    IO.println s!"{m} in cone: {mods.contains m}"
  IO.println s!"forbidden modules in the cone: {bad.toList}"
  IO.println s!"cone modules importing a forbidden module: {badImporters.toList}"
  unless bad.isEmpty && badImporters.isEmpty do
    throwError "E14 cone check FAILED"
  IO.println "E14 cone check PASSED"
