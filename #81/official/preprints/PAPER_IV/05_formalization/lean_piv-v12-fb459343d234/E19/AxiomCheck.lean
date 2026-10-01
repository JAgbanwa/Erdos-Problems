import E19.Main
open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  let bad := env.constants.toList.filter fun (n, _) =>
    let r := n.getRoot.toString
    r == "Erdos81" || r == "GalvinRoute" || r == "RouteB"
  IO.println s!"constants under forbidden roots: {bad.length}"
  let mods := env.header.moduleNames.filter fun m =>
    let r := m.getRoot.toString
    r == "Erdos81" || r == "GalvinRoute" || r == "RouteB"
  IO.println s!"modules under forbidden roots: {mods.size}; total modules in cone: {env.header.moduleNames.size}"
#print axioms E19.Sched.gamT_ge
#print axioms E19.Sched.TT_le
#print axioms E19.Sched.excT_ge
#print axioms E19.Sched.lominT_ge
#print axioms E19.Sched.muT_ge
#print axioms E19.Sched.DS_le
#print axioms E19.Sched.gamR_ge
#print axioms E19.GateB.gamQ_ge
#print axioms E19.G1_le
#print axioms E19.G2_le
#print axioms E19.G3_le
#print axioms E19.stepBound_le_two_pow
#print axioms E19.iterate_le_tower2
#print axioms E19.iterate_le_tower2_explicit
#print axioms E19.NfarE_eta0_le_clean
#print axioms E19.Tnum_le_tower2
#print axioms E19.NfarE_eta0_le_tower
#print axioms E19.farRegime_eta0_tower
