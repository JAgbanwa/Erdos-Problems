import E17.ImprovedFarRounding
import Lean.Elab.Command

namespace E17Bridge.B7Audit
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

elab "auditB7" : command => do
  let env ← getEnv
  for t in [ `E17Bridge.faceTransfer_loss,
      `E17Bridge.faceTransfer_weight_four,
      `E17Bridge.profileCleanup_loss,
      `E17Bridge.profileCleanup_zero_or_heavy,
      `E17Bridge.profileCleanup_offCanonical_zero,
      `E17Bridge.profileCleanup_triangleMass_loss,
      `E17Bridge.exists_improvedGateGap_of_high_mass,
      `E17Bridge.cleanedR3_loss,
      `E17Bridge.UniformSchedule.uniformRoundingTarget_via_r3_f1,
      `E17Bridge.exists_improvedGateGap_eventually,
      `E17Bridge.improved_far_loss_eventually ] do
    unless (env.find? t).isSome do throwError "Missing target: {t}"
    let used := (cone env [t] {}).toList
    let mut axioms : List Name := []
    for n in used do
      if n.toString.startsWith "PaperIV.RC01Final." then
        throwError "Circular final-rounding dependency in {t}: {n}"
      match env.find? n with
      | some (.axiomInfo _) =>
        axioms := n :: axioms
        unless [ `propext, `Classical.choice, `Quot.sound ].contains n do
          throwError "Unapproved axiom in {t}: {n}"
      | _ => pure ()
    logInfo m!"PASS {t}: {used.length} transitive constants; axioms {axioms}"

auditB7
end E17Bridge.B7Audit
