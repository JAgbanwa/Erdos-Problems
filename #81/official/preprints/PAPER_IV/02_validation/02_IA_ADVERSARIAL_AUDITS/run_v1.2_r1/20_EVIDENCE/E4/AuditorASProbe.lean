import AuditorChecks
open Lean Elab Command
/-! Auditor probe: which named removal keys (the six in FDCheck.ASCheck) and which historical
Theorem C interfaces occur in the cones of the classification and related declarations. -/
elab "auditorASProbe" : command => do
  let env ← getEnv
  let keys : List Name := [`AlonShapira.lemma_4_2, `AlonShapira.near_chordal_of_few_induced_cycles',
    `AlonShapira.near_chordal_of_induced_cycles_littleO', `PaperIV.EditRoute.editApproxAt_all,
    `PaperIV.EditRoute.fixedL4Localization_unconditional, `AFKS.strong_regularity,
    `PaperIV.DefectSharpPublication.rooted_defect_eventual, `A4S1.IndepAll.a4Sharp_all_indep,
    `E34.theoremC_fully_explicit_final, `E32.theoremC_at]
  for t in [`E32.cp_classification_of_theoremCPrimeC, `PaperIV.SublinearResearch.FixedExplicit.fixed_defect_stability_explicit,
            `PaperIV.DefectExplicitPublication.rooted_defect_maximum, `E32.ref15Theorem11_of_theoremCPrimeC,
            `FDCheck.FinalAudit.ref15_all, `PaperIV.SublinearResearch.sequence_arbitrary_orders_stability] do
    match env.find? t with
    | none => logInfo m!"PROBE {t}: not in environment"
    | some _ =>
      let used := AuditorChecks.cone env [t] {}
      logInfo m!"PROBE {t}: keys present = {keys.filter used.contains}"
auditorASProbe
