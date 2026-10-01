import PaperIV.PaperTheorems
import PaperIV.Erdos81AllOrders
import PaperIV.SplitCompleteRigidity
import PaperIV.SplitCompleteDefect
import PaperIV.LinearCoefficient
import PaperIV.BalancedReserve
import PaperIV.SplitMixedGap
import PaperIV.SimplicialReduction
import PaperIV.SimplicialReductionRefined
import PaperIV.SpreadLedgerAbsorption
import PaperIV.SpreadAbsorptionCompatibility
import PaperIV.IntegralStability
import PaperIV.ExtremalClassification
import PaperIV.SeparationAbsorptionRoute
import PaperIV.NearThresholdSensitivity
import PaperIV.FourHostClosure
import PaperIV.ReserveIdentity
import PaperIV.LossBudget
import Lean.Elab.Command

/-!
# Auditoría por cono de constantes

`#print axioms` dice de qué **axiomas** depende un teorema. No dice de qué **desarrollos**
depende. Para eso hace falta recorrer el cono transitivo de constantes —tipo y valor de cada
declaración— y mirar de qué módulo viene cada una.

Los imports mienten: un módulo puede importar medio árbol y usar tres lemas. Lo que cuenta es
qué constantes aparecen realmente en el término de la demostración.

## Qué comprueba este fichero

Para cada enunciado del paper:

* **veto duro** — que no aparezca ninguna constante del espacio de nombres raíz `Erdos81`, que es
  el del desarrollo externo publicado. Cualquier aparición es un fallo y se imprime con nombre;
* **reparto por procedencia** — cuántas constantes vienen de `PaperI`, del nibble de Paper III,
  de la librería neutral del modelo mixto, de material propio de Paper IV, y cuántas de Mathlib
  o del núcleo.

El veto es lo que permite afirmar que el teorema principal **no usa** el desarrollo publicado.
Nótese que `PaperIV.Erdos81Unconditional` contiene la cadena «Erdos81» en su nombre y es
material propio: el veto mira el **espacio de nombres raíz**, no la subcadena.
-/

open Lean Elab Command

namespace PaperIV.ConeAudit

private partial def cone (env : Environment) : List Name → NameSet → NameSet
  | [], acc => acc
  | n :: rest, acc =>
      if acc.contains n then cone env rest acc
      else
        let acc := acc.insert n
        match env.find? n with
        | none => cone env rest acc
        | some info =>
            let fromType := info.type.getUsedConstants.toList
            let fromValue := match info.value? with
              | some v => v.getUsedConstants.toList
              | none => []
            cone env (fromType ++ fromValue ++ rest) acc

/-- Espacio de nombres raíz de una constante. -/
private def rootNs (n : Name) : Name :=
  match n.components with
  | c :: _ => c
  | [] => n

/-- Los enunciados del paper, en el mismo orden que `PaperIV/Audit.lean`. -/
private def targets : List Name :=
  [ `PaperIV.Erdos81AllOrders.erdos81_all_orders,
    `PaperIV.Erdos81AllOrders.erdos81_all_orders_additive,
    `PaperIV.Erdos81Unconditional.erdos81_cliquePartition,
    `PaperIV.Erdos81Unconditional.erdos81_linear_form,
    `PaperIV.Erdos81Unconditional.erdos81_chordalTarget,
    `PaperIV.CertifiedOptimumExistence.exists_certifiedFractionalOptimum,
    `PaperI.FiniteLP.exists_optimal_pair,
    `PaperIV.RC01Final.rc01_uniformRoundingTarget,
    `PaperIV.RC01FarAssembly.farRegime_cliquePartition,
    `PaperIV.NearH1GlobalAssembly.nearRegimeAt,
    `PaperIV.NearH1GlobalAssembly.chordalTargetAt,
    `PaperIV.RootRegularizationBridge.exists_regularizedRoot_engineFree,
    `PaperIV.HybridDichotomy.chordal_far_or_nearStructure,
    `PaperIV.HybridDichotomy.chordal_near_extremal_stability,
    `PaperIV.HybridDichotomy.erdos81_of_structuralDichotomy,
    `PaperIV.PaperTheorems.erdos81_hybrid_linear_form,
    `PaperIV.PaperTheorems.splitGraph_isChordal,
    `PaperIV.PaperTheorems.exists_chordal_extremal_witness,
    `PaperIV.PaperTheorems.erdos81_max_eq,
    `PaperIV.SplitCompleteExactValue.exists_optimal_cliquePartition,
    `PaperIV.SplitCompleteExactValueAllParities.exists_optimal_cliquePartition_allParities,
    `PaperIV.SplitCompleteSharpLower.cliquePartition_size_ge_baseline_unrestricted,
    `PaperIV.SplitCompleteSharpValue.exists_sharp_cliquePartition_allParities,
    `PaperIV.SplitCompleteSharpLower.critical_baseline_eq_targetSize,
    `PaperIV.SplitCompleteRigidity.baseline_eq_targetSize_iff,
    `PaperIV.SplitCompleteRigidity.optimal_cores,
    `PaperIV.SplitCompleteDefect.size_add_choose_eq_mul_add_sum_defect,
    `PaperIV.SplitMixedGap.mixed_gap_zero,
    `PaperIV.SimplicialReduction.sharpBoundAt_of_largeCliqueRegime,
    `PaperIV.SimplicialReductionRefined.not_strongLoosePieceHypothesis,
    `PaperIV.SplitCompleteDefect.card_paying_pieces_le_excess,
    `PaperIV.LinearCoefficient.linear_coefficient_optimal,
    `PaperIV.SpreadAbsorptionCompatibility.exists_budgeted_compatible_spread_absorber,
    `PaperIV.BalancedReserve.exists_balanced_reserve,
    `PaperIV.SpreadAbsorption.exists_certificate,
    `PaperIV.SpreadAbsorption.exists_lowConflict_certificate,
    `PaperIV.SpreadAbsorption.physical_triangle_absorber,
    `PaperIV.SpreadAbsorption.exists_budgeted_physical_triangle_absorber,
    `PaperIV.SpreadLedgerAbsorption.total_ledgerBad_le_paid_mass,
    `PaperIV.SpreadLedgerAbsorption.exists_spread_absorber_count_add_cost_le_baseline,
    `PaperIV.SpreadAbsorptionCompatibility.exists_compatible_spread_absorber,
    `PaperIV.SeparationAbsorptionRoute.erdos81_of_dualSeparation_absorption,
    `PaperIV.SplitEditIdentity.editDist_split_eq,
    `PaperIV.FarSlackQuantitative.farRegime_cliquePartition_slack,
    `PaperIV.IntegralStability.chordal_linear_stability,
    `PaperIV.ExtremalClassification.split_value,
    `PaperIV.ExtremalClassification.chordal_extremal_classification,
    `PaperIV.NearThresholdSensitivity.eps_le_of_physical_budget,
    `PaperIV.NearThresholdSensitivity.near_threshold_of_budget,
    `PaperIV.NearThresholdSensitivity.edit_mass_of_budget,
    `PaperIV.FourHostClosure.exists_fourHost_packing,
    `PaperIV.ReserveIdentity.targetSize_eq_baseline_add_reserve,
    `PaperIV.ReserveIdentity.baseline_eq_targetSize_iff_reserve,
    `PaperIV.ReserveIdentity.residual_sq_le_iff,
    `PaperIV.LossBudget.budget_iff,
    `PaperIV.LossBudget.erdos81_cp_form,
    `PaperIV.LossBudget.erdos81_cp_form_all_orders ]

elab "coneAudit" : command => do
  let env ← getEnv
  let mut totalViolations := 0
  let mut missing : List Name := []
  for t in targets do
    if (env.find? t).isNone then
      missing := missing ++ [t]
    else
      let used := (cone env [t] {}).toList
      let mut ext : List Name := []
      let mut nPaperI := 0
      let mut nNibble := 0
      let mut nMixed := 0
      let mut nPaperIV := 0
      for nm in used do
        match rootNs nm with
        | `Erdos81      => ext := ext ++ [nm]
        | `PaperI       => nPaperI := nPaperI + 1
        | `Nibble       => nNibble := nNibble + 1
        | `MixedRounding => nMixed := nMixed + 1
        | `PaperIV      => nPaperIV := nPaperIV + 1
        | _             => pure ()
      totalViolations := totalViolations + ext.length
      let flag := if ext.isEmpty then "OK  " else "FALLO"
      logInfo m!"{flag} {t}\n      total {used.length} | PaperIV {nPaperIV} | PaperI {nPaperI} | Nibble {nNibble} | MixedRounding {nMixed} | EXTERNO {ext.length}"
      unless ext.isEmpty do
        logError m!"  constantes del desarrollo externo en {t}: {ext.take 20}"
  unless missing.isEmpty do
    logError m!"enunciados ausentes del entorno: {missing}"
  if totalViolations == 0 && missing.isEmpty then
    logInfo m!"VEREDICTO: los {targets.length} enunciados del paper no usan ninguna constante del espacio de nombres `Erdos81`."
  else
    logError m!"VEREDICTO: {totalViolations} constantes externas en el cono."

coneAudit

end PaperIV.ConeAudit
