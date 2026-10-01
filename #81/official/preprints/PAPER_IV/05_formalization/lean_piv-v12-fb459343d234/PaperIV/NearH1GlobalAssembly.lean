import PaperIV.NearH1Localization
import PaperIV.NearH1TargetAssembly
import PaperIV.RC01FarAssembly

set_option maxHeartbeats 1000000

/-!
# Global assembly of the independent near-H1 route

The descent localization of `PaperIV.NearH1Localization` places the near graph
in the `eps`-neighbourhood of the split family and produces a literal split
core.  That comparator is fed once to the already compiled H1 constructor.  No
inverse transport of a terminal packing is used.
-/

namespace PaperIV.NearH1GlobalAssembly

open PaperIV.FarRounding PaperIV.VertexCopyGate
open PaperIV.GraphFamilyDistance PaperIV.SplitComparatorFamily
open PaperIV.RC01FarAssembly

/-- The fixed near parameter used by the independent H1 route. -/
theorem nearRegimeAt : NearRegimeAt PaperIV.NearH1Calibration.eta := by
  refine ⟨4 * 10 ^ 12, ?_⟩
  intro n hn G _ hG w hw hnear
  -- Las dos cordalidades son ahora el mismo enunciado: `PaperIV.IsChordal` y
  -- `PaperIV.FarRounding.IsChordal` son alias (`export`) de `SimpleGraph.IsChordal`.
  -- La composición «descenso → comparador → testigo» está factorizada en
  -- `NearH1Localization`; aquí sólo se proyecta el testigo por el puente físico de conteo.
  obtain ⟨W⟩ :=
    PaperIV.NearH1Localization.exists_nearStructureWitness_of_nearRegime
      hn G hG hw hnear
  simpa using
    PaperIV.NearRegimePacking.exists_cliquePartition_target_of_physicalAccounts
      W.isPacking W.accounts W.accounts_order

/-- RC01 closes the far branch and the preceding theorem closes its exact
near complement. -/
theorem chordalTargetAt : ChordalTargetAt :=
  chordalTargetAt_of_nearRegimeAt PaperIV.NearH1Calibration.eta
    (by dsimp [PaperIV.NearH1Calibration.eta]; positivity) nearRegimeAt

end PaperIV.NearH1GlobalAssembly
