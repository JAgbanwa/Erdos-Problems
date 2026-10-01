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
  classical
  refine ⟨2 * 10 ^ 13, ?_⟩
  intro n hn G _ hG w hw hnear
  have hnQ : 2 * (10 : ℚ) ^ 13 ≤ (n : ℚ) := by exact_mod_cast hn
  -- Las dos cordalidades son ahora el mismo enunciado: `PaperIV.IsChordal` y
  -- `PaperIV.FarRounding.IsChordal` son alias (`export`) de `SimpleGraph.IsChordal`.
  have hGcopy : PaperIV.IsChordal G := hG
  obtain ⟨C, hC, hedit, hres⟩ :=
    PaperIV.NearH1Localization.exists_localized_split_core hn G hGcopy hw hnear
  let S : SimpleGraph (Fin n) :=
    PaperIV.SplitUniformIncidence.splitGraph C (Finset.univ \ C)
  letI : DecidableRel S.Adj := Classical.decRel _
  have heditS : (PaperIV.EditMetric.editDist G.edgeFinset S.edgeFinset : ℚ) ≤
      PaperIV.NearH1Calibration.eps * (n : ℚ) ^ 2 := by
    simpa [S, graphEdgeSupport_eq_edgeFinset] using hedit
  have hS : ∀ x y, S.Adj x y ↔
      (PaperIV.SplitUniformIncidence.splitGraph C (Finset.univ \ C)).Adj x y := by
    intro x y
    rfl
  simpa using
    (PaperIV.NearH1TargetAssembly.exists_target_partition_of_split_comparator
      G S hGcopy C hC hS (by simpa using hnQ)
        (PaperIV.NearH1SplitComparator.deltaCal_le (Fintype.card (Fin n) : ℚ))
        (by simpa using hres) rfl (by simpa using heditS))

/-- RC01 closes the far branch and the preceding theorem closes its exact
near complement. -/
theorem chordalTargetAt : ChordalTargetAt :=
  chordalTargetAt_of_nearRegimeAt PaperIV.NearH1Calibration.eta
    (by dsimp [PaperIV.NearH1Calibration.eta]; positivity) nearRegimeAt

end PaperIV.NearH1GlobalAssembly
