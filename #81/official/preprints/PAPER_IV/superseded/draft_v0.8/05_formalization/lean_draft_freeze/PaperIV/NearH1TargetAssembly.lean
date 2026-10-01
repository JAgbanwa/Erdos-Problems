import PaperIV.NearH1StructureWitness
import PaperIV.NearRegimePackingInterface

/-! # End-to-end near-H1 target assembly

The calibrated split comparator, root regularization, literal phase I and the
physical RD09 accounts are composed once, in
`PaperIV.NearH1StructureWitness`.  This file only projects that structural
package through the target-size packing bridge.  No scalar or ledger hypothesis
remains in the conclusion.
-/

namespace PaperIV.NearH1TargetAssembly

open PaperIV.FarRounding

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

/-- A calibrated split comparator produces a literal clique partition of the
original graph with order at most four and the target number of pieces. -/
theorem exists_target_partition_of_split_comparator
    (G S : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel S.Adj]
    (hchordal : PaperIV.IsChordal G) (C : Finset V) (hC : C.Nonempty)
    (hS : ∀ x y, S.Adj x y ↔
      (PaperIV.SplitUniformIncidence.splitGraph C (Finset.univ \ C)).Adj x y)
    {delta residual : ℚ}
    (hn : 2 * (10 : ℚ) ^ 13 ≤ (Fintype.card V : ℚ))
    (hdelta : delta ≤ (PaperIV.NearH1Calibration.eta +
      6 * PaperIV.NearH1Calibration.eps) * (Fintype.card V : ℚ) ^ 2 +
      (Fintype.card V : ℚ) / 6 + 1 / 24)
    (hres : residual ^ 2 ≤ 24 * delta)
    (hresDef : residual = 6 * (C.card : ℚ) -
      2 * (Fintype.card V : ℚ) - 1)
    (hedit : (PaperIV.EditMetric.editDist G.edgeFinset S.edgeFinset : ℚ) ≤
      PaperIV.NearH1Calibration.eps * (Fintype.card V : ℚ) ^ 2) :
    ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧
      Q.size ≤ targetSize (Fintype.card V) := by
  obtain ⟨W⟩ :=
    PaperIV.NearH1StructureWitness.exists_nearStructureWitness_of_split_comparator
      G S hchordal C hC hS hn hdelta hres hresDef hedit
  exact PaperIV.NearRegimePacking.exists_cliquePartition_target_of_physicalAccounts
    W.isPacking W.accounts W.accounts_order

end PaperIV.NearH1TargetAssembly
