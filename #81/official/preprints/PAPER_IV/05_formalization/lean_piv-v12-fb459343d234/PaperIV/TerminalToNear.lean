import PaperIV.TerminalLedger
import PaperIV.TwoRegimeAssembly

/-!
# From a physical terminal ledger to the near-regime certificate

The terminal construction remains responsible for producing `PhysicalTerminal`.
This adapter is intentionally smaller: it records that the *literal completed
partition* it produces is exactly the direct witness consumed by the near arm
of the two-regime assembly.
-/

namespace PaperIV.TerminalToNear

open PaperIV.Model PaperIV.PhysicalCompletion
open PaperIV.TerminalLedger PaperIV.TwoRegimeAssembly

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A paid terminal whose baseline is below the common target supplies the
numerical near-regime witness. -/
theorem nearCertificate_of_physicalTerminal
    {Q : ℚ} (T : PhysicalTerminal (G := G))
    (hbase : T.base ≤ Q) (hmissing : 0 ≤ T.missing)
    (hrootLoss : 0 ≤ T.rootLoss) :
    NearCertificate Q ((completion G T.packing).card : ℚ) := by
  refine ⟨?_⟩
  have hpaid := T.count_le_paid hmissing hrootLoss
  nlinarith

/-- The same terminal supplies both parts of the near witness: an actual exact
edge partition and the numerical bound accepted by the common assembly. -/
theorem exactPartition_and_nearCertificate_of_physicalTerminal
    {Q : ℚ} (T : PhysicalTerminal (G := G))
    (hbase : T.base ≤ Q) (hmissing : 0 ≤ T.missing)
    (hrootLoss : 0 ≤ T.rootLoss) :
    IsExactPartition G (completion G T.packing) ∧
      NearCertificate Q ((completion G T.packing).card : ℚ) :=
  ⟨T.exactPartition,
    nearCertificate_of_physicalTerminal T hbase hmissing hrootLoss⟩

/-- A literal physical packing whose completed count is already below the
target needs no non-neutral RD09 accounting: its canonical neutral terminal
gives both the exact partition and the near-regime certificate. -/
theorem exactPartition_and_nearCertificate_of_packing_bound
    {Q : ℚ} (P : Finset (Finset V)) (hP : IsK34Packing G P)
    (hbound : ((completion G P).card : ℚ) ≤ Q) :
    IsExactPartition G (completion G P) ∧
      NearCertificate Q ((completion G P).card : ℚ) := by
  let T := PhysicalTerminal.neutral P hP
  have hbase : T.base ≤ Q := by
    simpa [T] using hbound
  exact exactPartition_and_nearCertificate_of_physicalTerminal T hbase (by simp [T])
    (by simp [T])

end PaperIV.TerminalToNear
