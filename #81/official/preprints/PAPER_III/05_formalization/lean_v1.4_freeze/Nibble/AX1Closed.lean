/-
# AX1 — closed

`Nibble.AX1.BoxAllocationResidual` was the single remaining hypothesis of AX1 after the reduction
`Nibble.AX1.ax1_of_boxAllocation` (`Nibble.CoarseCellCoupled`).  It is discharged in
`Nibble.BoxPlacementNibble` by a weighted nibble on the placement hypergraph, under the small-box
restriction `s₀ ≤ θ·P` (which is necessary: `Nibble.AX1.box_allocation_infeasible` refutes the
unrestricted statement).  This file records the two consequences.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.BoxPlacementNibble
import Nibble.CoarseCellCoupled

namespace Nibble.AX1

/-- **The coupled block-cover residual** holds. -/
theorem blockCoverResidualCoupled_holds : BlockCoverResidualCoupled :=
  blockCoverResidualCoupled_of_boxAllocation boxAllocationResidual_holds

/-- **AX1 holds.** -/
theorem ax1Statement_holds : AX1Statement :=
  ax1_of_boxAllocation boxAllocationResidual_holds

end Nibble.AX1
