import PaperIV.RC01FarAssembly
import PaperIV.FarRoundingToPhysical
import PaperIV.RD09PhysicalLedger
import PaperIV.SplitBaselineTarget

/-!
# What actually closes `NearRegimeAt`: a packing in the original graph

`RC01FarAssembly.NearRegimeAt η` asks, for every sufficiently large chordal
graph without far slack, for a clique partition of order at most four and size
at most `targetSize n`.  This module records the **only** legitimate way to
reach it along the first-entry route: produce a literal `K3`/`K4` packing *in
the original graph* whose physical completion has at most `targetSize n`
pieces.

Two structural points are respected.

* **Quantifier order.**  Every constant (`η`, the threshold `N`) is fixed
  before `n`: the interface below is `η → ∃ N, ∀ n ≥ N, …`, never
  `∀ n, ∃ N`.
* **No inverse transport.**  The hypothesis speaks about a packing of `G`
  itself, not of a terminal graph reached by copies.  The first-entry machinery
  (`SymmetrizationInvariantBarrier`, `LocalStabilityS01S03`) locates `G` in the metric
  neighbourhood of the critical split family; it does not transport a
  partition backwards, and by itself it does not discharge the hypothesis
  below.

Nothing in this file claims `NearRegimeAt` — the packing supply
`NearPackingSupplyAt` is an explicit input.
-/

namespace PaperIV.NearRegimePacking

open PaperIV.FarRounding
open PaperIV.Model PaperIV.PhysicalCompletion
open PaperIV.RC01FarAssembly

/-! ## From a physical packing to a clique partition of the same size -/

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A literal `K3`/`K4` packing of `G` yields a clique partition of order at
most four whose size is exactly the number of completed pieces. -/
theorem exists_cliquePartition_card_completion {P : Finset (Finset V)}
    (hP : IsK34Packing G P) :
    ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size = (completion G P).card := by
  obtain ⟨Q, hQ4, hQsize⟩ :=
    exists_cliquePartition_of_packing (PaperIV.FarRoundingToPhysical.ofPhysicalPacking hP)
  refine ⟨Q, hQ4, ?_⟩
  have hgain : (PaperIV.FarRoundingToPhysical.ofPhysicalPacking hP).gain = totalGain P :=
    PaperIV.FarRoundingToPhysical.physical_gain_eq hP
  have hcompl : (completion G P).card + totalGain P = (graphEdges G).card :=
    card_completion_add_totalGain hP
  have hedges : (graphEdges G).card = G.edgeFinset.card := rfl
  omega

/-- **The packing bridge.**  A literal `K3`/`K4` packing of `G` whose physical
completion has at most `t` pieces gives a clique partition of order at most
four and size at most `t`. -/
theorem exists_cliquePartition_le_of_packing {P : Finset (Finset V)}
    (hP : IsK34Packing G P) {t : ℕ} (hcount : (completion G P).card ≤ t) :
    ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size ≤ t := by
  obtain ⟨Q, hQ4, hQsize⟩ := exists_cliquePartition_card_completion hP
  exact ⟨Q, hQ4, by omega⟩

/-! ## The near-regime packing supply -/

/-- **The near-regime packing supply.**  For a fixed separation parameter `η`,
a threshold `N` chosen *before* `n`, such that every chordal graph of order
`n ≥ N` without far slack carries a literal `K3`/`K4` packing whose completion
has at most `targetSize n` pieces.

This is the honest formal content of "the local physical constructor applied
once to the original graph". -/
def NearPackingSupplyAt (η : ℚ) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    IsChordal G → ∀ w : ℚ, CertifiedFractionalOptimum G w →
      ¬ ((G.edgeFinset.card : ℚ) - w < (n : ℚ) ^ 2 / 6 - η * (n : ℚ) ^ 2) →
        ∃ P : Finset (Finset (Fin n)), IsK34Packing G P ∧
          (completion G P).card ≤ targetSize n

/-- **The packing supply closes the near regime.**  All constants are fixed
before `n`. -/
theorem nearRegimeAt_of_nearPackingSupplyAt {η : ℚ} (h : NearPackingSupplyAt η) :
    NearRegimeAt η := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N, ?_⟩
  intro n hn G _ hG w hw hslack
  obtain ⟨P, hP, hcount⟩ := hN n hn G hG w hw hslack
  exact exists_cliquePartition_le_of_packing hP hcount

/-- **Full assembly, conditional on the packing supply only.**  RC01 already
discharges the far branch unconditionally, so the whole chordal target follows
from an actual packing in the original graph. -/
theorem chordalTargetAt_of_nearPackingSupplyAt (η : ℚ) (hη : 0 < η)
    (h : NearPackingSupplyAt η) : ChordalTargetAt :=
  chordalTargetAt_of_nearRegimeAt η hη (nearRegimeAt_of_nearPackingSupplyAt h)

/-! ## The same supply, phrased through the paid RD09 ledger -/

/-- A packing supply expressed through the physical RD09 accounts: the
completion count is bounded by the split baseline minus the RD09 discount, and
that bound is below the target.  This is the form the two-phase construction
would deliver. -/
theorem exists_cliquePartition_of_physicalAccounts
    {P : Finset (Finset V)} (hP : IsK34Packing G P)
    (acc : PaperIV.RD09PhysicalLedger.PhysicalAccounts G P) {t : ℕ}
    (hbound : splitBaseline acc.order acc.split
        - (acc.missingEdges.card : ℚ) / 20 - (acc.rootLossEdges.card : ℚ) / 2 ≤ (t : ℚ)) :
    ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size ≤ t := by
  have hpaid := acc.count_le_paid
  have hcount : ((completion G P).card : ℚ) ≤ (t : ℚ) := le_trans hpaid hbound
  exact exists_cliquePartition_le_of_packing hP (by exact_mod_cast hcount)

/-- **The target-sized physical-accounts bridge.**  Once the `order` field of
the RD09 accounts is identified with the actual order of the graph, no
separate numerical `hbound` is needed: the integral split baseline is always
at most `targetSize`, and the two RD09 discounts are nonnegative.

Keeping `horder` explicit is essential.  `PhysicalAccounts` is a reusable
ledger whose rational `order` field is not definitionally tied to the vertex
type. -/
theorem exists_cliquePartition_target_of_physicalAccounts
    {P : Finset (Finset V)} (hP : IsK34Packing G P)
    (acc : PaperIV.RD09PhysicalLedger.PhysicalAccounts G P)
    (horder : acc.order = (Fintype.card V : ℚ)) :
    ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size ≤ targetSize (Fintype.card V) := by
  have hbase : (((acc.baseCount : ℤ) : ℚ)) =
      splitBaseline (Fintype.card V : ℚ) acc.split := by
    norm_num
    rw [acc.base_eq, horder]
  have hpaid := acc.count_le_paid
  have hpaidBase : ((completion G P).card : ℚ) ≤ (acc.baseCount : ℚ)
      - (acc.missingEdges.card : ℚ) / 20 - (acc.rootLossEdges.card : ℚ) / 2 := by
    rw [acc.base_eq]
    exact hpaid
  have hcountZ : ((completion G P).card : ℤ) ≤
      (targetSize (Fintype.card V) : ℤ) := by
    apply PaperIV.SplitBaselineTarget.count_le_targetSize_of_paid
        (p := acc.split)
        (m := (acc.missingEdges.card : ℚ))
        (A := (acc.rootLossEdges.card : ℚ))
        (S := (acc.baseCount : ℤ))
        (count := ((completion G P).card : ℤ))
    · exact hbase
    · positivity
    · positivity
    · simpa using hpaidBase
  exact exists_cliquePartition_le_of_packing hP (by exact_mod_cast hcountZ)

end PaperIV.NearRegimePacking
