import PaperIV.NearH1CalibratedRoot
import PaperIV.NearH1PhaseI
import PaperIV.NearH1FinalAssembly
import PaperIV.NearH1SplitComparator

/-!
# The literal structural output of the near H1/RD09 route

A calibrated split comparator does not only produce a clique partition of the
target size: the construction passes through concrete extremal data, namely

* a literal split **core** with a quadratic edit budget and the calibrated
  residual square (the comparator of `PaperIV.NearH1SplitComparator`),
* a **regularized root** (`PaperIV.NearH1RootRegularization.RegularizedRoot`),
  carrying the calibrated reference clique, its retained part, and every
  denominator-cleared scalar ratio of the RD09 interface,
* the **physical H1/RD09 terminal accounts** of the original graph:  a literal
  `K3`/`K4` packing with its RD09 ledger, whose missing-edge and root-loss
  families are the literal families of the regularized root.

This module bundles those witnesses in `NearStructureWitness` and proves that a
calibrated split comparator produces one.  Both the numerical near route
(`PaperIV.NearH1TargetAssembly`) and the structural hybrid route
(`PaperIV.HybridDichotomy`) are obtained from this single constructor, so the
composition calibrated root → phase I → physical accounts occurs once.
-/

namespace PaperIV.NearH1StructureWitness

open PaperIV.RootVocab
open PaperIV.GraphFamilyDistance
open PaperIV.PhysicalCompletion

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

/-- Visible extremal witnesses of the near regime. -/
structure NearStructureWitness (G : SimpleGraph V) [DecidableRel G.Adj] where
  /-- the literal split core of the comparator -/
  core : Finset V
  core_nonempty : core.Nonempty
  /-- quadratic edit budget between `G` and the complete split graph on `core` -/
  core_edit_le : (PaperIV.EditMetric.editDist G.edgeFinset
      (graphEdgeSupport
        (PaperIV.SplitUniformIncidence.splitGraph core (Finset.univ \ core))) : ℚ) ≤
    PaperIV.NearH1Calibration.eps * (Fintype.card V : ℚ) ^ 2
  /-- calibrated residual square: `core` has the critical size up to `√δ` -/
  core_residual_sq_le : (6 * (core.card : ℚ) - 2 * (Fintype.card V : ℚ) - 1) ^ 2 ≤
    24 * PaperIV.NearH1SplitComparator.deltaCal (Fintype.card V : ℚ)
  /-- the regularized root produced from the calibrated reference clique -/
  regularized : PaperIV.NearH1RootRegularization.RegularizedRoot G
  /-- the literal `K3`/`K4` packing of the *original* graph -/
  packing : Finset (Finset V)
  isPacking : IsK34Packing G packing
  /-- its physical RD09 ledger -/
  accounts : PaperIV.RD09PhysicalLedger.PhysicalAccounts G packing
  accounts_split : accounts.split = regularized.root.card
  accounts_order : accounts.order = (Fintype.card V : ℚ)
  accounts_missing : accounts.missingEdges = outsideEdges G regularized.root
  accounts_rootLoss : accounts.rootLossEdges =
    PaperIV.RD09SplitEditAccount.missingSpokeEdges G regularized.root
  /-- The same literal accounts retain the stronger L10Q coefficients. -/
  accounts_count_le_improved :
    ((PaperIV.PhysicalCompletion.completion G packing).card : ℚ) ≤
      splitBaseline accounts.order accounts.split -
        (117 : ℚ) / 1825 * (accounts.missingEdges.card : ℚ) -
        (12687 : ℚ) / 20000 * (accounts.rootLossEdges.card : ℚ)

/-- **The structural near constructor.**  A calibrated split comparator yields
the full extremal package: core, regularized root and physical RD09 accounts of
the original graph. -/
theorem exists_nearStructureWitness_of_split_comparator
    (G S : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel S.Adj]
    (hchordal : PaperIV.IsChordal G) (C : Finset V) (hC : C.Nonempty)
    (hS : ∀ x y, S.Adj x y ↔
      (PaperIV.SplitUniformIncidence.splitGraph C (Finset.univ \ C)).Adj x y)
    (hn : 4 * (10 : ℚ) ^ 12 ≤ (Fintype.card V : ℚ))
    (hres : (6 * (C.card : ℚ) - 2 * (Fintype.card V : ℚ) - 1) ^ 2 ≤
      24 * ((PaperIV.NearH1Calibration.eta +
        6 * PaperIV.NearH1Calibration.eps) * (Fintype.card V : ℚ) ^ 2 +
        (Fintype.card V : ℚ) / 6 + 1 / 24))
    (hedit : (PaperIV.EditMetric.editDist G.edgeFinset S.edgeFinset : ℚ) ≤
      PaperIV.NearH1Calibration.eps * (Fintype.card V : ℚ) ^ 2) :
    Nonempty (NearStructureWitness G) := by
  classical
  obtain ⟨R⟩ :=
    PaperIV.NearH1CalibratedRoot.exists_regularizedRoot_of_split_comparator
      G S hchordal C hC hS hn hres hedit
  have hrootPos : 0 < R.root.card :=
    lt_of_lt_of_le (by omega : 0 < 1000) R.card_ge
  letI : NeZero R.root.card := ⟨Nat.ne_of_gt hrootPos⟩
  obtain ⟨roots, z, E, hroot, hE, hhub, -, hL9⟩ :=
    PaperIV.NearH1PhaseI.exists_phaseI_of_regularizedRoot hchordal R
  obtain ⟨P, acc, hP, hsplit, horder, hmissing, hrootLoss, hstrong⟩ :=
    PaperIV.NearH1FinalAssembly.exists_physicalAccounts_of_ready_phaseI
      R roots z E hroot hE hhub hL9
  have hSedge : S.edgeFinset =
      graphEdgeSupport
        (PaperIV.SplitUniformIncidence.splitGraph C (Finset.univ \ C)) := by
    ext e
    induction e using Sym2.ind with
    | _ x y =>
      simp only [SimpleGraph.mem_edgeFinset, graphEdgeSupport, Set.mem_toFinset,
        SimpleGraph.mem_edgeSet]
      exact hS x y
  exact ⟨{ core := C
           core_nonempty := hC
           core_edit_le := by rw [← hSedge]; exact hedit
           core_residual_sq_le := by
             refine hres.trans ?_
             dsimp [PaperIV.NearH1SplitComparator.deltaCal]
             linarith
           regularized := R
           packing := P
           isPacking := hP
           accounts := acc
           accounts_split := hsplit
           accounts_order := by exact_mod_cast horder
           accounts_missing := hmissing
           accounts_rootLoss := hrootLoss
           accounts_count_le_improved := hstrong }⟩

end PaperIV.NearH1StructureWitness
