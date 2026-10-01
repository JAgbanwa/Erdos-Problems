import PaperIV.SplitComparatorResidual
import PaperIV.SplitComparatorFamily
import PaperIV.NearH1SplitComparator
import PaperIV.CertifiedF4Bridge
import PaperIV.NearH1CalibratedRoot
import PaperIV.NearH1PhaseI
import PaperIV.NearH1FinalAssembly
import PaperIV.LocalStabilityS01S03
import PaperIV.RD09RootSplitDistance

/-!
# Physical accounts throughout the near split window

This is the local input required by the descending H1 stability mechanism.
Every chordal graph in the fixed `eps`-neighbourhood of the split family and
above the original near graph in `F4'` admits literal RD09 accounts.  Those
same accounts both contract the family distance and are paid by the original
near-regime deficit.
-/

namespace PaperIV.NearH1WindowAccounts

open PaperIV.FarRounding PaperIV.VertexCopyGate
open PaperIV.GraphFamilyDistance PaperIV.SplitComparatorFamily
open PaperIV.RootVocab

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

/-- The window-local physical account package consumed by
`localize_original_of_windowed_accounts_descent`. -/
theorem exists_window_accounts
    (G X : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel X.Adj]
    (hX : PaperIV.IsChordal X) {w : ℚ}
    (hw : CertifiedFractionalOptimum G w)
    (hnear : ¬ ((G.edgeFinset.card : ℚ) - w <
      (Fintype.card V : ℚ) ^ 2 / 6 -
        PaperIV.NearH1Calibration.eta * (Fintype.card V : ℚ) ^ 2))
    (hGX : F4' G ≤ F4' X)
    (hn : 2 * (10 : ℚ) ^ 13 ≤ (Fintype.card V : ℚ))
    (hdist : graphFamDistNorm
      (allSplitSupports (V := V)) allSplitSupports_nonempty X
        ((Fintype.card V : ℚ) ^ 2) < PaperIV.NearH1Calibration.eps) :
    ∃ m A : ℚ, 0 ≤ A ∧
      m + A ≤ 20 * (PaperIV.NearH1Calibration.eta *
        (Fintype.card V : ℚ) ^ 2 + (Fintype.card V : ℚ) / 6 + 1 / 24) ∧
      graphFamDistNorm (allSplitSupports (V := V)) allSplitSupports_nonempty X
          ((Fintype.card V : ℚ) ^ 2) * (Fintype.card V : ℚ) ^ 2 ≤ m + A := by
  classical
  let n : ℚ := Fintype.card V
  have hnpos : 0 < n := by dsimp [n]; linarith
  have hFG : (((G.edgeFinset.card : ℚ) - w : ℚ) : ℝ) = F4' G := by
    symm
    exact PaperIV.CertifiedF4Bridge.F4'_eq_edge_sub_certified hw
  have hnearGQ : (n ^ 2 / 6 - PaperIV.NearH1Calibration.eta * n ^ 2) ≤
      (G.edgeFinset.card : ℚ) - w := le_of_not_gt hnear
  have hnearX : (((n ^ 2 / 6 - PaperIV.NearH1Calibration.eta * n ^ 2 : ℚ)) : ℝ) ≤
      F4' X := by
    have hnearGR :
        (((n ^ 2 / 6 - PaperIV.NearH1Calibration.eta * n ^ 2 : ℚ)) : ℝ) ≤ F4' G := by
      rw [← hFG]
      exact_mod_cast hnearGQ
    exact hnearGR.trans hGX
  obtain ⟨C, hC, hedit, hres⟩ :=
    PaperIV.NearH1SplitComparator.exists_calibrated_split_core X hn hdist
      (by simpa [n] using hnearX)
  let S : SimpleGraph V :=
    PaperIV.SplitUniformIncidence.splitGraph C (Finset.univ \ C)
  letI : DecidableRel S.Adj := Classical.decRel _
  have heditS : (PaperIV.EditMetric.editDist X.edgeFinset S.edgeFinset : ℚ) ≤
      PaperIV.NearH1Calibration.eps * n ^ 2 := by
    simpa [S, n, PaperIV.GraphFamilyDistance.graphEdgeSupport_eq_edgeFinset]
      using hedit
  have hS : ∀ x y, S.Adj x y ↔
      (PaperIV.SplitUniformIncidence.splitGraph C (Finset.univ \ C)).Adj x y := by
    intro x y
    rfl
  obtain ⟨R⟩ := PaperIV.NearH1CalibratedRoot.exists_regularizedRoot_of_split_comparator
    X S hX C hC hS hn
    (PaperIV.NearH1SplitComparator.deltaCal_le (Fintype.card V : ℚ)) hres rfl
    (by simpa [n] using heditS)
  have hrootPos : 0 < R.root.card :=
    lt_of_lt_of_le (by omega : 0 < 1000) R.card_ge
  letI : NeZero R.root.card := ⟨Nat.ne_of_gt hrootPos⟩
  obtain ⟨roots, z, E, hroot, hE, hhub, -, hL9⟩ :=
    PaperIV.NearH1PhaseI.exists_phaseI_of_regularizedRoot hX R
  obtain ⟨P, acc, hP, horder, hmissing, hrootLoss⟩ :=
    PaperIV.NearH1FinalAssembly.exists_physicalAccounts_of_ready_phaseI
      R roots z E hroot hE hhub hL9
  let m : ℚ := acc.missingEdges.card
  let A : ℚ := 10 * acc.rootLossEdges.card
  refine ⟨m, A, by positivity, ?_, ?_⟩
  · have hpaid := PaperIV.LocalStability.accounts_le_twenty_deficit_of_physicalAccounts acc
    have hcount := PaperIV.VertexCopyWBridge.F4'_le_completion_card_of_physical hP
    have hdef : PaperIV.sharpEnvelope n -
        ((PaperIV.PhysicalCompletion.completion X P).card : ℚ) ≤
        PaperIV.NearH1Calibration.eta * n ^ 2 + n / 6 + 1 / 24 := by
      have hcountR : F4' X ≤
          (((PaperIV.PhysicalCompletion.completion X P).card : ℚ) : ℝ) := by
        exact_mod_cast hcount
      have hnearCount :
          n ^ 2 / 6 - PaperIV.NearH1Calibration.eta * n ^ 2 ≤
            ((PaperIV.PhysicalCompletion.completion X P).card : ℚ) := by
        exact_mod_cast hnearX.trans hcountR
      unfold PaperIV.sharpEnvelope
      nlinarith
    rw [horder] at hpaid
    dsimp [m, A, n]
    linarith
  · have hmember : PaperIV.GraphFamilyDistance.graphEdgeSupport
        (PaperIV.SplitUniformIncidence.splitGraph R.root (outsideVertices R.root)) ∈
        allSplitSupports (V := V) := by
      rw [mem_allSplitSupports_iff]
      exact ⟨R.root, by rfl⟩
    have hfam := PaperIV.EditMetric.famDist_le
      (allSplitSupports (V := V)) allSplitSupports_nonempty
      (PaperIV.GraphFamilyDistance.graphEdgeSupport X) hmember
    have heditRoot := PaperIV.RD09RootSplitDistance.editDist_splitRoot_le_accounts
      X R.root R.isClique
    rw [PaperIV.GraphFamilyDistance.graphFamDistNorm,
      PaperIV.EditMetric.famDistNorm]
    have hn2ne : n ^ 2 ≠ 0 := ne_of_gt (sq_pos_of_pos hnpos)
    rw [div_mul_cancel₀ _ hn2ne]
    rw [PaperIV.GraphFamilyDistance.graphEdgeSupport_eq_edgeFinset]
    rw [PaperIV.GraphFamilyDistance.graphEdgeSupport_eq_edgeFinset,
      PaperIV.GraphFamilyDistance.graphEdgeSupport_eq_edgeFinset] at hfam
    dsimp [m, A]
    have hrootCard :
        (PaperIV.RD09SplitEditAccount.missingSpokeEdges X R.root).card =
          PaperIV.RootVocab.missingIncidences X R.root :=
      PaperIV.RD09SplitEditAccount.card_missingSpokeEdges X R.root
    have hnat : PaperIV.EditMetric.famDist
          (allSplitSupports (V := V)) allSplitSupports_nonempty X.edgeFinset ≤
        acc.missingEdges.card + 10 * acc.rootLossEdges.card := by
      rw [hmissing, hrootLoss, hrootCard]
      exact le_trans hfam (le_trans heditRoot (by omega))
    have hnatQ :
        (PaperIV.EditMetric.famDist
          (allSplitSupports (V := V)) allSplitSupports_nonempty X.edgeFinset : ℚ) ≤
        ((acc.missingEdges.card + 10 * acc.rootLossEdges.card : ℕ) : ℚ) :=
      Nat.cast_le.mpr hnat
    push_cast at hnatQ
    exact hnatQ

end PaperIV.NearH1WindowAccounts
