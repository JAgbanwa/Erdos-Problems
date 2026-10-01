import PaperIV.NearH1SplitComparator
import PaperIV.NearH1StructureWitness
import PaperIV.NearRootWindow
import PaperIV.NearRegimePackingInterface
import PaperIV.CertifiedF4Bridge

set_option maxHeartbeats 1000000

/-!
# The local near constructor stated in the paper

The manuscript's Theorem 5.0 was previously presented as the conjunction of
the calibrated split comparator, root regularization, the two physical phases,
and the RD09 ledger.  This module exports that conjunction as one public Lean
theorem.  It does not make a second existential choice: the root, packing,
physical accounts, and clique partition all come from the single
`NearStructureWitness` constructed below.
-/

namespace PaperIV.NearH1LocalConstructor

open PaperIV.FarRounding
open PaperIV.VertexCopyGate
open PaperIV.GraphFamilyDistance
open PaperIV.SplitComparatorFamily
open PaperIV.RootVocab

/-- **Theorem 5.0, sharp form (local near constructor with the critical
window).**  Same hypotheses and same clique partition as
`exists_near_partition_paid_by_root`, but the root is located at the centre:
`|3|R| − n| ≤ n/50`, i.e. `|R| = n/3` with relative error below 1 %.  The
previously exported window `n/4 ≤ |R| ≤ n/2` is the corollary below.

The sharper window costs nothing: it is `PaperIV.NearRootWindow`'s arithmetic
reading of three ratios that the regularized root already carries. -/
theorem exists_near_partition_paid_by_root_sharp {n : ℕ}
    (hn : 4 * 10 ^ 12 ≤ n)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : PaperIV.IsChordal G) {w : ℚ}
    (hw : CertifiedFractionalOptimum G w)
    (hdist : graphFamDistNorm
      (allSplitSupports (V := Fin n)) allSplitSupports_nonempty G
        ((n : ℚ) ^ 2) < PaperIV.NearH1Calibration.eps)
    (hnear : (n : ℚ) ^ 2 / 6 -
        PaperIV.NearH1Calibration.eta * (n : ℚ) ^ 2 ≤
      (G.edgeFinset.card : ℚ) - w) :
    ∃ (R : Finset (Fin n)) (Q : CliquePartition G),
      G.IsClique (R : Set (Fin n)) ∧
      |3 * (R.card : ℚ) - (n : ℚ)| ≤ (n : ℚ) / 50 ∧
      Q.OrderAtMost 4 ∧
      (Q.size : ℚ) ≤
        splitBaseline (n : ℚ) (R.card : ℚ) -
          ((outsideEdges G R).card : ℚ) / 20 -
          (missingIncidences G R : ℚ) / 2 := by
  classical
  have hnQ : 4 * (10 : ℚ) ^ 12 ≤ (n : ℚ) := by
    exact_mod_cast hn
  have hnCardQ : 4 * (10 : ℚ) ^ 12 ≤ (Fintype.card (Fin n) : ℚ) := by
    simpa only [Fintype.card_fin] using hnQ
  have hdistCard : graphFamDistNorm
      (allSplitSupports (V := Fin n)) allSplitSupports_nonempty G
        ((Fintype.card (Fin n) : ℚ) ^ 2) < PaperIV.NearH1Calibration.eps := by
    simpa only [Fintype.card_fin] using hdist
  have hnearR :
      ((((n : ℚ) ^ 2 / 6 - PaperIV.NearH1Calibration.eta *
          (n : ℚ) ^ 2 : ℚ)) : ℝ) ≤ F4' G := by
    rw [PaperIV.CertifiedF4Bridge.F4'_eq_edge_sub_certified hw]
    exact_mod_cast hnear
  have hnearCard :
      ((((Fintype.card (Fin n) : ℚ) ^ 2 / 6 -
          PaperIV.NearH1Calibration.eta *
            (Fintype.card (Fin n) : ℚ) ^ 2 : ℚ)) : ℝ) ≤ F4' G := by
    simpa only [Fintype.card_fin] using hnearR
  obtain ⟨C, hC, hedit, hres⟩ :=
    PaperIV.NearH1SplitComparator.exists_calibrated_split_core G
      hnCardQ hdistCard hnearCard
  let S : SimpleGraph (Fin n) :=
    PaperIV.SplitUniformIncidence.splitGraph C (Finset.univ \ C)
  letI : DecidableRel S.Adj := Classical.decRel _
  have hS : ∀ x y, S.Adj x y ↔
      (PaperIV.SplitUniformIncidence.splitGraph C (Finset.univ \ C)).Adj x y := by
    intro x y
    rfl
  have heditS :
      (PaperIV.EditMetric.editDist G.edgeFinset S.edgeFinset : ℚ) ≤
        PaperIV.NearH1Calibration.eps * (n : ℚ) ^ 2 := by
    simpa [S, graphEdgeSupport_eq_edgeFinset] using hedit
  have heditCard :
      (PaperIV.EditMetric.editDist G.edgeFinset S.edgeFinset : ℚ) ≤
        PaperIV.NearH1Calibration.eps *
          (Fintype.card (Fin n) : ℚ) ^ 2 := by
    simpa only [Fintype.card_fin] using heditS
  obtain ⟨W⟩ :=
    PaperIV.NearH1StructureWitness.exists_nearStructureWitness_of_split_comparator
      G S hG C hC hS hnCardQ
        (by simpa [PaperIV.NearH1SplitComparator.deltaCal] using hres) heditCard
  obtain ⟨Q, hQ4, hQsize⟩ :=
    PaperIV.NearRegimePacking.exists_cliquePartition_card_completion W.isPacking
  let R := W.regularized.root
  have hwindow : |3 * (R.card : ℚ) - (n : ℚ)| ≤ (n : ℚ) / 50 := by
    simpa only [R, Fintype.card_fin] using
      PaperIV.NearRootWindow.regularizedRoot_card_near_third W.regularized
  have hpaid := W.accounts.count_le_paid
  rw [W.accounts_order, W.accounts_split, W.accounts_missing,
    W.accounts_rootLoss,
    PaperIV.RD09SplitEditAccount.card_missingSpokeEdges] at hpaid
  refine ⟨R, Q, W.regularized.isClique, hwindow, hQ4, ?_⟩
  rw [hQsize]
  simpa [R] using hpaid

/-- **Theorem 5.0 (local near constructor).**  A sufficiently large chordal
graph that is both close to the complete-split family and near the mixed
fractional envelope has a literal clique root in the critical size window and
a clique partition whose cost is paid by the two physical root defects.

The two defects are the number of graph edges outside the root and the number
of missing root--exterior incidences.  The baseline is fixed at
`splitBaseline n |R|` before the partition is counted.

The statement is unchanged; it is now derived from the sharp form above. -/
theorem exists_near_partition_paid_by_root {n : ℕ}
    (hn : 4 * 10 ^ 12 ≤ n)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : PaperIV.IsChordal G) {w : ℚ}
    (hw : CertifiedFractionalOptimum G w)
    (hdist : graphFamDistNorm
      (allSplitSupports (V := Fin n)) allSplitSupports_nonempty G
        ((n : ℚ) ^ 2) < PaperIV.NearH1Calibration.eps)
    (hnear : (n : ℚ) ^ 2 / 6 -
        PaperIV.NearH1Calibration.eta * (n : ℚ) ^ 2 ≤
      (G.edgeFinset.card : ℚ) - w) :
    ∃ (R : Finset (Fin n)) (Q : CliquePartition G),
      G.IsClique (R : Set (Fin n)) ∧
      (n : ℚ) / 4 ≤ (R.card : ℚ) ∧
      (R.card : ℚ) ≤ (n : ℚ) / 2 ∧
      Q.OrderAtMost 4 ∧
      (Q.size : ℚ) ≤
        splitBaseline (n : ℚ) (R.card : ℚ) -
          ((outsideEdges G R).card : ℚ) / 20 -
          (missingIncidences G R : ℚ) / 2 := by
  obtain ⟨R, Q, hclique, hwindow, hQ4, hsize⟩ :=
    exists_near_partition_paid_by_root_sharp hn G hG hw hdist hnear
  rw [abs_le] at hwindow
  have hn0 : (0 : ℚ) ≤ (n : ℚ) := by positivity
  exact ⟨R, Q, hclique, by linarith [hwindow.1], by linarith [hwindow.2], hQ4, hsize⟩

end PaperIV.NearH1LocalConstructor

