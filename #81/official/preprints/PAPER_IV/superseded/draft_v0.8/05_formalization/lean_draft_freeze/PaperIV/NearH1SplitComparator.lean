import PaperIV.SplitComparatorResidual
import PaperIV.SplitComparatorFamily
import PaperIV.NearH1Calibration

/-!
# The shared calibrated split-comparator adapter

Both near-regime entry points — the window-local accounts of
`PaperIV.NearH1WindowAccounts` and the global assembly of
`PaperIV.NearH1GlobalAssembly` — need the same passage from

* a graph that is `eps`-close to the family of complete split graphs, and
* a near-optimal mixed defect,

to a literal split core `C` together with the two numeric facts consumed by the
calibrated root constructor: a quadratic edit budget and the residual square
bound.  That passage is isolated here once, instead of being repeated in both
callers.
-/

namespace PaperIV.NearH1SplitComparator

open PaperIV.FarRounding PaperIV.VertexCopyGate
open PaperIV.GraphFamilyDistance PaperIV.SplitComparatorFamily

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The fixed calibrated terminal deficit used by the near route. -/
def deltaCal (n : ℚ) : ℚ :=
  (PaperIV.NearH1Calibration.eta + 6 * PaperIV.NearH1Calibration.eps) * n ^ 2 +
    n / 6 + 1 / 24

theorem deltaCal_le (n : ℚ) :
    deltaCal n ≤ (PaperIV.NearH1Calibration.eta +
      6 * PaperIV.NearH1Calibration.eps) * n ^ 2 + n / 6 + 1 / 24 := le_rfl

theorem deltaCal_le_div_forty {n : ℚ} (hn : 2 * (10 : ℚ) ^ 13 ≤ n) :
    deltaCal n ≤ n ^ 2 / 40 := by
  have hsmall := PaperIV.NearH1Calibration.delta_small hn (deltaCal_le n)
  dsimp [PaperIV.NearH1Calibration.eps] at hsmall
  nlinarith [sq_nonneg n]

/-- **Calibrated split comparator.**  A graph in the `eps`-neighbourhood of the
split family whose mixed defect is near the sharp envelope has a literal split
core with a quadratic edit budget and a calibrated residual square. -/
theorem exists_calibrated_split_core (Y : SimpleGraph V) [DecidableRel Y.Adj]
    (hn : 2 * (10 : ℚ) ^ 13 ≤ (Fintype.card V : ℚ))
    (hdist : graphFamDistNorm (allSplitSupports (V := V)) allSplitSupports_nonempty
      Y ((Fintype.card V : ℚ) ^ 2) < PaperIV.NearH1Calibration.eps)
    (hnear : (((Fintype.card V : ℚ) ^ 2 / 6 -
        PaperIV.NearH1Calibration.eta * (Fintype.card V : ℚ) ^ 2 : ℚ) : ℝ) ≤
      F4' Y) :
    ∃ C : Finset V, C.Nonempty ∧
      (PaperIV.EditMetric.editDist Y.edgeFinset
          (graphEdgeSupport
            (PaperIV.SplitUniformIncidence.splitGraph C (Finset.univ \ C))) : ℚ) ≤
        PaperIV.NearH1Calibration.eps * (Fintype.card V : ℚ) ^ 2 ∧
      (6 * (C.card : ℚ) - 2 * (Fintype.card V : ℚ) - 1) ^ 2 ≤
        24 * deltaCal (Fintype.card V : ℚ) := by
  classical
  have hnpos : (0 : ℚ) < (Fintype.card V : ℚ) := by nlinarith
  have hn100 : 100 ≤ Fintype.card V := by
    have h : (100 : ℚ) ≤ (Fintype.card V : ℚ) := by linarith
    exact_mod_cast h
  obtain ⟨C, hYC⟩ := exists_split_editDist_lt Y (sq_pos_of_pos hnpos) hdist
  let S : SimpleGraph V :=
    PaperIV.SplitUniformIncidence.splitGraph C (Finset.univ \ C)
  letI : DecidableRel S.Adj := Classical.decRel _
  have hYC' : (PaperIV.EditMetric.editDist Y.edgeFinset S.edgeFinset : ℚ) <
      PaperIV.NearH1Calibration.eps * (Fintype.card V : ℚ) ^ 2 := by
    simpa [S, graphEdgeSupport_eq_edgeFinset] using hYC
  have hnearS : ((PaperIV.sharpEnvelope (Fintype.card V : ℚ) -
      deltaCal (Fintype.card V : ℚ) : ℚ) : ℝ) ≤ F4' S := by
    have hFrob := PaperIV.F4EditRobustness.abs_sub_F4'_le_six_editDist Y S
    rw [abs_sub_le_iff] at hFrob
    have heditR : (PaperIV.EditMetric.editDist Y.edgeFinset S.edgeFinset : ℝ) <
        ((PaperIV.NearH1Calibration.eps * (Fintype.card V : ℚ) ^ 2 : ℚ) : ℝ) := by
      exact_mod_cast hYC'
    unfold PaperIV.sharpEnvelope deltaCal
    push_cast at hFrob hnear heditR ⊢
    nlinarith
  have hdj : Disjoint C (Finset.univ \ C) := by
    rw [Finset.disjoint_left]
    intro x hx hxc
    exact (Finset.mem_sdiff.mp hxc).2 hx
  have hcover : C.card + (Finset.univ \ C).card = Fintype.card V := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ C)]
    exact Nat.add_sub_of_le (Finset.card_le_univ C)
  have hres := PaperIV.SplitComparatorResidual.residual_sq_le_of_near_split_universal
    hdj hcover hn100 (deltaCal_le_div_forty hn) hnearS
  refine ⟨C, ?_, ?_, hres⟩
  · rw [Finset.nonempty_iff_ne_empty]
    intro hzero
    have hcard : C.card = 0 := by simp [hzero]
    rw [hcard] at hres
    dsimp [deltaCal, PaperIV.NearH1Calibration.eta,
      PaperIV.NearH1Calibration.eps] at hres
    nlinarith
  · simpa [S, graphEdgeSupport_eq_edgeFinset] using hYC'.le

end PaperIV.NearH1SplitComparator
