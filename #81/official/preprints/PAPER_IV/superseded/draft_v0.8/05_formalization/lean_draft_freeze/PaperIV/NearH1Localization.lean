import PaperIV.NearH1WindowAccounts
import PaperIV.GatedTerminalSplit
import PaperIV.NearH1SplitComparator

set_option maxHeartbeats 1000000

/-!
# Descent localization of a near-regime chordal graph

This module isolates the *structural* half of the near branch: a chordal graph
of large order whose certified mixed defect has no quadratic far slack is
located, by the symmetrization descent of
`PaperIV.LocalStability.localize_original_of_windowed_accounts_descent`, inside
the `eps`-neighbourhood of the complete split family, and therefore carries a
literal split core with a quadratic edit budget and the calibrated residual
square.

Both the original near-regime entry point
(`PaperIV.NearH1GlobalAssembly.nearRegimeAt`) and the hybrid structural route
(`PaperIV.HybridNearStructure`) consume exactly this statement, so the descent
argument occurs only once in the project.
-/

namespace PaperIV.NearH1Localization

open PaperIV.FarRounding PaperIV.VertexCopyGate
open PaperIV.GraphFamilyDistance PaperIV.SplitComparatorFamily

/-- **Near localization.**  A large chordal graph whose certified mixed defect
is not far-separated admits a literal split core `C` together with the two
numeric facts consumed by the calibrated root constructor. -/
theorem exists_localized_split_core {n : ℕ} (hn : 2 * 10 ^ 13 ≤ n)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : PaperIV.IsChordal G) {w : ℚ} (hw : CertifiedFractionalOptimum G w)
    (hnear : ¬ ((G.edgeFinset.card : ℚ) - w <
      (n : ℚ) ^ 2 / 6 - PaperIV.NearH1Calibration.eta * (n : ℚ) ^ 2)) :
    ∃ C : Finset (Fin n), C.Nonempty ∧
      (PaperIV.EditMetric.editDist G.edgeFinset
          (graphEdgeSupport
            (PaperIV.SplitUniformIncidence.splitGraph C (Finset.univ \ C))) : ℚ) ≤
        PaperIV.NearH1Calibration.eps * (n : ℚ) ^ 2 ∧
      (6 * (C.card : ℚ) - 2 * (n : ℚ) - 1) ^ 2 ≤
        24 * PaperIV.NearH1SplitComparator.deltaCal (n : ℚ) := by
  classical
  let nq : ℚ := n
  let D : ℚ := PaperIV.NearH1Calibration.eta * nq ^ 2 + nq / 6 + 1 / 24
  have hnQ : 2 * (10 : ℚ) ^ 13 ≤ nq := by
    dsimp [nq]
    exact_mod_cast hn
  have hnpos : 0 < nq := by dsimp [nq]; positivity
  have hn2 : 2 ≤ n := by omega
  have houter : PaperIV.NearH1Calibration.eps / 2 + 1 / nq ≤
      PaperIV.NearH1Calibration.eps := by
    have hinv : 1 / nq ≤ PaperIV.NearH1Calibration.eps / 2 := by
      rw [div_le_iff₀ hnpos]
      dsimp [PaperIV.NearH1Calibration.eps]
      nlinarith
    linarith
  have hcontract : PaperIV.NearH1Calibration.eps / 4 ≤
      PaperIV.NearH1Calibration.eps / 2 := by
    dsimp [PaperIV.NearH1Calibration.eps]
    norm_num
  have hDcontract : 20 * D / nq ^ 2 < PaperIV.NearH1Calibration.eps / 4 := by
    rw [div_lt_iff₀ (sq_pos_of_pos hnpos)]
    dsimp [D, PaperIV.NearH1Calibration.eta, PaperIV.NearH1Calibration.eps]
    nlinarith [sq_nonneg (nq - 2 * (10 : ℚ) ^ 13)]
  obtain ⟨H, Cterm, hpath, hHchord, hHsplit, hF4H⟩ :=
    PaperIV.GatedTerminalSplit.exists_split_terminal_symmetrizationPath G hG
  have hterminal : graphFamDistNorm
      (allSplitSupports (V := Fin n)) allSplitSupports_nonempty H (nq ^ 2) <
        PaperIV.NearH1Calibration.eps / 2 := by
    have hhost : PaperIV.TerminalSplitAdapter.hostFinset Cterm =
        Finset.univ \ PaperIV.TerminalSplitAdapter.coreFinset Cterm := by
      ext x
      simp [PaperIV.TerminalSplitAdapter.mem_hostFinset,
        PaperIV.TerminalSplitAdapter.mem_coreFinset]
    rw [hHsplit, hhost]
    have hmem : graphEdgeSupport
          (PaperIV.SplitUniformIncidence.splitGraph
            (PaperIV.TerminalSplitAdapter.coreFinset Cterm)
            (Finset.univ \ PaperIV.TerminalSplitAdapter.coreFinset Cterm)) ∈
        allSplitSupports (V := Fin n) := by
      rw [mem_allSplitSupports_iff]
      exact ⟨PaperIV.TerminalSplitAdapter.coreFinset Cterm, rfl⟩
    rw [graphFamDistNorm, PaperIV.EditMetric.famDistNorm,
      (PaperIV.EditMetric.famDist_eq_zero_iff
        (allSplitSupports (V := Fin n)) allSplitSupports_nonempty).2 hmem]
    dsimp [PaperIV.NearH1Calibration.eps]
    norm_num
  have hlocal : ∀ X : SimpleGraph (Fin n), PaperIV.IsChordal X →
      F4' G ≤ F4' X → F4' X ≤ F4' H →
      graphFamDistNorm (allSplitSupports (V := Fin n)) allSplitSupports_nonempty X
          (nq ^ 2) < PaperIV.NearH1Calibration.eps →
      ∃ m A : ℚ, 0 ≤ A ∧ m + A ≤ 20 * D ∧
        graphFamDistNorm (allSplitSupports (V := Fin n)) allSplitSupports_nonempty X
            (nq ^ 2) * nq ^ 2 ≤ m + A := by
    intro X hX hGX _ hdist
    have hout := PaperIV.NearH1WindowAccounts.exists_window_accounts
      G X hX hw (by simpa using hnear) hGX (by simpa [nq] using hnQ)
        (by simpa [nq] using hdist)
    simpa [nq, D] using hout
  have hDcontract' :
      20 * (PaperIV.NearH1Calibration.eta * (Fintype.card (Fin n) : ℚ) ^ 2 +
        (Fintype.card (Fin n) : ℚ) / 6 + 1 / 24) /
          (Fintype.card (Fin n) : ℚ) ^ 2 <
        PaperIV.NearH1Calibration.eps / 4 := by
    dsimp [D, nq] at hDcontract
    simpa using hDcontract
  have hGdist := PaperIV.LocalStability.localize_original_of_windowed_accounts_descent
    (allSplitSupports (V := Fin n)) allSplitSupports_nonempty (by simpa using hn2)
    (by simpa [nq] using houter) hcontract hG
    (by simpa [nq, D] using hlocal) hDcontract' hpath
    (by simpa [nq] using hterminal)
  have hGdist' : graphFamDistNorm
      (allSplitSupports (V := Fin n)) allSplitSupports_nonempty G (nq ^ 2) <
        PaperIV.NearH1Calibration.eps / 2 := by
    simpa [nq] using hGdist
  have hnearQ : nq ^ 2 / 6 - PaperIV.NearH1Calibration.eta * nq ^ 2 ≤
      (G.edgeFinset.card : ℚ) - w := le_of_not_gt hnear
  have hnearG :
      (((nq ^ 2 / 6 - PaperIV.NearH1Calibration.eta * nq ^ 2 : ℚ)) : ℝ) ≤ F4' G := by
    rw [PaperIV.CertifiedF4Bridge.F4'_eq_edge_sub_certified hw]
    exact_mod_cast hnearQ
  obtain ⟨C, hC, hedit, hres⟩ :=
    PaperIV.NearH1SplitComparator.exists_calibrated_split_core G
      (by simpa [nq] using hnQ)
      (by
        refine lt_of_lt_of_le (by simpa [nq] using hGdist') ?_
        dsimp [PaperIV.NearH1Calibration.eps]
        norm_num)
      (by simpa [nq] using hnearG)
  exact ⟨C, hC, by simpa [nq] using hedit, by simpa [nq] using hres⟩

end PaperIV.NearH1Localization
