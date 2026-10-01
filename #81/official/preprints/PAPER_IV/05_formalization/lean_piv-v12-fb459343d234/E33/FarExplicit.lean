import E18.Far
import E19.Main
import PaperIV.IntegralStability

/-!
# E33 — explicit far regime and explicit chordal linear stability

* `farSlack_explicit η`: the far regime **with quadratic slack** for every graph and every
  `η > 0`, above the explicit threshold `E18.NfarE η` (formula (C.1) of Paper IV at
  accuracy `η/2`).  This is the explicit form of
  `PaperIV.FarSlackQuantitative.farRegime_cliquePartition_slack` (whose threshold is only
  existential); chordality is not needed.
* `stabThreshold := max (max (4·10¹²) (NfarE η₀)) 5`, `η₀ = 10⁻¹⁶`, and
  `stabThreshold_le_tower : stabThreshold ≤ tower2 (hIter + 7)`.
* `chordal_linear_stability_explicit`: the statement of
  `PaperIV.IntegralStability.chordal_linear_stability_sixteen` with the explicit
  threshold `stabThreshold` in place of `∃ N`.
-/

namespace E33

open PaperIV.FarRounding

/-- **Far regime with slack, explicit threshold `NfarE η`, every graph.** -/
theorem farSlack_explicit (η : ℚ) (hη : 0 < η) :
    ∀ n : ℕ, E18.NfarE η ≤ n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      ∀ w : ℚ, CertifiedFractionalOptimum G w →
        (G.edgeFinset.card : ℚ) - w < (n : ℚ) ^ 2 / 6 - η * (n : ℚ) ^ 2 →
          ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧
            (Q.size : ℚ) < (n : ℚ) ^ 2 / 6 - η * (n : ℚ) ^ 2 / 2 := by
  intro n hn G _ w hw hfar
  obtain ⟨P, hP⟩ := E18.uniformTransferAt_explicit (η / 2) (by positivity) n hn G w hw
  obtain ⟨Q, hQ4, hQsize⟩ := exists_cliquePartition_of_packing P
  refine ⟨Q, hQ4, ?_⟩
  have hsize : (Q.size : ℚ) + (P.gain : ℚ) = (G.edgeFinset.card : ℚ) := by
    exact_mod_cast hQsize
  linarith

/-- The explicit threshold of chordal linear stability:
near threshold `4·10¹²`, far threshold `NfarE η₀`, and `5`. -/
noncomputable def stabThreshold : ℕ :=
  max (max (4 * 10 ^ 12) (E18.NfarE PaperIV.NearH1Calibration.eta)) 5

theorem eta_eq_eta0 : PaperIV.NearH1Calibration.eta = E18.Numeric.eta0 := by
  norm_num [PaperIV.NearH1Calibration.eta, E18.Numeric.eta0]

theorem four_e12_le_tower : 4 * 10 ^ 12 ≤ E19.tower2 (E18.Numeric.hIter + 7) := by
  have hbase : 4 * 10 ^ 12 ≤ E18.Numeric.k0num := by
    norm_num [E18.Numeric.k0num]
  have hiter := E19.le_iterate_stepBound E18.Numeric.hIter E18.Numeric.k0num
  have htower := E19.Tnum_le_tower2
  have hmono := E19.tower2_mono (show E18.Numeric.hIter + 5 ≤ E18.Numeric.hIter + 7 by omega)
  exact hbase.trans (hiter.trans (htower.trans hmono))

/-- **The stability threshold is below the tower `T(h+7)`** (`h = hIter` of §6.3). -/
theorem stabThreshold_le_tower : stabThreshold ≤ E19.tower2 (E18.Numeric.hIter + 7) := by
  have h1 := four_e12_le_tower
  have h2 : E18.NfarE PaperIV.NearH1Calibration.eta ≤ E19.tower2 (E18.Numeric.hIter + 7) := by
    rw [eta_eq_eta0]; exact E19.NfarE_eta0_le_tower
  unfold stabThreshold
  refine max_le (max_le h1 h2) (le_trans (by norm_num) h1)

open PaperIV.NearH1StructureWitness PaperIV.SplitUniformIncidence
  PaperIV.GraphFamilyDistance in
/-- **BP-01 with an explicit threshold.**  Same statement as
`PaperIV.IntegralStability.chordal_linear_stability_sixteen`, with `N = stabThreshold`. -/
theorem chordal_linear_stability_explicit :
    ∀ n : ℕ, stabThreshold ≤ n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      PaperIV.FarRounding.IsChordal G → ∀ δ : ℚ, 0 ≤ δ →
        δ ≤ PaperIV.IntegralStability.gamma * (n : ℚ) ^ 2 →
        (∀ Q : CliquePartition G, Q.OrderAtMost 4 →
            (PaperIV.targetSize n : ℚ) - δ ≤ (Q.size : ℚ)) →
          ∃ R : Finset (Fin n), G.IsClique (R : Set (Fin n)) ∧
            2 ≤ R.card ∧ R.card ≤ (Finset.univ \ R).card ∧
            PaperIV.splitBaseline (n : ℚ) R.card ≤
              (PaperIV.targetSize n : ℚ) ∧
            (117 : ℚ) / 1825 *
                ((PaperIV.RootVocab.outsideEdges G R).card : ℚ) +
              (12687 : ℚ) / 20000 *
                (PaperIV.RootVocab.missingIncidences G R : ℚ) ≤ δ ∧
            (PaperIV.targetSize n : ℚ) -
                PaperIV.splitBaseline (n : ℚ) R.card +
              ((PaperIV.RootVocab.outsideEdges G R).card : ℚ) / 16 +
              (PaperIV.RootVocab.missingIncidences G R : ℚ) / 2 ≤ δ ∧
            (PaperIV.EditMetric.editDist G.edgeFinset
                (graphEdgeSupport (splitGraph R (Finset.univ \ R))) : ℚ) ≤ 16 * δ := by
  classical
  intro n hn G _ hG δ hδ0 hδ hmin
  have hn5 : 5 ≤ n := le_trans (Nat.le_max_right _ _) hn
  have hnnear : 4 * 10 ^ 12 ≤ n :=
    le_trans (le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)) hn
  have hnfar : E18.NfarE PaperIV.NearH1Calibration.eta ≤ n :=
    le_trans (le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)) hn
  obtain ⟨w, hw⟩ := PaperIV.CertifiedOptimumExistence.exists_certifiedFractionalOptimum G
  by_cases hslack : (G.edgeFinset.card : ℚ) - w <
      (n : ℚ) ^ 2 / 6 - PaperIV.NearH1Calibration.eta * (n : ℚ) ^ 2
  · exfalso
    obtain ⟨Q, hQ4, hQlt⟩ := farSlack_explicit _ PaperIV.IntegralStability.eta_pos n hnfar G w hw
      hslack
    have h1 := hmin Q hQ4
    have h2 := PaperIV.FarSlackQuantitative.sq_div_six_le_targetSize hn5
    have hn5Q : (5 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn5
    have hsq : (0 : ℚ) < (n : ℚ) ^ 2 := by nlinarith
    have hγ : PaperIV.IntegralStability.gamma = PaperIV.NearH1Calibration.eta / 4 := rfl
    rw [hγ] at hδ
    nlinarith [PaperIV.IntegralStability.eta_pos]
  · obtain ⟨W⟩ := PaperIV.NearH1Localization.exists_nearStructureWitness_of_nearRegime
      hnnear G hG hw hslack
    set R : Finset (Fin n) := W.regularized.root with hRdef
    have hRclique : G.IsClique (R : Set (Fin n)) := W.regularized.isClique
    have hRtwo : 2 ≤ R.card := by
      have h := W.regularized.card_ge
      rw [hRdef]
      omega
    have hRout : R.card ≤ (Finset.univ \ R).card := W.regularized.root_le_outside
    obtain ⟨Q, hQ4, hQsize⟩ :=
      PaperIV.NearRegimePacking.exists_cliquePartition_card_completion W.isPacking
    have hbase : (W.accounts.baseCount : ℚ) =
        PaperIV.splitBaseline (n : ℚ) W.accounts.split := by
      have h := W.accounts.base_eq
      rw [W.accounts_order] at h
      simpa using h
    have hbaseZ : ((W.accounts.baseCount : ℤ)) ≤ (PaperIV.targetSize n : ℤ) :=
      PaperIV.SplitBaselineTarget.splitBaseline_le_targetSize (by exact_mod_cast hbase)
    have hbaseQ : (W.accounts.baseCount : ℚ) ≤ (PaperIV.targetSize n : ℚ) := by
      exact_mod_cast hbaseZ
    have hpaid := W.accounts_count_le_improved
    rw [← W.accounts.base_eq] at hpaid
    have hQmin := hmin Q hQ4
    rw [hQsize] at hQmin
    have hacct : (117 : ℚ) / 1825 * (W.accounts.missingEdges.card : ℚ)
        + (12687 : ℚ) / 20000 *
            (W.accounts.rootLossEdges.card : ℚ) ≤ δ := by linarith
    have hm : W.accounts.missingEdges.card = (PaperIV.RootVocab.outsideEdges G R).card := by
      rw [W.accounts_missing]
    have hA : W.accounts.rootLossEdges.card = PaperIV.RootVocab.missingIncidences G R := by
      rw [W.accounts_rootLoss, PaperIV.RD09SplitEditAccount.card_missingSpokeEdges]
    have hbaseR : (W.accounts.baseCount : ℚ) =
        PaperIV.splitBaseline (n : ℚ) R.card := by
      rw [hbase, W.accounts_split]
    have hbaseline : PaperIV.splitBaseline (n : ℚ) R.card ≤
        (PaperIV.targetSize n : ℚ) := by
      rw [← hbaseR]
      exact hbaseQ
    have hreserve : (PaperIV.targetSize n : ℚ) -
          PaperIV.splitBaseline (n : ℚ) R.card +
        ((PaperIV.RootVocab.outsideEdges G R).card : ℚ) / 16 +
        (PaperIV.RootVocab.missingIncidences G R : ℚ) / 2 ≤ δ := by
      have hm0 : (0 : ℚ) ≤ (W.accounts.missingEdges.card : ℚ) := by positivity
      have hA0 : (0 : ℚ) ≤ (W.accounts.rootLossEdges.card : ℚ) := by positivity
      rw [← hm, ← hA, ← hbaseR]
      linarith
    rw [hm, hA] at hacct
    refine ⟨R, hRclique, hRtwo, hRout, hbaseline, hacct, hreserve, ?_⟩
    rw [PaperIV.SplitEditIdentity.editDist_split_eq G hRclique]
    have hAnn : (0 : ℚ) ≤ (PaperIV.RootVocab.missingIncidences G R : ℚ) := by positivity
    push_cast
    linarith

end E33
