import E17.ExplicitFarAssembly
import PaperIV.NearH1GlobalAssembly
import PaperIV.Erdos81AllOrders

/-!
# Explicit global threshold and all-orders additive constant

The unconditional numerical far threshold is joined to the *actual* near
threshold, 4 * 10^12. No design-theoretic hypothesis is imported or assumed.
The tower is kept symbolic throughout: this is an effective bound, not a
practically evaluable order. The additive constant is not asserted optimal.
The far partition is produced by R3/F1 with the explicit E18 schedule;
E19 supplies its numerical upper bound, not the old final rounding theorem.
-/

namespace PaperIV.ExplicitThreshold

open PaperIV.FarRounding

irreducible_def sharpThreshold : ℕ := E19.tower2 (E18.Numeric.hIter + 7)

def additiveConstant : ℕ := sharpThreshold ^ 2

theorem nearThreshold_le : 4 * 10 ^ 12 ≤ sharpThreshold := by
  rw [sharpThreshold_def]
  have hbase : 4 * 10 ^ 12 ≤ E18.Numeric.k0num := by
    norm_num [E18.Numeric.k0num]
  have hiter := E19.le_iterate_stepBound E18.Numeric.hIter E18.Numeric.k0num
  have htower := E19.Tnum_le_tower2
  have hmono := E19.tower2_mono (show E18.Numeric.hIter + 5 ≤ E18.Numeric.hIter + 7 by omega)
  exact hbase.trans (hiter.trans (htower.trans hmono))

/-- The sharp bound for every chordal graph above a specified tower threshold. -/
theorem erdos81_sharp_explicit (n : ℕ) (hn : sharpThreshold ≤ n)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : IsChordal G) :
    ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size ≤ targetSize n := by
  obtain ⟨w, hw⟩ := PaperIV.CertifiedOptimumExistence.exists_certifiedFractionalOptimum G
  by_cases hfar : (G.edgeFinset.card : ℚ) - w <
      (n : ℚ) ^ 2 / 6 - PaperIV.NearH1Calibration.eta * (n : ℚ) ^ 2
  · apply E17Bridge.ExplicitAssembly.farRegime_eta0_tower n
      (by simpa only [sharpThreshold_def] using hn) G
    rw [PaperIV.CertifiedF4Bridge.F4'_eq_edge_sub_certified hw]
    have hr := (show ((G.edgeFinset.card : ℚ) - w : ℝ) <
        (((n : ℚ) ^ 2 / 6 - PaperIV.NearH1Calibration.eta * (n : ℚ) ^ 2 : ℚ) : ℝ) by
      exact_mod_cast hfar)
    simpa only [Rat.cast_sub, Rat.cast_natCast, Rat.cast_div, Rat.cast_pow,
      Rat.cast_ofNat, Rat.cast_mul, PaperIV.NearH1Calibration.eta, E18.Numeric.eta0] using hr
  · obtain ⟨W⟩ := PaperIV.NearH1Localization.exists_nearStructureWitness_of_nearRegime
      (nearThreshold_le.trans hn) G hG hw hfar
    simpa using PaperIV.NearRegimePacking.exists_cliquePartition_target_of_physicalAccounts
      W.isPacking W.accounts W.accounts_order

private theorem square_le_two_pow (n : ℕ) (hn : 4 ≤ n) : n ^ 2 ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [pow_succ (2 : ℕ) n]
    nlinarith

private theorem tower_square_le_next (h : ℕ) (hh : 4 ≤ E19.tower2 h) :
    E19.tower2 h ^ 2 ≤ E19.tower2 (h + 1) := by
  rw [E19.tower2_succ]
  exact square_le_two_pow _ hh

private theorem tower_square_add_seven (h : ℕ) (hh : 4 ≤ E19.tower2 (h + 7)) :
    E19.tower2 (h + 7) ^ 2 ≤ E19.tower2 (h + 8) := by
  simpa only [Nat.add_assoc] using tower_square_le_next (h + 7) hh

theorem additiveConstant_le_tower :
    additiveConstant ≤ E19.tower2 (E18.Numeric.hIter + 8) := by
  have hN : 4 ≤ sharpThreshold := le_trans (by norm_num) nearThreshold_le
  rw [additiveConstant, sharpThreshold_def]
  exact tower_square_add_seven _ (by simpa only [sharpThreshold_def] using hN)

/-- All orders, with the fixed constant N^2 (not an existential threshold). -/
theorem erdos81_all_orders_explicit (n : ℕ) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hG : IsChordal G) :
    ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧
      Q.size ≤ targetSize n + additiveConstant := by
  classical
  by_cases hn : sharpThreshold ≤ n
  · obtain ⟨Q, h4, hsize⟩ := erdos81_sharp_explicit n hn G hG
    exact ⟨Q, h4, hsize.trans (Nat.le_add_right _ _)⟩
  · obtain ⟨Q, h4, hsize⟩ := PaperIV.Erdos81AllOrders.exists_trivial_cliquePartition G
    refine ⟨Q, h4, ?_⟩
    have he : G.edgeFinset.card ≤ n.choose 2 := by
      simpa using (SimpleGraph.card_edgeFinset_le_card_choose_two (G := G))
    have hid := PaperIV.SplitUniformIncidence.mul_pred_eq_two_mul_choose_two n
    have hpred : n * (n - 1) ≤ n * n := Nat.mul_le_mul_left n (by omega)
    have hnn : n * n ≤ sharpThreshold * sharpThreshold :=
      Nat.mul_le_mul (by omega) (by omega)
    change Q.size ≤ targetSize n + sharpThreshold ^ 2
    nlinarith

/-- A bounded additive witness for Erdős #81, with no mathematical input
beyond the finite chordal graph; all thresholds are discharged internally. -/
theorem erdos81_all_orders_bounded_additive :
    ∃ b : ℕ, b ≤ E19.tower2 (E18.Numeric.hIter + 8) ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], IsChordal G →
        ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size ≤ targetSize n + b :=
  ⟨additiveConstant, additiveConstant_le_tower, erdos81_all_orders_explicit⟩

end PaperIV.ExplicitThreshold
