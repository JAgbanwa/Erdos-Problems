import PaperIV.NearH1WindowAccounts
import PaperIV.GatedTerminalSplit
import PaperIV.NearH1SplitComparator
import PaperIV.NearH1StructureWitness

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
theorem exists_localized_split_core {n : ℕ} (hn : 4 * 10 ^ 12 ≤ n)
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
  -- `Ddef` es el déficit terminal; el presupuesto de cuentas es `16 * Ddef` (coeficientes
  -- mejorados del ledger), y el descenso lo consume en la forma `20 * D`.
  let Ddef : ℚ := PaperIV.NearH1Calibration.eta * nq ^ 2 + nq / 6 + 1 / 24
  let D : ℚ := 4 / 5 * Ddef
  have hnQ : 4 * (10 : ℚ) ^ 12 ≤ nq := by
    dsimp [nq]
    exact_mod_cast hn
  have hnpos : 0 < nq := by dsimp [nq]; positivity
  have hn2 : 2 ≤ n := by omega
  -- El descenso sólo pide `contracted ≤ barrier ≤ outer - 1/n`.  Se toma por tanto la
  -- barrera **máxima** admisible, `eps - 1/n`, y `contracted = barrier`: los dos factores
  -- dos que antes se regalaban (`barrier = eps/2` y `contracted = barrier/2`) eran holgura
  -- pura y son justamente los que fijaban el umbral.
  have hinvSmall : 1 / nq ≤ PaperIV.NearH1Calibration.eps / 2 := by
    rw [div_le_iff₀ hnpos]
    dsimp [PaperIV.NearH1Calibration.eps]
    nlinarith
  have houter : (PaperIV.NearH1Calibration.eps - 1 / (Fintype.card (Fin n) : ℚ)) +
      1 / (Fintype.card (Fin n) : ℚ) ≤ PaperIV.NearH1Calibration.eps :=
    le_of_eq (by ring)
  have hcontract : PaperIV.NearH1Calibration.eps - 1 / (Fintype.card (Fin n) : ℚ) ≤
      PaperIV.NearH1Calibration.eps - 1 / (Fintype.card (Fin n) : ℚ) := le_rfl
  have hDcontract : 20 * D / nq ^ 2 <
      PaperIV.NearH1Calibration.eps - 1 / nq := by
    have hexp : (PaperIV.NearH1Calibration.eps - 1 / nq) * nq ^ 2 =
        PaperIV.NearH1Calibration.eps * nq ^ 2 - nq := by
      field_simp
    rw [div_lt_iff₀ (sq_pos_of_pos hnpos), hexp]
    dsimp [D, Ddef, PaperIV.NearH1Calibration.eta, PaperIV.NearH1Calibration.eps]
    nlinarith [sq_nonneg (nq - 4 * (10 : ℚ) ^ 12)]
  obtain ⟨H, Cterm, hpath, hHchord, hHsplit, hF4H⟩ :=
    PaperIV.GatedTerminalSplit.exists_split_terminal_symmetrizationPath G hG
  have hterminal : graphFamDistNorm
      (allSplitSupports (V := Fin n)) allSplitSupports_nonempty H (nq ^ 2) <
        PaperIV.NearH1Calibration.eps - 1 / nq := by
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
    have hpos : (0 : ℚ) < PaperIV.NearH1Calibration.eps - 1 / nq := by
      have : (0 : ℚ) < PaperIV.NearH1Calibration.eps / 2 := by
        dsimp [PaperIV.NearH1Calibration.eps]; norm_num
      linarith
    simpa using hpos
  have hlocal : ∀ X : SimpleGraph (Fin n), PaperIV.IsChordal X →
      F4' G ≤ F4' X → F4' X ≤ F4' H →
      graphFamDistNorm (allSplitSupports (V := Fin n)) allSplitSupports_nonempty X
          (nq ^ 2) < PaperIV.NearH1Calibration.eps →
      ∃ m A : ℚ, 0 ≤ A ∧ m + A ≤ 20 * D ∧
        graphFamDistNorm (allSplitSupports (V := Fin n)) allSplitSupports_nonempty X
            (nq ^ 2) * nq ^ 2 ≤ m + A := by
    intro X hX hGX _ hdist
    obtain ⟨m, A, hA, hacc, hle⟩ := PaperIV.NearH1WindowAccounts.exists_window_accounts
      G X hX hw (by simpa using hnear) hGX (by simpa [nq] using hnQ)
        (by simpa [nq] using hdist)
    refine ⟨m, A, hA, ?_, by simpa [nq] using hle⟩
    have hacc' : m + A ≤ 16 * Ddef := by simpa [nq, Ddef] using hacc
    dsimp [D]
    linarith
  have hDcontract' :
      20 * (4 / 5 * (PaperIV.NearH1Calibration.eta * (Fintype.card (Fin n) : ℚ) ^ 2 +
        (Fintype.card (Fin n) : ℚ) / 6 + 1 / 24)) /
          (Fintype.card (Fin n) : ℚ) ^ 2 <
        PaperIV.NearH1Calibration.eps - 1 / (Fintype.card (Fin n) : ℚ) := by
    dsimp [D, Ddef, nq] at hDcontract
    simpa using hDcontract
  have hGdist := PaperIV.LocalStability.localize_original_of_windowed_accounts_descent
    (allSplitSupports (V := Fin n)) allSplitSupports_nonempty (by simpa using hn2)
    houter hcontract hG
    (by simpa [nq, D, Ddef] using hlocal) hDcontract' hpath
    (by simpa [nq] using hterminal)
  have hGdist' : graphFamDistNorm
      (allSplitSupports (V := Fin n)) allSplitSupports_nonempty G (nq ^ 2) <
        PaperIV.NearH1Calibration.eps - 1 / nq := by
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
        have hinv0 : (0 : ℚ) ≤ ((n : ℚ))⁻¹ := by positivity
        linarith)
      (by simpa [nq] using hnearG)
  exact ⟨C, hC, by simpa [nq] using hedit, by simpa [nq] using hres⟩

/-- **Paquete estructural cercano.**  Composición única de la localización por descenso con
el constructor estructural del comparador.  Las dos rutas cercanas —la numérica de
`PaperIV.NearH1GlobalAssembly.nearRegimeAt` y la estructural de
`PaperIV.HybridDichotomy.chordal_near_extremal_stability`— consumen exactamente este
enunciado, de modo que el paso «núcleo comparador → testigo» ocurre una sola vez, igual que
ya ocurría con el descenso. -/
theorem exists_nearStructureWitness_of_nearRegime {n : ℕ} (hn : 4 * 10 ^ 12 ≤ n)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : PaperIV.IsChordal G) {w : ℚ} (hw : CertifiedFractionalOptimum G w)
    (hnear : ¬ ((G.edgeFinset.card : ℚ) - w <
      (n : ℚ) ^ 2 / 6 - PaperIV.NearH1Calibration.eta * (n : ℚ) ^ 2)) :
    Nonempty (PaperIV.NearH1StructureWitness.NearStructureWitness G) := by
  classical
  have hnQ : 4 * (10 : ℚ) ^ 12 ≤ (n : ℚ) := by exact_mod_cast hn
  obtain ⟨C, hC, hedit, hres⟩ := exists_localized_split_core hn G hG hw hnear
  let S : SimpleGraph (Fin n) :=
    PaperIV.SplitUniformIncidence.splitGraph C (Finset.univ \ C)
  letI : DecidableRel S.Adj := Classical.decRel _
  exact PaperIV.NearH1StructureWitness.exists_nearStructureWitness_of_split_comparator
    G S hG C hC (fun _ _ => Iff.rfl) (by simpa using hnQ)
    (by
      simpa [PaperIV.NearH1SplitComparator.deltaCal] using hres)
    (by
      simpa [S, PaperIV.GraphFamilyDistance.graphEdgeSupport_eq_edgeFinset]
        using hedit)

end PaperIV.NearH1Localization
