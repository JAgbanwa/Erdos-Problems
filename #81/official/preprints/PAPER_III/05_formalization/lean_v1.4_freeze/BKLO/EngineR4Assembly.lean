/-
# Assembling the repaired fused §10 interface `BKLO.VortexReservoirEngineR4`.

This is `BKLO/EngineR3Assembly.lean` redone for the repaired reservoir clause: the three vortex
ingredients — the schedule window, the bottom clause, the descent clause — are the same theorems,
and the reservoir clause is passed through from `BKLO.ReservoirClauseResidual4`.

Everything here is `sorry`-free.
-/
import BKLO.ReservoirLarge
import BKLO.EngineR3Assembly
import BKLO.MainR4

open Finset

namespace BKLO

set_option maxHeartbeats 1000000 in
/-- **The repaired fused §10 interface follows from the repaired residual reservoir clause.**

All the vortex clauses are supplied here, with the explicit power-law schedule of
`BKLO/ScheduleR3.lean`: the window `C := 2n₂` is taken large enough for the amplitude condition
`250√K ≤ (ε/4)C^{1/4}` of the descent clause and for the bottom clause's requirement
`1000k ≤ εn₂`. -/
theorem vortexReservoirEngineR4_of_reservoir4 (h : ReservoirClauseResidual4) :
    VortexReservoirEngineR4 := by
  intro ε hε hε' n₀ N
  -- the constants
  set K : ℕ := max 800 ⌈(8 : ℝ) / ε⌉₊ with hKdef
  have hK800 : 800 ≤ K := le_max_left _ _
  have hK2 : 2 ≤ K := le_trans (by norm_num) hK800
  have hKR : (800 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK800
  have hKpos : (0 : ℝ) < (K : ℝ) := by linarith only [hKR]
  have hKε : (8 : ℝ) / ε ≤ (K : ℝ) := by
    have h1 : (8 : ℝ) / ε ≤ (⌈(8 : ℝ) / ε⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((⌈(8 : ℝ) / ε⌉₊ : ℕ) : ℝ) ≤ (K : ℝ) := by
      exact_mod_cast Nat.le_max_right 800 ⌈(8 : ℝ) / ε⌉₊
    linarith only [h1, h2]
  obtain ⟨η, n₃, hη, hn₃⟩ := h ε hε hε' K hK800 hKε
  -- the exponent of the bottom clause
  obtain ⟨k₀, hk₀⟩ :=
    exists_pow_lt_of_lt_one (show (0 : ℝ) < ε / (16 * (K : ℝ) * (K : ℝ)) by positivity)
      (show (1 : ℝ) - ε < 1 by linarith)
  set k : ℕ := max 1 k₀ with hkdef
  have hk1 : 1 ≤ k := le_max_left _ _
  have hkσ : (1 - ε) ^ k ≤ ε / (16 * (K : ℝ) * (K : ℝ)) :=
    le_of_lt (lt_of_le_of_lt
      (pow_le_pow_of_le_one (by linarith) (by linarith) (le_max_right 1 k₀)) hk₀)
  -- the two size thresholds
  obtain ⟨A, hA⟩ := exists_nat_gt ((1000 * Real.sqrt (K : ℝ) / ε) ^ 4)
  obtain ⟨Bn, hBn⟩ := exists_nat_gt ((1000 : ℝ) * (k : ℝ) / ε)
  set n₂ : ℕ := max (max n₀ (N η)) (max (max n₃ A) (max Bn 1)) with hn₂def
  set C : ℕ := 2 * n₂ with hCdef
  have hn₂1 : 1 ≤ n₂ :=
    le_trans (le_trans (le_max_right Bn 1) (le_max_right _ _)) (le_max_right _ _)
  have hn₂pos : 0 < n₂ := hn₂1
  have hCpos : 0 < C := by omega
  have hn₂R : (1 : ℝ) ≤ (n₂ : ℝ) := by exact_mod_cast hn₂1
  have hn₀ : n₀ ≤ n₂ := le_trans (le_max_left _ _) (le_max_left _ _)
  have hN : N η ≤ n₂ := le_trans (le_max_right _ _) (le_max_left _ _)
  have hn₃le : n₃ ≤ n₂ :=
    le_trans (le_trans (le_max_left n₃ A) (le_max_left _ _)) (le_max_right _ _)
  have hAle : A ≤ n₂ :=
    le_trans (le_trans (le_max_right n₃ A) (le_max_left _ _)) (le_max_right _ _)
  have hBnle : Bn ≤ n₂ :=
    le_trans (le_trans (le_max_left Bn 1) (le_max_right _ _)) (le_max_right _ _)
  -- the schedule window
  have hwin : ∀ s : ℕ, n₂ ≤ s →
      9 / 10 + ε / 2 ≤ powerSchedule ε C s ∧ powerSchedule ε C s ≤ 9 / 10 + 3 * ε / 4 :=
    fun s _ => powerSchedule_window hε hCpos s
  -- the amplitude condition
  have hamp : 250 * Real.sqrt (K : ℝ) ≤ ε / 4 * qrt (C : ℝ) := by
    have hACR : ((1000 : ℝ) * Real.sqrt (K : ℝ) / ε) ^ 4 ≤ (C : ℝ) := by
      have h1 : (A : ℝ) ≤ (n₂ : ℝ) := by exact_mod_cast hAle
      have h2 : (n₂ : ℝ) ≤ (C : ℝ) := by
        have : (n₂ : ℕ) ≤ C := by omega
        exact_mod_cast this
      linarith only [hA, h1, h2]
    have hq : 1000 * Real.sqrt (K : ℝ) / ε ≤ qrt (C : ℝ) :=
      le_qrt_of (by positivity) hACR
    have := mul_le_mul_of_nonneg_left hq (show (0 : ℝ) ≤ ε / 4 by linarith)
    calc 250 * Real.sqrt (K : ℝ) = ε / 4 * (1000 * Real.sqrt (K : ℝ) / ε) := by
          field_simp; ring
      _ ≤ ε / 4 * qrt (C : ℝ) := this
  -- the bottom-clause threshold
  have hkn₂ : (1000 : ℝ) * (k : ℝ) ≤ ε * (n₂ : ℝ) := by
    have h1 : (Bn : ℝ) ≤ (n₂ : ℝ) := by exact_mod_cast hBnle
    have h2 : (1000 : ℝ) * (k : ℝ) / ε < (n₂ : ℝ) := lt_of_lt_of_le hBn h1
    rw [div_lt_iff₀ hε] at h2
    nlinarith only [h2]
  refine ⟨powerSchedule ε C, n₂, C, K, η, hK2, hKε, hη, hn₀, hN, by omega, hn₂pos, hwin, ?_, ?_, ?_⟩
  · exact vortexBottomClauseR2_of_schedule_window hε hε' hK2 hk1
      (fun s _ hsC => le_of_eq (powerSchedule_of_le hCpos hsC)) hkσ hkn₂ (by omega)
  · refine vortexDescentClauseR3_of_powerSchedule hε hε' hK800 hn₂pos ?_ hamp
    calc C = 2 * n₂ := hCdef
      _ ≤ K * n₂ := Nat.mul_le_mul_right _ (by omega)
  · exact hn₃ (powerSchedule ε C) n₂ hn₃le hwin

/-- **Main theorem (AX2 half of Erdős #81), from the three classical inputs and the repaired
residual reservoir clause.**  All the vortex clauses of the §10 interface are theorems; the only
remaining hypothesis beyond the three classical inputs is `BKLO.ReservoirClauseResidual4` — the
residual `BKLO.ReservoirClauseResidual` of `BKLO/EngineR3Assembly.lean` with the protected level
required to be empty or of size at least `n₂`, without which it is false
(`BKLO.not_reservoirClauseResidual`). -/
theorem triangle_decomposition_of_inputs_and_reservoir4
    (hDross : FracTriangleThreshold) (hNib : FracToApproxMaxDeg) (hDirac : PerfectMatchingDirac)
    (hRes : ReservoirClauseResidual4) :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ,
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        n₀ ≤ Fintype.card V →
        (3 ∣ G.edgeFinset.card ∧ ∀ v, Even (G.degree v)) →
        (9 / 10 + ε) * (Fintype.card V : ℝ) ≤ (G.minDegree : ℝ) →
        TriangleDecomposable G :=
  triangle_decomposition_of_inputs_repaired4 hDross hNib hDirac
    (vortexReservoirEngineR4_of_reservoir4 hRes)

end BKLO
