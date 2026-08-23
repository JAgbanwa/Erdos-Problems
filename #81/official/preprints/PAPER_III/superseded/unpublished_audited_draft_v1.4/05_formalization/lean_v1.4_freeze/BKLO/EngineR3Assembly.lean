/-
# Assembling the thrice-repaired fused §10 interface.

Three of the four ingredients of `BKLO.VortexReservoirEngineR3` are theorems:

* the schedule window — `BKLO.powerSchedule_window`;
* the bottom clause — `BKLO.vortexBottomClauseR2_of_schedule_window` (`BKLO/BottomClause.lean`);
* the descent clause — `BKLO.vortexDescentClauseR3_of_powerSchedule` (`BKLO/ScheduleR3.lean`),
  itself built on the random level of `BKLO/LevelSampling.lean`.

What is left is the *reservoir* clause, and this file isolates exactly what is left of it:
`BKLO.ReservoirClauseResidual`.  It is the reservoir clause `BKLO.ReservoirClauseR` — unchanged,
in particular with the two repairs (between-levels density, global multiplicity bound) that the
refutations of the earlier versions forced — asked of an *arbitrary* schedule confined to the
window `[9/10 + ε/2, 9/10 + 3ε/4]`, above a threshold `n₃` that may depend on `ε`, `η` and `K`.
It quantifies over nothing that the engine chooses, so it is not circular: the schedule, the
window `C` and the scale `n₂` are chosen *after* it, in `BKLO.vortexReservoirEngineR3_of_reservoir`.

The perturbation scale `η` is **existentially** quantified in the residual, exactly as it is in
the interface itself.  This is not cosmetic.  A reservoir `R` that is apex-abundant at scale `η`
has `2η|W| ≤ |resLink R W' u|` for every `u ∈ W \ W'`, and taking `X u` to be `resLink R W' u`
(made even) gives an admissible link system with `∑ᵤ |X u| ≥ |W \ W'| · (2η|W| - 1)`.  A link
cover of it consists of triangles with exactly one vertex in `W \ W'`, so it spends one edge
inside `W'` per two crossing edges, and the multiplicity bound caps the total at
`(ε/8)|W'|²`.  Since `K|W'| ≤ |W|`, this forces `η = O(ε/K²)`: the clause is *false* for `η`
comparable to `ε`.  Only the nibble threshold `N η` depends on `η`, and `n₂` is chosen after it,
so a small `η` costs the derivation nothing.

Everything here is `sorry`-free.
-/
import BKLO.ScheduleR3
import BKLO.BottomClause

open Finset

namespace BKLO

/-- **The residual reservoir clause.**  The one ingredient of `BKLO.VortexReservoirEngineR3` that
is not proved here: a crossing, vertex-sparse, apex-abundant reservoir whose admissible link
systems are all coverable, for every large enough scale and every schedule in the window. -/
def ReservoirClauseResidual : Prop :=
  ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 100 → ∀ K : ℕ, 800 ≤ K → (8 : ℝ) / ε ≤ (K : ℝ) →
    ∃ (η : ℝ) (n₃ : ℕ), 0 < η ∧ ∀ (f : ℕ → ℝ) (n₂ : ℕ), n₃ ≤ n₂ →
      (∀ s : ℕ, n₂ ≤ s → 9 / 10 + ε / 2 ≤ f s ∧ f s ≤ 9 / 10 + 3 * ε / 4) →
      ReservoirClauseR ε η f n₂ K

set_option maxHeartbeats 1000000 in
/-- **The thrice-repaired fused §10 interface follows from the residual reservoir clause.**

All the vortex clauses are supplied here, with the explicit power-law schedule of
`BKLO/ScheduleR3.lean`: the window `C := 2n₂` is taken large enough for the amplitude condition
`250√K ≤ (ε/4)C^{1/4}` of the descent clause and for the bottom clause's requirement
`1000k ≤ εn₂`. -/
theorem vortexReservoirEngineR3_of_reservoir (h : ReservoirClauseResidual) :
    VortexReservoirEngineR3 := by
  intro ε hε hε' n₀ N
  -- the constants
  set K : ℕ := max 800 ⌈(8 : ℝ) / ε⌉₊ with hKdef
  have hK800 : 800 ≤ K := le_max_left _ _
  have hK2 : 2 ≤ K := le_trans (by norm_num) hK800
  have hKR : (800 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK800
  have hKpos : (0 : ℝ) < (K : ℝ) := by linarith
  have hKε : (8 : ℝ) / ε ≤ (K : ℝ) := by
    have h1 : (8 : ℝ) / ε ≤ (⌈(8 : ℝ) / ε⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((⌈(8 : ℝ) / ε⌉₊ : ℕ) : ℝ) ≤ (K : ℝ) := by
      exact_mod_cast Nat.le_max_right 800 ⌈(8 : ℝ) / ε⌉₊
    linarith
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
      linarith
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
    linarith
  refine ⟨powerSchedule ε C, n₂, C, K, η, hK2, hKε, hη, hn₀, hN, by omega, hn₂pos, hwin, ?_, ?_, ?_⟩
  · exact vortexBottomClauseR2_of_schedule_window hε hε' hK2 hk1
      (fun s _ hsC => le_of_eq (powerSchedule_of_le hCpos hsC)) hkσ hkn₂ (by omega)
  · refine vortexDescentClauseR3_of_powerSchedule hε hε' hK800 hn₂pos ?_ hamp
    calc C = 2 * n₂ := hCdef
      _ ≤ K * n₂ := Nat.mul_le_mul_right _ (by omega)
  · exact hn₃ (powerSchedule ε C) n₂ hn₃le hwin

end BKLO
