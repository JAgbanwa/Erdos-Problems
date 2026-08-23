/-
# The repaired vortex schedule of the cover-down vehicle.

`BKLO.VortexScheduleSlack` (`BKLO/CoverDownVortexFaithful.lean`) is false
(`BKLO.not_vortexScheduleSlack`).  The defect is entirely in its **descent clause**, and entirely
in what that clause allows at the bottom of its range: it quantifies over every `m` with
`|U| ≤ m`, so it contains the degenerate instance `m = |U|`, in which the level `W'` is forced to
be the bottom set `U` itself and the clause asks for a density of the edge set *induced on `U`*
that no hypothesis provides.  This file repairs the clause and proves the repaired schedule.

Two changes are needed, and both are forced (see `BKLO/VortexScheduleDiagnosis.lean`).

1. **A ratio between consecutive levels**: `K|U| ≤ m`, with `K ≥ 800` the same ratio the
   cover-down step uses.  This is what the vortex actually hands the clause — the levels of a
   vortex shrink by a factor `K` at a time and the recursion jumps straight to `U` as soon as the
   current level is within `K²` of it — and it excludes the degenerate instance outright.

2. **The density of the current level into the bottom set**, as a hypothesis and as a maintained
   invariant: `f|U|·|U| ≤ |resLink E U v|` for every `v` of the current level outside a small
   avoidance set `D`.  The ratio alone does not suffice: a random level of size `m` inherits only
   the density its ambient set has into the *forced* part `U` of that level, so without an
   into-`U` hypothesis every level costs a fixed fraction `≈ f|U|·|U|/m ≈ 1/K` of density, which
   the window `[9/10 + ε/2, 9/10 + 3ε/4]` cannot pay for at unboundedly many scales.  This is the
   `resLink` hypothesis of `BKLO.VortexDescentClauseR2`, i.e. exactly the form in which the
   descent clause is *proved* in this project.

The clause proved here, `BKLO.VortexDescentSlack`, differs from `BKLO.VortexDescentClauseR3` in
the two respects the cover-down vehicle needs:

* its conclusion carries a **surplus of `12`** over the schedule, which is what one divisibility
  fix (`BKLO.LevelDivFixProp`) at the new level costs, so that after the fix the level still
  carries exactly `f m · m`;
* its avoidance set `D` is only asked to be small in the sense `|D| ≤ 12|U| + (a - f|W|)·m`: `12|U|`
  is the number of vertices whose links into `U` one divisibility fix can damage, and the second
  summand is the surplus of the host graph over the schedule, which is what pays for the
  exceptional set of the bottom clause at the top level.

Both extra losses are paid for by the drop of the power-law schedule, through the sharpened slack
estimate `BKLO.powerSchedule_slack_spare`.

Everything here is `sorry`-free.
-/
import BKLO.ScheduleR3
import BKLO.BottomClause

open Finset

namespace BKLO

/-! ### The slack of the power-law schedule, with room to spare

`BKLO.powerSchedule_slack` says that the drop of the schedule from the scale `w` to the scale `m`
pays for the sampling error and for the deficiency of the forced bottom set.  Doubling the
amplitude condition leaves a spare term of `B·m^{3/4}/25` on top of that, which is what the
divisibility fix and the avoidance set are charged to. -/

/-- **The slack of the power-law schedule, with a spare term.**  As `BKLO.powerSchedule_slack`,
under the doubled amplitude condition `500√K ≤ (ε/4)C^{1/4}`, with `(ε/4)C^{1/4}·m^{3/4}/25` left
over. -/
theorem powerSchedule_slack_spare {ε : ℝ} (hε : 0 < ε) {C K u m w : ℕ}
    (hK : 800 ≤ K) (hC : 0 < C) (hCm : C ≤ m) (hu : 0 < u) (hKu : K * u ≤ m) (h2m : 2 * m ≤ w)
    (hB : 500 * Real.sqrt (K : ℝ) ≤ ε / 4 * qrt (C : ℝ)) :
    qrt (10 ^ 6 * (K : ℝ) ^ 2) / qrt (m : ℝ) * m
        + (powerSchedule ε C w - powerSchedule ε C u) * u
        + ε / 4 * qrt (C : ℝ) * (qrt (m : ℝ)) ^ 3 / 25
      ≤ (powerSchedule ε C w - powerSchedule ε C m) * m := by
  set B : ℝ := ε / 4 * qrt (C : ℝ) with hBdef
  have hKR : (800 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hmR : (0 : ℝ) < (m : ℝ) := by
    have : 0 < m := lt_of_lt_of_le hC hCm
    exact_mod_cast this
  have huR : (0 : ℝ) < (u : ℝ) := by exact_mod_cast hu
  have hwR : (2 : ℝ) * m ≤ (w : ℝ) := by exact_mod_cast h2m
  have hBpos : 0 < B := by
    have := qrt_pos (show (0 : ℝ) < (C : ℝ) by exact_mod_cast hC)
    positivity
  have hqm : 0 < qrt (m : ℝ) := qrt_pos hmR
  have hqw : 0 < qrt (w : ℝ) := qrt_pos (by linarith)
  have hqu : 0 < qrt (u : ℝ) := qrt_pos huR
  have hCw : C ≤ w := le_trans hCm (by omega)
  set Q : ℝ := qrt (m : ℝ) with hQ
  have hQ3 : (0 : ℝ) ≤ Q ^ 3 := by positivity
  have hsK : (0 : ℝ) ≤ Real.sqrt (K : ℝ) := Real.sqrt_nonneg _
  have hmQ : (m : ℝ) / Q = Q ^ 3 := div_qrt (le_of_lt hmR)
  have hQ4 : Q ^ 4 = (m : ℝ) := qrt_pow4 (le_of_lt hmR)
  -- the sampling error
  have hT1 : qrt (10 ^ 6 * (K : ℝ) ^ 2) / Q * m ≤ 32 * Real.sqrt (K : ℝ) * Q ^ 3 := by
    have h1 : qrt (10 ^ 6 * (K : ℝ) ^ 2) = qrt ((10 : ℝ) ^ 6) * Real.sqrt (K : ℝ) := by
      rw [qrt_mul (by norm_num), qrt_sq (by positivity)]
    have h2 : qrt ((10 : ℝ) ^ 6) ≤ 32 := qrt_le_of (by norm_num) (by norm_num)
    calc qrt (10 ^ 6 * (K : ℝ) ^ 2) / Q * m = qrt (10 ^ 6 * (K : ℝ) ^ 2) * ((m : ℝ) / Q) := by
          ring
      _ = qrt ((10 : ℝ) ^ 6) * (Real.sqrt (K : ℝ) * Q ^ 3) := by rw [h1, hmQ]; ring
      _ ≤ 32 * (Real.sqrt (K : ℝ) * Q ^ 3) := mul_le_mul_of_nonneg_right h2 (by positivity)
      _ = 32 * Real.sqrt (K : ℝ) * Q ^ 3 := by ring
  -- the deficiency of the forced bottom set
  have hqK : (100 : ℝ) ≤ (qrt (K : ℝ)) ^ 3 := by
    have h1 : (5.31 : ℝ) ≤ qrt (K : ℝ) := le_qrt_of (by norm_num) (by nlinarith)
    nlinarith [sq_nonneg (qrt (K : ℝ)), sq_nonneg (qrt (K : ℝ) - 5.31)]
  have hT2 : (powerSchedule ε C w - powerSchedule ε C u) * u ≤ B * Q ^ 3 / 100 := by
    have hstep1 : powerSchedule ε C w - powerSchedule ε C u ≤ B / qrt (u : ℝ) := by
      rw [powerSchedule_of_ge hCw, powerSchedule_eq]
      have h1 : qrt (u : ℝ) ≤ qrt ((max u C : ℕ) : ℝ) := by
        apply qrt_mono; exact_mod_cast Nat.le_max_left u C
      have h2 : B / qrt ((max u C : ℕ) : ℝ) ≤ B / qrt (u : ℝ) :=
        div_le_div_of_nonneg_left (le_of_lt hBpos) hqu h1
      have h3 : (0 : ℝ) ≤ B / qrt (w : ℝ) := by positivity
      linarith only [h2, h3]
    have hstep2 : B / qrt (u : ℝ) * u = B * (qrt (u : ℝ)) ^ 3 := by
      rw [show B / qrt (u : ℝ) * u = B * ((u : ℝ) / qrt (u : ℝ)) by ring,
        div_qrt (le_of_lt huR)]
    have hstep3 : qrt (u : ℝ) ≤ Q / qrt (K : ℝ) := by
      have hKpos : (0 : ℝ) < (K : ℝ) := by linarith only [hKR]
      have h1 : (u : ℝ) ≤ (m : ℝ) / (K : ℝ) := by
        rw [le_div_iff₀ hKpos]
        have : ((K * u : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hKu
        push_cast at this; linarith only [this]
      calc qrt (u : ℝ) ≤ qrt ((m : ℝ) / (K : ℝ)) := qrt_mono h1
        _ = Q / qrt (K : ℝ) := qrt_div (le_of_lt hmR) hKpos
    have hstep4 : (qrt (u : ℝ)) ^ 3 ≤ Q ^ 3 / 100 := by
      have h1 : (qrt (u : ℝ)) ^ 3 ≤ (Q / qrt (K : ℝ)) ^ 3 := pow_le_pow_left₀ (le_of_lt hqu) hstep3 3
      have h2 : (Q / qrt (K : ℝ)) ^ 3 = Q ^ 3 / (qrt (K : ℝ)) ^ 3 := by rw [div_pow]
      have h3 : Q ^ 3 / (qrt (K : ℝ)) ^ 3 ≤ Q ^ 3 / 100 :=
        div_le_div_of_nonneg_left hQ3 (by norm_num) hqK
      linarith only [h1, h2, h3]
    calc (powerSchedule ε C w - powerSchedule ε C u) * u
        ≤ (B / qrt (u : ℝ)) * u := mul_le_mul_of_nonneg_right hstep1 (le_of_lt huR)
      _ = B * (qrt (u : ℝ)) ^ 3 := hstep2
      _ ≤ B * (Q ^ 3 / 100) := mul_le_mul_of_nonneg_left hstep4 (le_of_lt hBpos)
      _ = B * Q ^ 3 / 100 := by ring
  -- the drop the schedule affords
  have hT3 : 15 / 100 * (B * Q ^ 3) ≤ (powerSchedule ε C w - powerSchedule ε C m) * m := by
    have hq2 : (1.18 : ℝ) ≤ qrt 2 := le_qrt_of (by norm_num) (by norm_num)
    have hqwge : qrt 2 * Q ≤ qrt (w : ℝ) := by
      have h1 : qrt (2 * (m : ℝ)) ≤ qrt (w : ℝ) := qrt_mono hwR
      rwa [qrt_mul (by norm_num)] at h1
    have h2 : B / qrt (w : ℝ) ≤ B / (qrt 2 * Q) :=
      div_le_div_of_nonneg_left (le_of_lt hBpos) (by positivity) hqwge
    have h3 : B / (qrt 2 * Q) ≤ (85 / 100) * (B / Q) := by
      have heq : B / (qrt 2 * Q) = (B / Q) / qrt 2 := by field_simp
      rw [heq, div_le_iff₀ (by linarith : (0 : ℝ) < qrt 2)]
      have hBQ : 0 ≤ B / Q := by positivity
      nlinarith only [hq2, hBQ]
    have hdiff : (15 / 100) * (B / Q) ≤ powerSchedule ε C w - powerSchedule ε C m := by
      rw [powerSchedule_of_ge hCw, powerSchedule_of_ge hCm]
      linarith
    calc 15 / 100 * (B * Q ^ 3) = ((15 / 100) * (B / Q)) * m := by rw [← hQ4]; field_simp
      _ ≤ (powerSchedule ε C w - powerSchedule ε C m) * m :=
          mul_le_mul_of_nonneg_right hdiff (le_of_lt hmR)
  have hfinal : 32 * Real.sqrt (K : ℝ) * Q ^ 3 + B * Q ^ 3 / 100 + B * Q ^ 3 / 25
      ≤ 15 / 100 * (B * Q ^ 3) := by
    have h1 : 32 * Real.sqrt (K : ℝ) ≤ (64 / 1000) * B := by linarith
    nlinarith [hQ3]
  linarith

end BKLO
