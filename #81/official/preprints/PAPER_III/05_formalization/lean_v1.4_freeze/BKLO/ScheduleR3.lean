/-
# The power-law schedule, and the descent clause of the thrice-repaired interface.

The descent clause `BKLO.VortexDescentClauseR3` is a *theorem*: this file proves it, for the
explicit schedule

  `f s = 9/10 + 3ε/4 - (ε/4)·(C/max(s,C))^{1/4}`,

which is constant `= 9/10 + ε/2` up to the scale `C` (where the bottom clause needs it, see
`BKLO/BottomClause.lean`) and climbs to `9/10 + 3ε/4` as the scale grows.

The schedule has to climb, because a descent step costs a sampling error `θ ≈ (K²/m)^{1/4}` at
the scale `m` (`BKLO.descent_level_of_density`), and the deficiency `(f|W| - f|U|)|U|` of the
forced bottom set.  What makes a *power law* work — and what a schedule of bounded variation
could not do, cf. `BKLO/DescentRefutation2.lean` — is that both losses shrink with the scale at
the same rate as the drop `f(2m) - f(m) ≈ (1 - 2^{-1/4})·(ε/4)(C/m)^{1/4}` the schedule can
afford there.  The amplitude condition

  `250·√K ≤ (ε/4)·C^{1/4}`

— satisfied by taking the window `C` of the bottom clause large enough — is what makes the drop
beat the losses at every scale simultaneously.

Everything here is `sorry`-free.
-/
import BKLO.DescentStep
import BKLO.EngineR3

open Finset

namespace BKLO

/-- The fourth root. -/
noncomputable def qrt (x : ℝ) : ℝ := Real.sqrt (Real.sqrt x)

/-- **The power-law schedule.**  Constant `9/10 + ε/2` up to the scale `C`, climbing to
`9/10 + 3ε/4` like `1 - (C/s)^{1/4}` beyond it. -/
noncomputable def powerSchedule (ε : ℝ) (C : ℕ) (s : ℕ) : ℝ :=
  9 / 10 + 3 * ε / 4 - ε / 4 * (qrt (C : ℝ) / qrt ((max s C : ℕ) : ℝ))

/-! ### The fourth root -/

theorem qrt_nonneg (x : ℝ) : 0 ≤ qrt x := Real.sqrt_nonneg _

theorem qrt_pos {x : ℝ} (hx : 0 < x) : 0 < qrt x := Real.sqrt_pos.2 (Real.sqrt_pos.2 hx)

theorem qrt_mono {x y : ℝ} (h : x ≤ y) : qrt x ≤ qrt y :=
  Real.sqrt_le_sqrt (Real.sqrt_le_sqrt h)

theorem qrt_pow4 {x : ℝ} (hx : 0 ≤ x) : (qrt x) ^ 4 = x := by
  have h2 : Real.sqrt (Real.sqrt x) ^ 4 = (Real.sqrt (Real.sqrt x) ^ 2) ^ 2 := by ring
  simp only [qrt, h2, Real.sq_sqrt (Real.sqrt_nonneg x), Real.sq_sqrt hx]

theorem qrt_mul {x y : ℝ} (hx : 0 ≤ x) : qrt (x * y) = qrt x * qrt y := by
  simp only [qrt, Real.sqrt_mul hx, Real.sqrt_mul (Real.sqrt_nonneg x)]

theorem qrt_of_pow4 {a : ℝ} (ha : 0 ≤ a) : qrt (a ^ 4) = a := by
  rw [show a ^ 4 = (a * a) * (a * a) by ring, qrt_mul (by positivity)]
  simp only [qrt, Real.sqrt_mul_self ha]
  exact Real.mul_self_sqrt ha

theorem qrt_le_of {x a : ℝ} (ha : 0 ≤ a) (h : x ≤ a ^ 4) : qrt x ≤ a := by
  have h1 := qrt_mono h; rwa [qrt_of_pow4 ha] at h1

theorem le_qrt_of {x a : ℝ} (ha : 0 ≤ a) (h : a ^ 4 ≤ x) : a ≤ qrt x := by
  have h1 := qrt_mono h; rwa [qrt_of_pow4 ha] at h1

theorem qrt_sq {x : ℝ} (hx : 0 ≤ x) : qrt (x ^ 2) = Real.sqrt x := by
  rw [show x ^ 2 = x * x by ring]; simp only [qrt, Real.sqrt_mul_self hx]

theorem div_qrt {x : ℝ} (hx : 0 ≤ x) : x / qrt x = (qrt x) ^ 3 := by
  rcases eq_or_lt_of_le hx with h | h
  · simp [← h, qrt]
  · rw [div_eq_iff (ne_of_gt (qrt_pos h)), show (qrt x) ^ 3 * qrt x = (qrt x) ^ 4 by ring,
      qrt_pow4 hx]

theorem qrt_div {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y) : qrt (x / y) = qrt x / qrt y := by
  rw [eq_div_iff (ne_of_gt (qrt_pos hy)), ← qrt_mul (by positivity),
    div_mul_cancel₀ _ (ne_of_gt hy)]

/-! ### Elementary properties of the schedule -/

theorem powerSchedule_eq (ε : ℝ) (C s : ℕ) :
    powerSchedule ε C s
      = 9 / 10 + 3 * ε / 4 - (ε / 4 * qrt (C : ℝ)) / qrt ((max s C : ℕ) : ℝ) := by
  rw [powerSchedule]; ring

theorem powerSchedule_of_ge {ε : ℝ} {C s : ℕ} (hs : C ≤ s) :
    powerSchedule ε C s = 9 / 10 + 3 * ε / 4 - (ε / 4 * qrt (C : ℝ)) / qrt (s : ℝ) := by
  rw [powerSchedule_eq, max_eq_left hs]

/-- Below the window the schedule sits at the bottom of its range. -/
theorem powerSchedule_of_le {ε : ℝ} {C s : ℕ} (hC : 0 < C) (hs : s ≤ C) :
    powerSchedule ε C s = 9 / 10 + ε / 2 := by
  have hCR : (0 : ℝ) < (C : ℝ) := by exact_mod_cast hC
  have : (max s C : ℕ) = C := max_eq_right hs
  rw [powerSchedule, this]
  rw [div_self (ne_of_gt (qrt_pos hCR))]
  ring

/-- The schedule is nondecreasing. -/
theorem powerSchedule_mono {ε : ℝ} (hε : 0 ≤ ε) {C : ℕ} (hC : 0 < C) :
    Monotone (powerSchedule ε C) := by
  intro s s' hss
  have hCR : (0 : ℝ) < (C : ℝ) := by exact_mod_cast hC
  have hB : (0 : ℝ) ≤ ε / 4 * qrt (C : ℝ) := mul_nonneg (by linarith) (qrt_nonneg _)
  have hmaxs : (0 : ℝ) < ((max s C : ℕ) : ℝ) := by
    have : C ≤ max s C := Nat.le_max_right _ _
    have : (0 : ℝ) < ((max s C : ℕ) : ℝ) := by
      have h : 0 < max s C := lt_of_lt_of_le hC this
      exact_mod_cast h
    exact this
  have hle : qrt ((max s C : ℕ) : ℝ) ≤ qrt ((max s' C : ℕ) : ℝ) := by
    apply qrt_mono
    have : max s C ≤ max s' C := max_le_max hss le_rfl
    exact_mod_cast this
  have := div_le_div_of_nonneg_left hB (qrt_pos hmaxs) hle
  rw [powerSchedule_eq, powerSchedule_eq]
  linarith

/-- The schedule stays in the lower three quarters of the window. -/
theorem powerSchedule_window {ε : ℝ} (hε : 0 < ε) {C : ℕ} (hC : 0 < C) (s : ℕ) :
    9 / 10 + ε / 2 ≤ powerSchedule ε C s ∧ powerSchedule ε C s ≤ 9 / 10 + 3 * ε / 4 := by
  have hCR : (0 : ℝ) < (C : ℝ) := by exact_mod_cast hC
  have hqC : 0 < qrt (C : ℝ) := qrt_pos hCR
  have hB : (0 : ℝ) ≤ ε / 4 * qrt (C : ℝ) := mul_nonneg (by linarith) (qrt_nonneg _)
  have hmax : (C : ℝ) ≤ ((max s C : ℕ) : ℝ) := by exact_mod_cast Nat.le_max_right s C
  have hqmax : qrt (C : ℝ) ≤ qrt ((max s C : ℕ) : ℝ) := qrt_mono hmax
  have hqmaxpos : 0 < qrt ((max s C : ℕ) : ℝ) := lt_of_lt_of_le hqC hqmax
  have hdiv : (ε / 4 * qrt (C : ℝ)) / qrt ((max s C : ℕ) : ℝ) ≤ ε / 4 := by
    rw [div_le_iff₀ hqmaxpos]
    exact mul_le_mul_of_nonneg_left hqmax (by linarith)
  have hnn : (0 : ℝ) ≤ (ε / 4 * qrt (C : ℝ)) / qrt ((max s C : ℕ) : ℝ) :=
    div_nonneg hB (qrt_nonneg _)
  rw [powerSchedule_eq]
  constructor <;> linarith

/-- **The slack of the power-law schedule.**  At every scale `m ≥ C`, with a level `w ≥ 2m` above
it and a bottom set `u ≤ m/K` below it, the drop of the schedule between the scales `w` and `m`
pays for the sampling error of one descent step *and* for the deficiency of the bottom set.  This
is the whole arithmetic content of the descent clause. -/
theorem powerSchedule_slack {ε : ℝ} (hε : 0 < ε) {C K u m w : ℕ}
    (hK : 800 ≤ K) (hC : 0 < C) (hCm : C ≤ m) (hu : 0 < u) (hKu : K * u ≤ m) (h2m : 2 * m ≤ w)
    (hB : 250 * Real.sqrt (K : ℝ) ≤ ε / 4 * qrt (C : ℝ)) :
    qrt (10 ^ 6 * (K : ℝ) ^ 2) / qrt (m : ℝ) * m
        + (powerSchedule ε C w - powerSchedule ε C u) * u
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
      linarith
    have hstep2 : B / qrt (u : ℝ) * u = B * (qrt (u : ℝ)) ^ 3 := by
      rw [show B / qrt (u : ℝ) * u = B * ((u : ℝ) / qrt (u : ℝ)) by ring,
        div_qrt (le_of_lt huR)]
    have hstep3 : qrt (u : ℝ) ≤ Q / qrt (K : ℝ) := by
      have hKpos : (0 : ℝ) < (K : ℝ) := by linarith
      have h1 : (u : ℝ) ≤ (m : ℝ) / (K : ℝ) := by
        rw [le_div_iff₀ hKpos]
        have : ((K * u : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hKu
        push_cast at this; linarith
      calc qrt (u : ℝ) ≤ qrt ((m : ℝ) / (K : ℝ)) := qrt_mono h1
        _ = Q / qrt (K : ℝ) := qrt_div (le_of_lt hmR) hKpos
    have hstep4 : (qrt (u : ℝ)) ^ 3 ≤ Q ^ 3 / 100 := by
      have h1 : (qrt (u : ℝ)) ^ 3 ≤ (Q / qrt (K : ℝ)) ^ 3 := pow_le_pow_left₀ (le_of_lt hqu) hstep3 3
      have h2 : (Q / qrt (K : ℝ)) ^ 3 = Q ^ 3 / (qrt (K : ℝ)) ^ 3 := by rw [div_pow]
      have h3 : Q ^ 3 / (qrt (K : ℝ)) ^ 3 ≤ Q ^ 3 / 100 :=
        div_le_div_of_nonneg_left hQ3 (by norm_num) hqK
      linarith
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
      nlinarith
    have hdiff : (15 / 100) * (B / Q) ≤ powerSchedule ε C w - powerSchedule ε C m := by
      rw [powerSchedule_of_ge hCw, powerSchedule_of_ge hCm]
      linarith
    calc 15 / 100 * (B * Q ^ 3) = ((15 / 100) * (B / Q)) * m := by rw [← hQ4]; field_simp
      _ ≤ (powerSchedule ε C w - powerSchedule ε C m) * m :=
          mul_le_mul_of_nonneg_right hdiff (le_of_lt hmR)
  have hfinal : 32 * Real.sqrt (K : ℝ) * Q ^ 3 + B * Q ^ 3 / 100 ≤ 15 / 100 * (B * Q ^ 3) := by
    have h1 : 32 * Real.sqrt (K : ℝ) ≤ (14 / 100) * B := by linarith
    nlinarith [hQ3]
  linarith

/-! ### The descent clause -/

set_option maxHeartbeats 1000000 in
/-- **The descent clause of the thrice-repaired interface is a theorem.**

For the power-law schedule with window `C` and amplitude `ε/4`, provided the amplitude condition
`250√K ≤ (ε/4)C^{1/4}` holds and the bottom scale `n₂` is at least `C/K`, every configuration the
clause quantifies over has an admissible level.  The level is the random one of
`BKLO.descent_level_of_density`; the whole content here is that the schedule has, at every scale,
the slack that step consumes. -/
theorem vortexDescentClauseR3_of_powerSchedule {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 100)
    {n₂ C K : ℕ} (hK : 800 ≤ K) (hn₂ : 0 < n₂) (hCn₂ : C ≤ K * n₂)
    (hB : 250 * Real.sqrt (K : ℝ) ≤ ε / 4 * qrt (C : ℝ)) :
    VortexDescentClauseR3 (powerSchedule ε C) n₂ K := by
  classical
  have hKR : (800 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hKpos : (0 : ℝ) < (K : ℝ) := by linarith
  have hsK2 : Real.sqrt (K : ℝ) ^ 2 = (K : ℝ) := Real.sq_sqrt (le_of_lt hKpos)
  have hsK1 : (1 : ℝ) ≤ Real.sqrt (K : ℝ) := by
    nlinarith only [Real.sqrt_nonneg (K : ℝ), hsK2, hKR]
  have hqC : 1000 * Real.sqrt (K : ℝ) ≤ qrt (C : ℝ) := by
    have h0 : (0 : ℝ) ≤ qrt (C : ℝ) := qrt_nonneg _
    nlinarith only [hB, hε, hε', h0, Real.sqrt_nonneg (K : ℝ)]
  have hCge : (10 : ℝ) ^ 12 * (K : ℝ) ^ 2 ≤ (C : ℝ) := by
    have h := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 1000 * Real.sqrt (K : ℝ)) hqC 4
    rw [qrt_pow4 (by positivity)] at h
    have hpow : (1000 * Real.sqrt (K : ℝ)) ^ 4 = (10 : ℝ) ^ 12 * (K : ℝ) ^ 2 := by
      rw [mul_pow, show Real.sqrt (K : ℝ) ^ 4 = (Real.sqrt (K : ℝ) ^ 2) ^ 2 by ring, hsK2]
      norm_num
    linarith only [hpow ▸ h]
  have hCposR : (0 : ℝ) < (C : ℝ) := lt_of_lt_of_le (by nlinarith only [hKR]) hCge
  have hCpos : 0 < C := by exact_mod_cast hCposR
  intro V _ W U D E m a hU hUW hUD hKU hKD hpool hWK hfa ha1 hE hdeg hbot
  -- basic sizes
  have hupos : 0 < U.card := lt_of_lt_of_le hn₂ hU
  have huR : (0 : ℝ) < (U.card : ℝ) := by exact_mod_cast hupos
  have hCm : C ≤ m := by
    calc C ≤ K * n₂ := hCn₂
      _ ≤ K * U.card := Nat.mul_le_mul_left _ hU
      _ ≤ m := hKU
  have hmpos : 0 < m := lt_of_lt_of_le hCpos hCm
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hmpos
  have h2mW : 2 * m ≤ W.card := le_trans (Nat.le_add_right _ _) hpool
  have hUWc : U.card ≤ W.card := Finset.card_le_card hUW
  -- the schedule at the three scales
  set fW : ℝ := powerSchedule ε C W.card with hfWdef
  set fU : ℝ := powerSchedule ε C U.card with hfUdef
  set fm : ℝ := powerSchedule ε C m with hfmdef
  have hmono := powerSchedule_mono (le_of_lt hε) hCpos
  have hfUW : fU ≤ fW := hmono hUWc
  have hfW0 : (0 : ℝ) ≤ fW := by
    have := (powerSchedule_window hε hCpos W.card).1
    linarith
  have ha0 : (0 : ℝ) ≤ a := le_trans hfW0 hfa
  -- the avoidance set, cut down to `W`
  set D' : Finset V := D ∩ W with hD'def
  have hD'W : D' ⊆ W := Finset.inter_subset_right
  have hUD' : Disjoint U D' := hUD.mono_right Finset.inter_subset_left
  have hD'card : D'.card ≤ D.card := Finset.card_le_card Finset.inter_subset_left
  have hsdiff : W \ D' = W \ D := by
    ext x; simp only [Finset.mem_sdiff, hD'def, Finset.mem_inter]; tauto
  -- the sampling error
  set θ : ℝ := qrt (10 ^ 6 * (K : ℝ) ^ 2) / qrt (m : ℝ) with hθdef
  have hq6 : (0 : ℝ) < qrt (10 ^ 6 * (K : ℝ) ^ 2) := qrt_pos (by positivity)
  have hqm : (0 : ℝ) < qrt (m : ℝ) := qrt_pos hmR
  have hθ0 : 0 < θ := div_pos hq6 hqm
  have hθ4 : θ ^ 4 * (m : ℝ) = 10 ^ 6 * (K : ℝ) ^ 2 := by
    rw [hθdef, div_pow, qrt_pow4 (by positivity), qrt_pow4 (le_of_lt hmR)]
    field_simp
  have hθ1 : θ ≤ 1 := by
    have hmge : (10 : ℝ) ^ 12 * (K : ℝ) ^ 2 ≤ (m : ℝ) := by
      have : (C : ℝ) ≤ (m : ℝ) := by exact_mod_cast hCm
      linarith
    have h4 : θ ^ 4 ≤ 1 := by
      have : θ ^ 4 * (m : ℝ) ≤ 1 * (m : ℝ) := by
        rw [hθ4, one_mul]; linarith only [hmge, sq_nonneg ((K : ℝ))]
      exact le_of_mul_le_mul_right this hmR
    nlinarith [pow_nonneg (le_of_lt hθ0) 2, sq_nonneg (θ ^ 2 - 1), sq_nonneg (θ - 1),
      sq_nonneg (θ + 1)]
  -- the target density of the new level
  set g : ℝ := fm + ((a - fW) * ((m : ℝ) - (U.card : ℝ)) - (D.card : ℝ)) / (m : ℝ) with hgdef
  have hgm : g * (m : ℝ) = fm * (m : ℝ) + (a - fW) * ((m : ℝ) - (U.card : ℝ)) - (D.card : ℝ) := by
    rw [hgdef]; field_simp; ring
  -- the slack of the schedule
  have hslack :
      θ * (m : ℝ) + (fW - fU) * (U.card : ℝ) ≤ (fW - fm) * (m : ℝ) := by
    have h := powerSchedule_slack (ε := ε) hε (C := C) (K := K) (u := U.card) (m := m)
      (w := W.card) hK hCpos hCm hupos hKU h2mW hB
    have hmul : qrt (10 ^ 6 * (K : ℝ) ^ 2) / qrt (m : ℝ) * (m : ℝ)
        + (fW - fU) * (U.card : ℝ) ≤ (fW - fm) * (m : ℝ) := by
      have e1 : powerSchedule ε C W.card - powerSchedule ε C U.card = fW - fU := rfl
      have e2 : powerSchedule ε C W.card - powerSchedule ε C m = fW - fm := rfl
      rw [e1, e2] at h
      exact h
    exact hmul
  -- the descent step
  obtain ⟨W', hUW', hW'W, hW'D', hW'card, hstrong, hweak⟩ :=
    descent_level_of_density (W := W) (U := U) (D := D') (E := E) (m := m)
      (fW := a) (fU := fU) (fm := g) (θ := θ) (Kr := (K : ℝ) ^ 2)
      hUW hD'W hUD'
      (by have h8 : 800 * U.card ≤ K * U.card := Nat.mul_le_mul_right _ hK; omega)
      (by omega) (by rw [sq]; exact_mod_cast hWK)
      ha0 ha1 (le_trans hfUW hfa) hθ0 hθ1 (by nlinarith only [hKR]) (by rw [hθ4]) hE hdeg
      (by rw [hsdiff]; exact hbot)
      (by
        have hDR : (0 : ℝ) ≤ (D.card : ℝ) - (D'.card : ℝ) := by
          have : (D'.card : ℝ) ≤ (D.card : ℝ) := by exact_mod_cast hD'card
          linarith
        have hD'0 : (0 : ℝ) ≤ (D'.card : ℝ) := Nat.cast_nonneg _
        rw [hgm]
        nlinarith)
  have hW'D : Disjoint W' D := by
    rw [Finset.disjoint_left]
    intro x hx hxD
    exact (Finset.disjoint_left.1 hW'D') hx (Finset.mem_inter.2 ⟨hxD, hW'W hx⟩)
  refine ⟨W', hUW', hW'W, hW'D, hW'card, ?_, ?_⟩
  · intro v hv
    have := hstrong v (by rw [hsdiff]; exact hv)
    rw [hgm] at this
    exact this
  · intro v hv
    have h := hweak v hv
    rw [hgm] at h
    -- `(a - fW)(m - |U|) ≥ 0`, `|D| ≤ m/K` and `a|U| ≤ |U| ≤ m/K`
    have hKU' : ((K : ℝ)) * (U.card : ℝ) ≤ (m : ℝ) := by exact_mod_cast hKU
    have hKD' : ((K : ℝ)) * (D.card : ℝ) ≤ (m : ℝ) := by exact_mod_cast hKD
    have humle : (U.card : ℝ) ≤ (m : ℝ) := by nlinarith only [hKU', hKR, huR]
    have hsurp : (0 : ℝ) ≤ (a - fW) * ((m : ℝ) - (U.card : ℝ)) :=
      mul_nonneg (by linarith) (by linarith)
    have hd : (D.card : ℝ) ≤ (m : ℝ) / (K : ℝ) := by
      rw [le_div_iff₀ hKpos]; linarith
    have hau : a * (U.card : ℝ) ≤ (m : ℝ) / (K : ℝ) := by
      rw [le_div_iff₀ hKpos]
      nlinarith only [ha1, ha0, hKU', huR, hKpos]
    have : (fm - 2 / (K : ℝ)) * (m : ℝ) ≤ g * (m : ℝ) - a * (U.card : ℝ) := by
      rw [hgm]
      have h2K : (2 : ℝ) / (K : ℝ) * (m : ℝ) = 2 * ((m : ℝ) / (K : ℝ)) := by field_simp
      linarith only [h2K, hd, hau, hsurp]
    linarith

end BKLO
