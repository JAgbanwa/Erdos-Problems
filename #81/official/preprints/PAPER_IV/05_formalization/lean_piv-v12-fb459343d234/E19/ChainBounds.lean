import E18.NibbleChain
import E19.ScheduleBounds

/-!
# E19 — numerical bounds for the round-oracle and nibble-chain constants at `r = 7`, `β₀`

Continuing `E19.ScheduleBounds`, with `Zc = 3·A0 + 220 + B0` and `W = Ybig + Zc + 8`:

* `D0T 7 β₀ ≤ 2^(A0+146)`, `2^(-(Ybig+3A0+220)) ≤ c0T 7 β₀`;
* `2^(-(Ybig+Zc)) ≤ muT 7 β₀`, `d0T 7 β₀ ≤ 2^(A0+146+B0)`;
* `DS 7 β₀ ≤ 2^W`, `2^(-W) ≤ gamW 7 β₀`, `2^(-W) ≤ gamR 6 β₀`.
-/

namespace E19.Sched

open E18.Nib

/-- The small additive part of the exponent of `1/muT`, `Zc = 3·A0 + 220 + B0`. -/
irreducible_def Zc : ℕ := 3 * A0 + 220 + B0

/-- The exponent `W = Ybig + Zc + 8` of the nibble-chain codegree constant: `2^(-W) ≤ gamR 6 β₀`. -/
irreducible_def Wexp : ℕ := Ybig + Zc + 8

theorem betaN_beta0 : betaN beta0 = beta0 := by
  unfold betaN; exact min_eq_left beta0_le_half

theorem half_beta0_sq : (beta0 / 2) ^ 2 = 1 / (128 * 10 ^ 18) ^ 2 := by
  norm_num [beta0]

theorem half_beta0_sq_ge : ((2 : ℝ) ^ 134)⁻¹ ≤ (beta0 / 2) ^ 2 := by
  rw [half_beta0_sq]; norm_num

/-- **`D0T 7 β₀ ≤ 2^(A0+146)`**. -/
theorem D0T_le : D0T 7 beta0 ≤ 2 ^ (A0 + 146) := by
  unfold D0T
  rw [half_beta0_sq, epsT_eq]
  set g := gamT 7 beta0 with hgdef
  set N : ℝ := 2 ^ A0 with hNdef
  have hg := gamT_pos
  have hNg := one_le_N_mul_gamT
  rw [← hgdef, ← hNdef] at hNg
  rw [← hgdef] at hg
  have hN1 : (1 : ℝ) ≤ N := one_le_two_pow A0
  have h1 : 256 * ((7 : ℕ) : ℝ) / (1 / (128 * 10 ^ 18) ^ 2 * g)
      ≤ 256 * 7 * (128 * 10 ^ 18) ^ 2 * N := by
    rw [div_le_iff₀ (by positivity)]; push_cast; nlinarith
  have h2 : 96 / (24 / 7 * g) ≤ 28 * N := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have h3 : (2 : ℝ) ^ (A0 + 146) = 2 ^ 146 * N := by rw [pow_add, hNdef, mul_comm]
  rw [h3]
  have h4 : (256 * 7 * (128 * 10 ^ 18) ^ 2 + 28 + 4 : ℝ) ≤ 2 ^ 146 := by norm_num
  nlinarith

theorem D0T_pos : 0 < D0T 7 beta0 := by
  unfold D0T; have := gamT_pos; have := epsT_pos; have := beta0_pos; positivity

/-- **`2^(-(Ybig + 3 A0 + 220)) ≤ c0T 7 β₀`**. -/
theorem c0T_ge : ((2 : ℝ) ^ (Ybig + 3 * A0 + 220))⁻¹ ≤ c0T 7 beta0 := by
  unfold c0T
  have hc : ((2 : ℝ) ^ 17)⁻¹ ≤ (16384 * ((7 : ℕ) : ℝ))⁻¹ := by norm_num
  have e := lb_mul (lb_mul (lb_mul (lb_mul excT_ge (lb_mul epsT_ge epsT_ge)) gamT_ge)
    half_beta0_sq_ge) hc
  have hexp : Ybig + 69 + (A0 + A0) + A0 + 134 + 17 = Ybig + 3 * A0 + 220 := by ring
  rw [hexp] at e
  rw [div_eq_mul_inv, sq (epsT 7 beta0)]
  exact e

theorem c0T_pos : 0 < c0T 7 beta0 := lt_of_lt_of_le (by positivity) c0T_ge

/-- **`2^(-(Ybig + Zc)) ≤ muT 7 β₀`**. -/
theorem muT_ge : ((2 : ℝ) ^ (Ybig + Zc))⁻¹ ≤ muT 7 beta0 := by
  unfold muT
  have hA : A0 ≤ Ybig + Zc := by rw [Zc_def]; omega
  refine le_min ?_ (le_min ?_ (le_min ?_ ?_))
  · apply lb_mono hA
    have := gamT_ge; have := gamT_pos; linarith
  · have := lb_mul c0T_ge lominT_ge
    rw [show Ybig + 3 * A0 + 220 + B0 = Ybig + Zc by rw [Zc_def]; ring] at this
    exact this
  · have hD := D0T_le
    have hle : 2 * (D0T 7 beta0 + 1) ≤ (2 : ℝ) ^ (A0 + 148) := by
      have : (2 : ℝ) ^ (A0 + 148) = 4 * 2 ^ (A0 + 146) := by
        rw [show A0 + 148 = (A0 + 146) + 2 by ring, pow_add]; ring
      have := one_le_two_pow (A0 + 146)
      linarith
    have h := lb_of_ub_inv (by have := D0T_pos; positivity) hle
    rw [one_div]
    exact lb_mono (by rw [Zc_def]; omega) h
  · have : ((2 : ℝ) ^ (Ybig + Zc))⁻¹ ≤ ((2 : ℝ) ^ 1)⁻¹ :=
      inv_anti₀ (by positivity) (pow_le_pow_right₀ (by norm_num) (by rw [Zc_def]; omega))
    simpa using this

theorem muT_pos : 0 < muT 7 beta0 := lt_of_lt_of_le (by positivity) muT_ge

/-- **`d0T 7 β₀ ≤ 2^(A0 + 146 + B0)`**. -/
theorem d0T_le : d0T 7 beta0 ≤ 2 ^ (A0 + 146 + B0) := by
  unfold d0T
  apply max_le (one_le_two_pow _)
  rw [div_eq_mul_inv, pow_add]
  exact mul_le_mul D0T_le (inv_le_of_lb lominT_ge) (by have := lominT_pos; positivity)
    (by positivity)

theorem kS_seven : (kS 7 : ℝ) = 50 := by norm_num [kS]

/-- **`DS 7 β₀ ≤ 2^W`**, `W = Ybig + Zc + 8`. -/
theorem DS_le : (DS 7 beta0 : ℝ) ≤ 2 ^ Wexp := by
  unfold DS muN d0N
  rw [betaN_beta0]
  push_cast
  rw [kS_seven]
  have hmu := muT_pos
  have hd := d0T_le
  have hc1 : (⌈d0T 7 beta0⌉₊ : ℝ) < d0T 7 beta0 + 1 :=
    Nat.ceil_lt_add_one (le_trans zero_le_one (le_max_left _ _))
  have hc2 : (⌈4 * 50 / muT 7 beta0⌉₊ : ℝ) < 4 * 50 / muT 7 beta0 + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hinv : (muT 7 beta0)⁻¹ ≤ 2 ^ (Ybig + Zc) := inv_le_of_lb muT_ge
  have hd' : d0T 7 beta0 ≤ 2 ^ (Ybig + Zc) := ub_mono (by rw [Zc_def]; omega) hd
  have hW : (2 : ℝ) ^ Wexp = 256 * 2 ^ (Ybig + Zc) := by
    rw [Wexp_def, pow_add]; norm_num; ring
  rw [hW]
  have h1 := one_le_two_pow (Ybig + Zc)
  have h200 : 4 * 50 / muT 7 beta0 ≤ 200 * 2 ^ (Ybig + Zc) := by
    rw [div_eq_mul_inv]; linarith
  have := max_le_iff.2 ⟨hc1.le.trans (by linarith : d0T 7 beta0 + 1 ≤ 200 * 2 ^ (Ybig + Zc) + 1),
    hc2.le.trans (by linarith : 4 * 50 / muT 7 beta0 + 1 ≤ 200 * 2 ^ (Ybig + Zc) + 1)⟩
  linarith

theorem DS_pos : (0 : ℝ) < DS 7 beta0 := by
  unfold DS; positivity

/-- **`2^(-W) ≤ gamW 7 β₀`**. -/
theorem gamW_ge : ((2 : ℝ) ^ Wexp)⁻¹ ≤ gamW 7 beta0 := by
  unfold gamW
  apply le_min
  · rw [one_div]; exact lb_of_ub_inv DS_pos DS_le
  · unfold muN; rw [betaN_beta0]
    have h := muT_ge
    have : ((2 : ℝ) ^ Wexp)⁻¹ ≤ ((2 : ℝ) ^ (Ybig + Zc))⁻¹ / 4 := by
      rw [Wexp_def, show Ybig + Zc + 8 = (Ybig + Zc) + 8 by ring, pow_add, mul_inv]
      have : (0 : ℝ) < ((2 : ℝ) ^ (Ybig + Zc))⁻¹ := by positivity
      norm_num
      nlinarith
    linarith

/-- **`2^(-W) ≤ gamR 6 β₀`**. -/
theorem gamR_ge : ((2 : ℝ) ^ Wexp)⁻¹ ≤ gamR 6 beta0 := by
  unfold gamR
  apply le_min gamW_ge
  exact inv_le_one_of_one_le₀ (one_le_two_pow _)

theorem gamR_pos : 0 < gamR 6 beta0 := lt_of_lt_of_le (by positivity) gamR_ge

theorem gamR_le_one : gamR 6 beta0 ≤ 1 := min_le_right _ _

end E19.Sched
