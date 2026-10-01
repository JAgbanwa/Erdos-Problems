import E34.Main
import E19.Tower

/-!
# E35 — the edit threshold `NeditE s δ_s` is below a tower of linear height

At `δ_s = ε_s⁴/(2¹⁹(s+1))`, `ε_s = 1/(10⁴¹(s+1)⁸)`, we have `1/δ_s ≤ R = 2^E`,
`E = Eedit s = 564 + 33(s+1)`.  Unfolding `mVq`, `mV`, `qV`, `sV`, `ellV`, `MV`:

* `mV d ≤ R^470` whenever `0 < d`, `1/d ≤ R`, `2^200 ≤ R` (`mV_le_pow`);
* hence `mVq δ_s ≤ 2^Yedit s`, `Yedit s = 470·Eedit s`;
* **`NeditE_le`**: `NeditE s δ_s ≤ 2^(2^(3·Yedit s))`, and `≤ tower2 (3·Yedit s + 2)`.
-/

namespace E35

open E34 E19

/-- Exponent of `1/δ_s ≤ 2^Eedit s`. -/
def Eedit (s : ℕ) : ℕ := 564 + 33 * (s + 1)
/-- Exponent of `mVq δ_s ≤ 2^Yedit s`. -/
def Yedit (s : ℕ) : ℕ := 470 * Eedit s

/-- The precision `δ_s = ε_s⁴/(2¹⁹(s+1))` at which `NeditE` is evaluated. -/
noncomputable def deltaS (s : ℕ) : ℚ :=
  A4S1.IndepAll.epsS s ^ 4 / (2 ^ 19 * ((s : ℚ) + 1))

theorem pow_le_R {R a b : ℕ} (hR : 1 ≤ R) (h : a ≤ b) : R ^ a ≤ R ^ b :=
  Nat.pow_le_pow_right hR h

/-- `mV d ≤ R^470` when `0 < d`, `d⁻¹ ≤ R` and `2^200 ≤ R`. -/
theorem mV_le_pow {d : ℝ} {R : ℕ} (hd : 0 < d) (hR : d⁻¹ ≤ R) (hR2 : 2 ^ 200 ≤ R) :
    mV d ≤ R ^ 470 := by
  have hR1 : 1 ≤ R := le_trans Nat.one_le_two_pow hR2
  have hRr : (0 : ℝ) < R := by exact_mod_cast hR1
  -- `sV`
  have hs : sV d ≤ R ^ 3 := by
    have h1 : sV d ≤ 102400 * R ^ 2 := by
      unfold sV
      apply Nat.ceil_le.2
      push_cast
      have : (102400 : ℝ) / d ^ 2 = 102400 * (d⁻¹) ^ 2 := by field_simp
      rw [this]
      have := pow_le_pow_left₀ (inv_pos.2 hd).le hR 2
      linarith
    have h2 : 102400 * R ^ 2 ≤ R * R ^ 2 :=
      Nat.mul_le_mul_right _ (le_trans (by norm_num) hR2)
    calc sV d ≤ R * R ^ 2 := h1.trans h2
      _ = R ^ 3 := by ring
  have hq : qV d ≤ R ^ 6 := by
    unfold qV
    calc sV d ^ 2 ≤ (R ^ 3) ^ 2 := Nat.pow_le_pow_left hs 2
      _ = R ^ 6 := by ring
  set q := qV d with hqdef
  -- `kMax`
  have hk : kMax q + 1 ≤ R ^ 26 := by
    unfold kMax
    have h1 : (4 * q ^ 2 + 1) ^ 2 + 1 ≤ (6 * q ^ 2 + 2) ^ 2 := by nlinarith
    have h2 : 6 * q ^ 2 + 2 ≤ 8 * R ^ 12 := by
      have : q ^ 2 ≤ (R ^ 6) ^ 2 := Nat.pow_le_pow_left hq 2
      have h' : (R ^ 6) ^ 2 = R ^ 12 := by ring
      have : 1 ≤ R ^ 12 := Nat.one_le_pow _ _ hR1
      omega
    have h3 : 8 * R ^ 12 ≤ R * R ^ 12 := Nat.mul_le_mul_right _ (le_trans (by norm_num) hR2)
    calc (4 * q ^ 2 + 1) ^ 2 + 1 ≤ (6 * q ^ 2 + 2) ^ 2 := h1
      _ ≤ (R * R ^ 12) ^ 2 := Nat.pow_le_pow_left (h2.trans h3) 2
      _ = R ^ 26 := by ring
  -- `ellV`
  have hl : ellV q ≤ R ^ 53 := by
    refine (ellV_le q).trans ?_
    calc 4 * (kMax q + 1) ^ 2 ≤ R * (R ^ 26) ^ 2 :=
          Nat.mul_le_mul (le_trans (by norm_num) hR2) (Nat.pow_le_pow_left hk 2)
      _ = R ^ 53 := by ring
  -- `MV`
  have hM : MV d q ≤ R ^ 416 := by
    have h1 := MV_le hd q
    have hkR : ((kMax q : ℝ) + 1) ≤ (R : ℝ) ^ 26 := by exact_mod_cast hk
    have hk15 : ((kMax q : ℝ) + 1) ^ 15 ≤ ((R : ℝ) ^ 26) ^ 15 :=
      pow_le_pow_left₀ (by positivity) hkR 15
    have hd24 : 1 / d ^ 24 ≤ (R : ℝ) ^ 24 := by
      rw [one_div, ← inv_pow]; exact pow_le_pow_left₀ (inv_pos.2 hd).le hR 24
    have h166' : 2 ^ 166 ≤ R := le_trans (Nat.pow_le_pow_right (by norm_num) (by norm_num)) hR2
    have h166 : (2 : ℝ) ^ 166 ≤ R := by exact_mod_cast h166'
    have h2 : (2 : ℝ) ^ 166 * ((kMax q : ℝ) + 1) ^ 15 / d ^ 24 + 1 ≤ (R : ℝ) ^ 416 := by
      have e : (2 : ℝ) ^ 166 * ((kMax q : ℝ) + 1) ^ 15 / d ^ 24
          = 2 ^ 166 * ((kMax q : ℝ) + 1) ^ 15 * (1 / d ^ 24) := by ring
      rw [e]
      have a1 : (2 : ℝ) ^ 166 * ((kMax q : ℝ) + 1) ^ 15 * (1 / d ^ 24)
          ≤ R * ((R : ℝ) ^ 26) ^ 15 * (R : ℝ) ^ 24 := by gcongr
      have a2 : (R : ℝ) * ((R : ℝ) ^ 26) ^ 15 * (R : ℝ) ^ 24 = (R : ℝ) ^ 415 := by ring
      have a3 : (R : ℝ) ^ 415 + 1 ≤ (R : ℝ) ^ 416 := by
        have hR1' : (1 : ℝ) ≤ R := by exact_mod_cast hR1
        have hR2' : (2 : ℝ) ≤ R := le_trans (by norm_num) h166
        have : (1 : ℝ) ≤ (R : ℝ) ^ 415 := one_le_pow₀ hR1'
        have e2 : (R : ℝ) ^ 416 = R * R ^ 415 := by ring
        nlinarith
      linarith
    exact_mod_cast h1.trans h2
  -- `mV`
  unfold mV
  rw [← hqdef]
  have h1 : MV d q * ellV q ≤ R ^ 416 * R ^ 53 := Nat.mul_le_mul hM hl
  have h2 : 2 * q ≤ 2 * R ^ 6 := by omega
  have h3 : 2 * R ^ 6 + R ^ 416 * R ^ 53 ≤ R ^ 470 := by
    have e1 : R ^ 416 * R ^ 53 = R ^ 469 := by ring
    have e2 : R ^ 470 = R * R ^ 469 := by ring
    have : R ^ 6 ≤ R ^ 469 := pow_le_R hR1 (by norm_num)
    have : 3 * R ^ 469 ≤ R * R ^ 469 := Nat.mul_le_mul_right _ (le_trans (by norm_num) hR2)
    omega
  omega

theorem deltaS_pos (s : ℕ) : 0 < deltaS s := by
  unfold deltaS A4S1.IndepAll.epsS; positivity

theorem deltaS_inv (s : ℕ) :
    ((deltaS s : ℚ) : ℝ)⁻¹ = 2 ^ 19 * 10 ^ 164 * ((s : ℝ) + 1) ^ 33 := by
  unfold deltaS A4S1.IndepAll.epsS
  push_cast
  field_simp

set_option exponentiation.threshold 600 in
theorem deltaS_inv_le (s : ℕ) : ((deltaS s : ℚ) : ℝ)⁻¹ ≤ ((2 ^ Eedit s : ℕ) : ℝ) := by
  rw [deltaS_inv]
  have h1 : (s : ℝ) + 1 ≤ 2 ^ (s + 1) := by
    have : ((s + 1 : ℕ) : ℝ) ≤ ((2 ^ (s + 1) : ℕ) : ℝ) := by
      exact_mod_cast (Nat.lt_two_pow_self).le
    push_cast at this; exact this
  have h2 : ((s : ℝ) + 1) ^ 33 ≤ ((2 : ℝ) ^ (s + 1)) ^ 33 :=
    pow_le_pow_left₀ (by positivity) h1 33
  have h3 : (2 : ℝ) ^ 19 * 10 ^ 164 ≤ 2 ^ 564 := by norm_num
  have e : (2 : ℝ) ^ (564 + 33 * (s + 1)) = 2 ^ 564 * ((2 : ℝ) ^ (s + 1)) ^ 33 := by
    rw [pow_add, ← pow_mul, mul_comm 33 (s + 1)]
  push_cast
  rw [Eedit, e]
  exact mul_le_mul h3 h2 (by positivity) (by positivity)

/-- **`mVq δ_s ≤ 2^Yedit s`.** -/
theorem mVq_deltaS_le (s : ℕ) : mVq (deltaS s) ≤ 2 ^ Yedit s := by
  unfold mVq
  have hd : (0 : ℝ) < ((deltaS s : ℚ) : ℝ) := by exact_mod_cast deltaS_pos s
  have h := mV_le_pow hd (deltaS_inv_le s)
    (Nat.pow_le_pow_right (by norm_num) (by unfold Eedit; omega))
  rw [← pow_mul] at h
  unfold Yedit
  rw [mul_comm]
  exact h

theorem Yedit_ge (s : ℕ) : s + 5 ≤ Yedit s := by unfold Yedit Eedit; omega

/-- The arithmetic core: `max m (max m (8 s m^(m+1) + 1)) ≤ 2^(2^(3Y))` when `1 ≤ m ≤ 2^Y`
and `s + 5 ≤ Y`. -/
theorem edit_arith (s m Y : ℕ) (hm1' : 1 ≤ m) (hmY : m ≤ 2 ^ Y) (hYs : s + 5 ≤ Y) :
    max m (max m (8 * s * m ^ (m + 1) + 1)) ≤ 2 ^ (2 ^ (3 * Y)) := by
  have hY2 : Y ≤ 2 ^ Y := (Nat.lt_two_pow_self).le
  have hs2 : s + 4 ≤ 2 ^ (s + 4) := (Nat.lt_two_pow_self).le
  have hm1 : m + 1 ≤ 2 ^ (Y + 1) := by rw [pow_succ]; have := Nat.one_le_two_pow (n := Y); omega
  have hexp : Y * (m + 1) ≤ 2 ^ (2 * Y + 1) := by
    calc Y * (m + 1) ≤ 2 ^ Y * 2 ^ (Y + 1) := Nat.mul_le_mul hY2 hm1
      _ = 2 ^ (2 * Y + 1) := by rw [← pow_add]; ring_nf
  have hpow : m ^ (m + 1) ≤ 2 ^ (2 ^ (2 * Y + 1)) :=
    calc m ^ (m + 1) ≤ (2 ^ Y) ^ (m + 1) := Nat.pow_le_pow_left hmY _
      _ = 2 ^ (Y * (m + 1)) := by rw [← pow_mul]
      _ ≤ _ := Nat.pow_le_pow_right (by norm_num) hexp
  have h8 : 8 * s + 1 ≤ 2 ^ (s + 4) := by
    rw [pow_add]; norm_num
    have := Nat.lt_two_pow_self (n := s); omega
  generalize hP : 2 ^ (2 * Y + 1) = P at hpow
  have hP1 : 1 ≤ P := by rw [← hP]; exact Nat.one_le_two_pow
  have hterm : 8 * s * m ^ (m + 1) + 1 ≤ 2 ^ (s + 4 + P) := by
    rw [pow_add (2 : ℕ) (s + 4) P]
    have hq1 : 1 ≤ m ^ (m + 1) := Nat.one_le_pow _ _ (by omega)
    generalize m ^ (m + 1) = M at hq1 hpow ⊢
    calc 8 * s * M + 1 ≤ (8 * s + 1) * M := by nlinarith
      _ ≤ 2 ^ (s + 4) * 2 ^ P := Nat.mul_le_mul h8 hpow
  have hexp2 : s + 4 + P ≤ 2 ^ (3 * Y) := by
    have e : 2 ^ (3 * Y) = 2 ^ (2 * Y + 1) * 2 ^ (Y - 1) := by
      rw [← pow_add]; congr 1; omega
    have : 2 ≤ 2 ^ (Y - 1) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (Y - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hs' : s + 4 ≤ 2 ^ (2 * Y + 1) := le_trans hs2 (Nat.pow_le_pow_right (by norm_num)
      (by omega))
    rw [e, hP]
    rw [hP] at hs'
    nlinarith
  have hbig : 2 ^ (s + 4 + P) ≤ 2 ^ (2 ^ (3 * Y)) := Nat.pow_le_pow_right (by norm_num) hexp2
  have hmle : m ≤ 2 ^ (2 ^ (3 * Y)) := by
    refine hmY.trans (Nat.pow_le_pow_right (by norm_num) ?_)
    exact le_trans (Nat.lt_two_pow_self).le (Nat.pow_le_pow_right (by norm_num) (by omega))
  exact max_le hmle (max_le hmle (hterm.trans hbig))

/-- **`NeditE s δ_s ≤ 2^(2^(3·Yedit s))`.** -/
theorem NeditE_le_two_pow (s : ℕ) : NeditE s (deltaS s) ≤ 2 ^ (2 ^ (3 * Yedit s)) := by
  have h2 := two_le_mV (ε := ((deltaS s : ℚ) : ℝ)) (by exact_mod_cast deltaS_pos s)
  unfold NeditE NeditV
  exact edit_arith s (mVq (deltaS s)) (Yedit s) (by unfold mVq; omega) (mVq_deltaS_le s)
    (Yedit_ge s)

theorem le_tower2_self (n : ℕ) : n ≤ tower2 n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [tower2_succ]
    have := (Nat.lt_two_pow_self (n := tower2 n))
    omega

theorem two_pow_two_pow_le_tower2 (n : ℕ) : 2 ^ (2 ^ n) ≤ tower2 (n + 2) := by
  rw [tower2_succ, tower2_succ]
  exact Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_right (by norm_num) (le_tower2_self n))

/-- **`NeditE s δ_s ≤ tower2 (3·Yedit s + 2)`.** -/
theorem NeditE_le_tower (s : ℕ) : NeditE s (deltaS s) ≤ tower2 (3 * Yedit s + 2) :=
  (NeditE_le_two_pow s).trans (two_pow_two_pow_le_tower2 _)

end E35
