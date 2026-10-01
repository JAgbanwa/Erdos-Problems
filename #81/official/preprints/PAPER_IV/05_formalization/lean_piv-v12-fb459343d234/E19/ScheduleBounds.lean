import E18.NibbleSchedule

/-!
# E19 — numerical bounds for the tight nibble schedule at `r = 7`, `β₀ = 1/(64·10^18)`

The dense gate of the far instance at `zq₀ = 1/(2·10^17)` calls the explicit nibble
constants with `r = 7` and `β₀ = zq₀/320 = 1/(64·10^18)` (see `E19.GateBounds`).  This file
bounds the scalar schedule parameters of `E18/NibbleSchedule.lean` at that point:

* `LT β₀ ≤ 46`, `MT 7 β₀ ≤ 5153`;
* `2^(-A0) ≤ gamT 7 β₀ ≤ 1/8` with `A0 = 59485`  (the only place where the constant matters);
* `TT 7 β₀ ≤ 2^(A0+13)`, `2 GgT 7 β₀ ≤ 2^(4 A0 + 5)`,
  `(2 GgT)^TT ≤ 2^Ybig` with `Ybig = 2^(A0+31)`;
* `2^(-(Ybig+69)) ≤ excT 7 β₀` and `2^(-B0) ≤ lominT 7 β₀` with `B0 = 12749`.

All bounds are stated with symbolic exponents (`A0`, `Ybig` are definitions), so no tactic
ever evaluates a power of astronomical size.
-/

namespace E19.Sched

open E18.Nib

/-- `β₀ = 1/(64·10^18)`. -/
noncomputable def beta0 : ℝ := 1 / (64 * 10 ^ 18)

/-- Exponent in the bound `exp (8 MT + 1) ≤ 2^Ae`. -/
def Ae : ℕ := 59480
/-- `1/gamT 7 β₀ ≤ 2^A0`, `A0 = 59485`. -/
def A0 : ℕ := Ae + 5
/-- The main exponent `Ybig = 2^(A0+31)`: `(2 GgT)^TT ≤ 2^Ybig`. -/
irreducible_def Ybig : ℕ := 2 ^ (A0 + 31)
/-- `1/lominT 7 β₀ ≤ 2^B0`, `B0 = 12749`. -/
def B0 : ℕ := 12749

theorem A0_eq : A0 = 59485 := rfl

/-! ## Generic helpers on powers of two -/

theorem exp_le_two_pow (x : ℝ) (n : ℕ) (h : x ≤ (n : ℝ) * 0.6931471803) :
    Real.exp x ≤ 2 ^ n := by
  have hl := Real.log_two_gt_d9
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have : x ≤ n * Real.log 2 := le_trans h (by nlinarith)
  calc Real.exp x ≤ Real.exp (n * Real.log 2) := Real.exp_le_exp.2 this
    _ = 2 ^ n := by rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]

theorem inv_two_pow_pos (a : ℕ) : (0 : ℝ) < ((2 : ℝ) ^ a)⁻¹ := by positivity

theorem lb_mono {x : ℝ} {a b : ℕ} (hab : a ≤ b) (h : ((2 : ℝ) ^ a)⁻¹ ≤ x) :
    ((2 : ℝ) ^ b)⁻¹ ≤ x :=
  le_trans (inv_anti₀ (by positivity) (pow_le_pow_right₀ (by norm_num) hab)) h

theorem lb_mul {x y : ℝ} {a b : ℕ} (hx : ((2 : ℝ) ^ a)⁻¹ ≤ x) (hy : ((2 : ℝ) ^ b)⁻¹ ≤ y) :
    ((2 : ℝ) ^ (a + b))⁻¹ ≤ x * y := by
  rw [pow_add, mul_inv]
  exact mul_le_mul hx hy (by positivity) (le_trans (by positivity) hx)

theorem ub_mono {x : ℝ} {a b : ℕ} (hab : a ≤ b) (h : x ≤ (2 : ℝ) ^ a) : x ≤ (2 : ℝ) ^ b :=
  le_trans h (pow_le_pow_right₀ (by norm_num) hab)

theorem inv_le_of_lb {x : ℝ} {a : ℕ} (h : ((2 : ℝ) ^ a)⁻¹ ≤ x) : x⁻¹ ≤ (2 : ℝ) ^ a := by
  have hx : 0 < x := lt_of_lt_of_le (by positivity) h
  rw [inv_le_comm₀ hx (by positivity)]
  exact h

theorem lb_of_ub_inv {x : ℝ} {a : ℕ} (hx : 0 < x) (h : x ≤ (2 : ℝ) ^ a) :
    ((2 : ℝ) ^ a)⁻¹ ≤ x⁻¹ :=
  inv_anti₀ hx h

theorem one_le_two_pow (a : ℕ) : (1 : ℝ) ≤ (2 : ℝ) ^ a := one_le_pow₀ (by norm_num)

/-! ## `β₀`, `LT`, `MT` -/

theorem beta0_pos : 0 < beta0 := by norm_num [beta0]
theorem beta0_lt_one : beta0 < 1 := by norm_num [beta0]
theorem beta0_le_half : beta0 ≤ 1 / 2 := by norm_num [beta0]
theorem inv_beta0_le : beta0⁻¹ ≤ 2 ^ 66 := by norm_num [beta0]
theorem beta0_ge : ((2 : ℝ) ^ 66)⁻¹ ≤ beta0 := by norm_num [beta0]

/-- `LT β₀ = log (64·10^18) ≤ 46`. -/
theorem LT_le : E18.Nib.LT beta0 ≤ 46 := by
  unfold E18.Nib.LT
  rw [← Real.log_inv]
  have h1 : Real.log beta0⁻¹ ≤ Real.log ((2 : ℝ) ^ 66) :=
    Real.log_le_log (inv_pos.2 beta0_pos) inv_beta0_le
  rw [Real.log_pow] at h1
  have := Real.log_two_lt_d9
  push_cast at h1
  linarith

theorem LT_pos : 0 < E18.Nib.LT beta0 := by
  unfold E18.Nib.LT; have := Real.log_neg beta0_pos beta0_lt_one; linarith

/-- `MT 7 β₀ = 112 LT β₀ + 1 ≤ 5153`. -/
theorem MT_le : MT 7 beta0 ≤ 5153 := by
  unfold MT; have := LT_le; push_cast; linarith

theorem one_le_MT : 1 ≤ MT 7 beta0 := by
  unfold MT; have := LT_pos; push_cast; linarith

/-! ## The round rate `gamT` -/

theorem gamT_pos : 0 < gamT 7 beta0 := by
  unfold gamT; exact lt_min (by norm_num) (by positivity)

theorem gamT_le : gamT 7 beta0 ≤ 1 / 8 := min_le_left _ _

/-- `exp (8 MT 7 β₀ + 1) ≤ 2^Ae`. -/
theorem exp_MT_le : Real.exp (8 * MT 7 beta0 + 1) ≤ 2 ^ Ae := by
  apply exp_le_two_pow
  have := MT_le
  norm_num [Ae]
  linarith

/-- **`2^(-A0) ≤ gamT 7 β₀`**, `A0 = 59485`. -/
theorem gamT_ge : ((2 : ℝ) ^ A0)⁻¹ ≤ gamT 7 beta0 := by
  unfold gamT
  apply le_min
  · rw [inv_le_comm₀ (by positivity) (by norm_num)]
    calc (1 / 8 : ℝ)⁻¹ = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ A0 := pow_le_pow_right₀ (by norm_num) (by norm_num [A0, Ae])
  · have hE := exp_MT_le
    have hprod : Real.exp (-(8 * MT 7 beta0) - 1) = (Real.exp (8 * MT 7 beta0 + 1))⁻¹ := by
      rw [← Real.exp_neg]; ring_nf
    rw [hprod, A0, pow_add, mul_inv, div_eq_mul_inv]
    gcongr
    norm_num

/-- `1 ≤ 2^A0 · gamT 7 β₀`. -/
theorem one_le_N_mul_gamT : 1 ≤ (2 : ℝ) ^ A0 * gamT 7 beta0 := by
  have h := mul_le_mul_of_nonneg_left gamT_ge (show (0 : ℝ) ≤ 2 ^ A0 by positivity)
  rwa [mul_inv_cancel₀ (by positivity)] at h

theorem inv_gamT_le : (gamT 7 beta0)⁻¹ ≤ 2 ^ A0 := inv_le_of_lb gamT_ge

/-! ## `aT`, `epsT`, `qT` -/

theorem aT_seven : aT 7 = 6 / 7 := by unfold aT; norm_num

theorem epsT_eq : epsT 7 beta0 = 24 / 7 * gamT 7 beta0 := by
  unfold epsT; rw [aT_seven]; ring

theorem epsT_pos : 0 < epsT 7 beta0 := by rw [epsT_eq]; have := gamT_pos; positivity

theorem epsT_ge : ((2 : ℝ) ^ A0)⁻¹ ≤ epsT 7 beta0 := by
  rw [epsT_eq]; have := gamT_ge; have := gamT_pos; linarith

theorem qT_eq : qT 7 beta0 = 1 - 6 / 7 * gamT 7 beta0 := by
  unfold qT; rw [aT_seven]

/-! ## The number of rounds `TT` -/

theorem TT_lt : (TT 7 beta0 : ℝ) < MT 7 beta0 / gamT 7 beta0 + 1 := by
  have h1 := one_le_MT
  have h2 := gamT_pos
  exact Nat.ceil_lt_add_one (by positivity)

/-- `gamT · TT ≤ MT + gamT`. -/
theorem gamT_mul_TT_le : gamT 7 beta0 * TT 7 beta0 ≤ MT 7 beta0 + gamT 7 beta0 := by
  have h := TT_lt
  have hg := gamT_pos
  have := mul_lt_mul_of_pos_left h hg
  rw [mul_add, mul_div_cancel₀ _ hg.ne'] at this
  linarith

/-- **`TT 7 β₀ ≤ 2^(A0+13)`**. -/
theorem TT_le : TT 7 beta0 ≤ 2 ^ (A0 + 13) := by
  have h := TT_lt
  have hg := gamT_pos
  have hN := one_le_N_mul_gamT
  have hM := MT_le
  have h1 : MT 7 beta0 / gamT 7 beta0 ≤ 5153 * 2 ^ A0 := by
    rw [div_le_iff₀ hg]; nlinarith
  have h2 : (1 : ℝ) ≤ 2 ^ A0 := one_le_two_pow A0
  have h3 : (TT 7 beta0 : ℝ) ≤ ((2 ^ (A0 + 13) : ℕ) : ℝ) := by
    push_cast; rw [pow_add]; nlinarith
  exact_mod_cast h3

/-! ## The exceptional growth factor `GgT` and the fraction `excT` -/

/-- **`2 GgT 7 β₀ ≤ 2^(4 A0 + 5)`**. -/
theorem two_GgT_le : 2 * GgT 7 beta0 ≤ 2 ^ (A0 * 4 + 5) := by
  unfold GgT
  rw [epsT_eq]
  set g := gamT 7 beta0 with hgdef
  set N : ℝ := 2 ^ A0 with hNdef
  have hg := gamT_pos
  have hNg := one_le_N_mul_gamT
  rw [← hgdef, ← hNdef] at hNg
  have hN1 : (1 : ℝ) ≤ N := one_le_two_pow A0
  have hNg2 : 1 ≤ N ^ 2 * g ^ 2 := by nlinarith
  have hfrac : ((7 : ℕ) : ℝ) / (24 / 7 * g * g) ≤ 3 * N ^ 2 := by
    rw [div_le_iff₀ (by positivity)]; push_cast; nlinarith
  have hpos : (0 : ℝ) ≤ ((7 : ℕ) : ℝ) / (24 / 7 * g * g) := by positivity
  have hN2' : (2 : ℝ) ≤ N := by
    rw [hNdef]
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ A0 := pow_le_pow_right₀ (by norm_num) (by norm_num [A0, Ae])
  have hN2 : (2 : ℝ) ≤ N ^ 2 := by nlinarith
  have hbase : 2 + ((7 : ℕ) : ℝ) / (24 / 7 * g * g) ≤ 4 * N ^ 2 := by linarith
  have hsq : (2 + ((7 : ℕ) : ℝ) / (24 / 7 * g * g)) ^ 2 ≤ (4 * N ^ 2) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hbase 2
  have hpow : (2 : ℝ) ^ (A0 * 4 + 5) = 32 * N ^ 4 := by
    rw [pow_add, pow_mul, ← hNdef]; norm_num; ring
  rw [hpow]
  nlinarith

theorem GgT_pos : 0 < GgT 7 beta0 := by
  unfold GgT; have := epsT_pos; have := gamT_pos; positivity

theorem one_le_two_GgT : 1 ≤ 2 * GgT 7 beta0 := by
  unfold GgT
  have := epsT_pos; have := gamT_pos
  have hpos : (0 : ℝ) ≤ (7 : ℕ) / (epsT 7 beta0 * gamT 7 beta0) := by positivity
  nlinarith

/-- `(A0·4+5) · TT ≤ Ybig` as natural numbers. -/
theorem exponent_TT_le : (A0 * 4 + 5) * TT 7 beta0 ≤ Ybig := by
  have h1 : A0 * 4 + 5 ≤ 2 ^ 18 := by norm_num [A0, Ae]
  calc (A0 * 4 + 5) * TT 7 beta0 ≤ 2 ^ 18 * 2 ^ (A0 + 13) := Nat.mul_le_mul h1 TT_le
    _ = Ybig := by rw [Ybig_def, ← pow_add, show 18 + (A0 + 13) = A0 + 31 by omega]

/-- **`(2 GgT 7 β₀)^TT ≤ 2^Ybig`**, `Ybig = 2^(A0+31)`. -/
theorem two_GgT_pow_TT_le : (2 * GgT 7 beta0) ^ TT 7 beta0 ≤ (2 : ℝ) ^ Ybig := by
  calc (2 * GgT 7 beta0) ^ TT 7 beta0 ≤ ((2 : ℝ) ^ (A0 * 4 + 5)) ^ TT 7 beta0 :=
        pow_le_pow_left₀ (by have := GgT_pos; positivity) two_GgT_le _
    _ = (2 : ℝ) ^ ((A0 * 4 + 5) * TT 7 beta0) := by rw [← pow_mul]
    _ ≤ (2 : ℝ) ^ Ybig := pow_le_pow_right₀ (by norm_num) exponent_TT_le

/-- **`2^(-(Ybig+69)) ≤ excT 7 β₀`**. -/
theorem excT_ge : ((2 : ℝ) ^ (Ybig + 69))⁻¹ ≤ excT 7 beta0 := by
  unfold excT
  have hX := two_GgT_pow_TT_le
  have hXpos : 0 < (2 * GgT 7 beta0) ^ TT 7 beta0 := by have := GgT_pos; positivity
  rw [div_eq_mul_inv, show Ybig + 69 = 66 + (3 + Ybig) by omega, pow_add, mul_inv]
  apply mul_le_mul beta0_ge _ (by positivity) beta0_pos.le
  apply inv_anti₀ (by positivity)
  rw [pow_add]
  norm_num
  exact hX

theorem excT_pos : 0 < excT 7 beta0 := lt_of_lt_of_le (by positivity) excT_ge

/-! ## The band floor `lominT` -/

/-- **`2^(-B0) ≤ lominT 7 β₀`**, `B0 = 12749`. -/
theorem lominT_ge : ((2 : ℝ) ^ B0)⁻¹ ≤ lominT 7 beta0 := by
  unfold lominT
  rw [qT_eq]
  set g := gamT 7 beta0 with hgdef
  set T := TT 7 beta0 with hTdef
  have hg := gamT_pos
  have hg8 := gamT_le
  rw [← hgdef] at hg hg8
  set x : ℝ := 6 / 7 * g with hx
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x ≤ 1 / 2 := by rw [hx]; linarith
  -- `1 - x ≥ (1 + 2x)⁻¹`
  have h1 : (1 + 2 * x)⁻¹ ≤ 1 - x := by
    rw [inv_le_iff_one_le_mul₀ (by positivity)]
    nlinarith
  -- `(1 + 2x)^T ≤ exp (2 x T)`
  have h2 : (1 + 2 * x) ^ T ≤ Real.exp (T * (2 * x)) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp (2 * x)]) T
  have hgT := gamT_mul_TT_le
  have hM := MT_le
  rw [← hgdef, ← hTdef] at hgT
  have h3 : (T : ℝ) * (2 * x) ≤ 12748 * 0.6931471803 := by
    rw [hx]; nlinarith
  have h4 : Real.exp (T * (2 * x)) ≤ 2 ^ 12748 := exp_le_two_pow _ _ (by exact_mod_cast h3)
  have h5 : ((2 : ℝ) ^ 12748)⁻¹ ≤ (1 - x) ^ T := by
    calc ((2 : ℝ) ^ 12748)⁻¹ ≤ ((1 + 2 * x) ^ T)⁻¹ :=
          inv_anti₀ (by positivity) (le_trans h2 h4)
      _ = ((1 + 2 * x)⁻¹) ^ T := (inv_pow _ _).symm
      _ ≤ (1 - x) ^ T := pow_le_pow_left₀ (by positivity) h1 T
  rw [B0, show (12749 : ℕ) = 12748 + 1 by rfl, pow_succ, mul_inv]
  have : (0 : ℝ) ≤ ((2 : ℝ) ^ 12748)⁻¹ := by positivity
  generalize ((2 : ℝ) ^ 12748)⁻¹ = P at h5 this ⊢
  nlinarith

theorem lominT_pos : 0 < lominT 7 beta0 := lt_of_lt_of_le (by positivity) lominT_ge

end E19.Sched
