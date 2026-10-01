import E18.NibbleChain
import E19.ScheduleBounds

/-!
# E35 — schedule and chain bounds for the tight nibble at `r = 7`, generic in `β`

This is the `β`-generic version of `E19/ScheduleBounds.lean` and `E19/ChainBounds.lean`
(which are hard-coded at `β₀ = 1/(64·10^18)`).  We fix a natural number `L` with
`2^(-L) ≤ β ≤ 1/2` (`Adm L β`) and bound every scalar constant of the schedule by a power of
two whose exponent is an explicit function of `L`:

* `MT 7 β ≤ 78 L + 1`, `exp (8 MT + 1) ≤ 2^Ae`, `Ae = 896 L + 13`;
* `2^(-A) ≤ gamT 7 β`, `A = Ae + 5`;
* `TT 7 β ≤ 2^(A+L+7)`, `(2 GgT)^TT ≤ 2^Ybig`, `Ybig = 2^(2A+L+10)`;
* `2^(-(Ybig+L+3)) ≤ excT`, `2^(-B0) ≤ lominT`, `B0 = 194 L + 5`;
* `D0T ≤ 2^(A+2L+14)`, `2^(-(Ybig+Zc)) ≤ muT`, `Zc = 3A + 3L + 22 + B0`;
* `DS ≤ 2^W`, `2^(-W) ≤ gamR 6 β`, `W = Ybig + Zc + 8`.
-/

namespace E35.Sched

open E18.Nib

/-- Admissible pairs: `2^(-L) ≤ β ≤ 1/2`. -/
def Adm (L : ℕ) (β : ℝ) : Prop := ((2 : ℝ) ^ L)⁻¹ ≤ β ∧ β ≤ 1 / 2

/-- Exponent of `exp (8 MT + 1) ≤ 2^Ae`. -/
def Ae (L : ℕ) : ℕ := 896 * L + 13
/-- Exponent of `1/gamT ≤ 2^A`. -/
def A (L : ℕ) : ℕ := Ae L + 5
/-- `(2 GgT)^TT ≤ 2^Ybig`. -/
def Ybig (L : ℕ) : ℕ := 2 ^ (2 * A L + L + 10)
/-- `1/lominT ≤ 2^B0`. -/
def B0 (L : ℕ) : ℕ := 194 * L + 5
/-- The additive part of the exponent of `1/muT`. -/
def Zc (L : ℕ) : ℕ := 3 * A L + 3 * L + 22 + B0 L
/-- The exponent of the chain codegree constant. -/
def W (L : ℕ) : ℕ := Ybig L + Zc L + 8

theorem A_eq (L : ℕ) : A L = 896 * L + 18 := by unfold A Ae; ring

variable {L : ℕ} {β : ℝ}

theorem Adm.pos (h : Adm L β) : 0 < β := lt_of_lt_of_le (by positivity) h.1
theorem Adm.lt_one (h : Adm L β) : β < 1 := by linarith [h.2]
theorem Adm.inv_le (h : Adm L β) : β⁻¹ ≤ (2 : ℝ) ^ L := E19.Sched.inv_le_of_lb h.1

theorem nat_succ_le_two_pow (n : ℕ) : n + 1 ≤ 2 ^ n := Nat.lt_two_pow_self

theorem four_mul_le_two_pow_of_four_le (n : ℕ) (hn : 4 ≤ n) : 4 * n ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih => rw [pow_succ]; omega

theorem real_succ_le_two_pow (n : ℕ) : (n : ℝ) + 1 ≤ (2 : ℝ) ^ n := by
  exact_mod_cast nat_succ_le_two_pow n

/-! ## `LT`, `MT` -/

theorem LT_le (h : Adm L β) : E18.Nib.LT β ≤ L * Real.log 2 := by
  unfold E18.Nib.LT
  rw [← Real.log_inv]
  have h1 : Real.log β⁻¹ ≤ Real.log ((2 : ℝ) ^ L) :=
    Real.log_le_log (inv_pos.2 h.pos) h.inv_le
  rw [Real.log_pow] at h1
  exact h1

theorem LT_pos (h : Adm L β) : 0 < E18.Nib.LT β := by
  unfold E18.Nib.LT; have := Real.log_neg h.pos h.lt_one; linarith

theorem exp_LT (h : Adm L β) : Real.exp (E18.Nib.LT β) = β⁻¹ := by
  unfold E18.Nib.LT; rw [Real.exp_neg, Real.exp_log h.pos]

theorem MT_le (h : Adm L β) : MT 7 β ≤ 78 * L + 1 := by
  unfold MT
  have h1 := LT_le h
  have h2 := Real.log_two_lt_d9
  have hL : (0 : ℝ) ≤ L := Nat.cast_nonneg L
  push_cast
  nlinarith

theorem one_le_MT (h : Adm L β) : 1 ≤ MT 7 β := by
  unfold MT; have := LT_pos h; push_cast; linarith

/-! ## `gamT` -/

theorem gamT_pos : 0 < gamT 7 β := by
  unfold gamT; exact lt_min (by norm_num) (by positivity)

theorem gamT_le : gamT 7 β ≤ 1 / 8 := min_le_left _ _

theorem exp_MT_le (h : Adm L β) : Real.exp (8 * MT 7 β + 1) ≤ 2 ^ Ae L := by
  have e1 : 8 * MT 7 β + 1 = (896 : ℕ) * E18.Nib.LT β + 9 := by unfold MT; push_cast; ring
  rw [e1, Real.exp_add, Real.exp_nat_mul, exp_LT h]
  have h9 : Real.exp 9 ≤ 2 ^ 13 := E19.Sched.exp_le_two_pow 9 13 (by norm_num)
  have hb : (β⁻¹) ^ 896 ≤ ((2 : ℝ) ^ L) ^ 896 :=
    pow_le_pow_left₀ (inv_pos.2 h.pos).le h.inv_le 896
  have : (2 : ℝ) ^ Ae L = ((2 : ℝ) ^ L) ^ 896 * 2 ^ 13 := by
    rw [Ae, pow_add, ← pow_mul, mul_comm L 896]
  rw [this]
  exact mul_le_mul hb h9 (by positivity) (by positivity)

theorem gamT_ge (h : Adm L β) : ((2 : ℝ) ^ A L)⁻¹ ≤ gamT 7 β := by
  unfold gamT
  apply le_min
  · rw [inv_le_comm₀ (by positivity) (by norm_num)]
    calc (1 / 8 : ℝ)⁻¹ = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ A L := pow_le_pow_right₀ (by norm_num) (by unfold A Ae; omega)
  · have hE := exp_MT_le h
    have hprod : Real.exp (-(8 * MT 7 β) - 1) = (Real.exp (8 * MT 7 β + 1))⁻¹ := by
      rw [← Real.exp_neg]; ring_nf
    rw [hprod, A, pow_add, mul_inv, div_eq_mul_inv]
    gcongr
    norm_num

theorem one_le_N_mul_gamT (h : Adm L β) : 1 ≤ (2 : ℝ) ^ A L * gamT 7 β := by
  have h' := mul_le_mul_of_nonneg_left (gamT_ge h) (show (0 : ℝ) ≤ 2 ^ A L by positivity)
  rwa [mul_inv_cancel₀ (by positivity)] at h'

theorem aT_seven : aT 7 = 6 / 7 := by unfold aT; norm_num

theorem epsT_eq : epsT 7 β = 24 / 7 * gamT 7 β := by
  unfold epsT; rw [aT_seven]; ring

theorem epsT_pos : 0 < epsT 7 β := by rw [epsT_eq]; have := @gamT_pos β; positivity

theorem epsT_ge (h : Adm L β) : ((2 : ℝ) ^ A L)⁻¹ ≤ epsT 7 β := by
  rw [epsT_eq]; have := gamT_ge h; have := @gamT_pos β; linarith

theorem qT_eq : qT 7 β = 1 - 6 / 7 * gamT 7 β := by
  unfold qT; rw [aT_seven]

/-! ## `TT` -/

theorem TT_lt (h : Adm L β) : (TT 7 β : ℝ) < MT 7 β / gamT 7 β + 1 := by
  have h1 := one_le_MT h
  have h2 := @gamT_pos β
  exact Nat.ceil_lt_add_one (by positivity)

theorem gamT_mul_TT_le (h : Adm L β) : gamT 7 β * TT 7 β ≤ MT 7 β + gamT 7 β := by
  have h' := TT_lt h
  have hg := @gamT_pos β
  have := mul_lt_mul_of_pos_left h' hg
  rw [mul_add, mul_div_cancel₀ _ hg.ne'] at this
  linarith

theorem TT_le (h : Adm L β) : TT 7 β ≤ 2 ^ (A L + L + 7) := by
  have h' := TT_lt h
  have hg := @gamT_pos β
  have hN := one_le_N_mul_gamT h
  have hM := MT_le h
  have hM1 := one_le_MT h
  have hL : (0 : ℝ) ≤ L := Nat.cast_nonneg L
  have h1 : MT 7 β / gamT 7 β ≤ (78 * L + 1) * 2 ^ A L := by
    rw [div_le_iff₀ hg]; nlinarith
  have h2 : (1 : ℝ) ≤ 2 ^ A L := E19.Sched.one_le_two_pow (A L)
  have h3 := real_succ_le_two_pow L
  have h4 : (78 * (L : ℝ) + 2) ≤ 2 ^ (L + 7) := by rw [pow_add]; nlinarith
  have h5 : (TT 7 β : ℝ) ≤ ((2 ^ (A L + L + 7) : ℕ) : ℝ) := by
    push_cast
    rw [add_assoc, pow_add (2 : ℝ) (A L)]
    nlinarith
  exact_mod_cast h5

/-! ## `GgT`, `excT` -/

theorem two_le_two_pow_A : (2 : ℝ) ≤ 2 ^ A L := by
  calc (2 : ℝ) = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ A L := pow_le_pow_right₀ (by norm_num) (by unfold A; omega)

theorem two_GgT_le (h : Adm L β) : 2 * GgT 7 β ≤ 2 ^ (A L * 4 + 5) := by
  unfold GgT
  rw [epsT_eq]
  set g := gamT 7 β with hgdef
  set N : ℝ := 2 ^ A L with hNdef
  have hg := @gamT_pos β
  have hNg := one_le_N_mul_gamT h
  rw [← hgdef, ← hNdef] at hNg
  rw [← hgdef] at hg
  have hN1 : (1 : ℝ) ≤ N := E19.Sched.one_le_two_pow (A L)
  have hNg2 : 1 ≤ N ^ 2 * g ^ 2 := by nlinarith
  have hfrac : ((7 : ℕ) : ℝ) / (24 / 7 * g * g) ≤ 3 * N ^ 2 := by
    rw [div_le_iff₀ (by positivity)]; push_cast; nlinarith
  have hpos : (0 : ℝ) ≤ ((7 : ℕ) : ℝ) / (24 / 7 * g * g) := by positivity
  have hN2' : (2 : ℝ) ≤ N := two_le_two_pow_A
  have hN2 : (2 : ℝ) ≤ N ^ 2 := by nlinarith
  have hbase : 2 + ((7 : ℕ) : ℝ) / (24 / 7 * g * g) ≤ 4 * N ^ 2 := by linarith
  have hsq : (2 + ((7 : ℕ) : ℝ) / (24 / 7 * g * g)) ^ 2 ≤ (4 * N ^ 2) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hbase 2
  have hpow : (2 : ℝ) ^ (A L * 4 + 5) = 32 * N ^ 4 := by
    rw [pow_add, pow_mul, ← hNdef]; norm_num; ring
  rw [hpow]
  nlinarith

theorem GgT_pos : 0 < GgT 7 β := by
  unfold GgT; have := @epsT_pos β; have := @gamT_pos β; positivity

theorem exponent_TT_le (h : Adm L β) : (A L * 4 + 5) * TT 7 β ≤ Ybig L := by
  have h1 : A L * 4 + 5 ≤ 2 ^ (A L + 3) := by
    have := nat_succ_le_two_pow (A L)
    rw [pow_add]; omega
  calc (A L * 4 + 5) * TT 7 β ≤ 2 ^ (A L + 3) * 2 ^ (A L + L + 7) := Nat.mul_le_mul h1 (TT_le h)
    _ = Ybig L := by rw [Ybig, ← pow_add]; congr 1; ring

theorem two_GgT_pow_TT_le (h : Adm L β) : (2 * GgT 7 β) ^ TT 7 β ≤ (2 : ℝ) ^ Ybig L := by
  calc (2 * GgT 7 β) ^ TT 7 β ≤ ((2 : ℝ) ^ (A L * 4 + 5)) ^ TT 7 β :=
        pow_le_pow_left₀ (by have := @GgT_pos β; positivity) (two_GgT_le h) _
    _ = (2 : ℝ) ^ ((A L * 4 + 5) * TT 7 β) := by rw [← pow_mul]
    _ ≤ (2 : ℝ) ^ Ybig L := pow_le_pow_right₀ (by norm_num) (exponent_TT_le h)

theorem excT_ge (h : Adm L β) : ((2 : ℝ) ^ (Ybig L + L + 3))⁻¹ ≤ excT 7 β := by
  unfold excT
  have hX := two_GgT_pow_TT_le h
  have hXpos : 0 < (2 * GgT 7 β) ^ TT 7 β := by have := @GgT_pos β; positivity
  rw [div_eq_mul_inv, show Ybig L + L + 3 = L + (3 + Ybig L) by omega, pow_add, mul_inv]
  apply mul_le_mul h.1 _ (by positivity) h.pos.le
  apply inv_anti₀ (by positivity)
  rw [pow_add]
  norm_num
  exact hX

theorem excT_pos (h : Adm L β) : 0 < excT 7 β := lt_of_lt_of_le (by positivity) (excT_ge h)

/-! ## `lominT` -/

theorem lominT_ge (h : Adm L β) : ((2 : ℝ) ^ B0 L)⁻¹ ≤ lominT 7 β := by
  unfold lominT
  rw [qT_eq]
  set g := gamT 7 β with hgdef
  set T := TT 7 β with hTdef
  have hg := @gamT_pos β
  have hg8 := @gamT_le β
  rw [← hgdef] at hg hg8
  set x : ℝ := 6 / 7 * g with hx
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x ≤ 1 / 2 := by rw [hx]; linarith
  have h1 : (1 + 2 * x)⁻¹ ≤ 1 - x := by
    rw [inv_le_iff_one_le_mul₀ (by positivity)]
    nlinarith
  have h2 : (1 + 2 * x) ^ T ≤ Real.exp (T * (2 * x)) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp (2 * x)]) T
  have hgT := gamT_mul_TT_le h
  have hM := MT_le h
  rw [← hgdef, ← hTdef] at hgT
  have hL : (0 : ℝ) ≤ L := Nat.cast_nonneg L
  have h3 : (T : ℝ) * (2 * x) ≤ ((194 * L + 4 : ℕ) : ℝ) * 0.6931471803 := by
    rw [hx]; push_cast; nlinarith
  have h4 : Real.exp (T * (2 * x)) ≤ 2 ^ (194 * L + 4) := E19.Sched.exp_le_two_pow _ _ h3
  have h5 : ((2 : ℝ) ^ (194 * L + 4))⁻¹ ≤ (1 - x) ^ T := by
    calc ((2 : ℝ) ^ (194 * L + 4))⁻¹ ≤ ((1 + 2 * x) ^ T)⁻¹ :=
          inv_anti₀ (by positivity) (le_trans h2 h4)
      _ = ((1 + 2 * x)⁻¹) ^ T := (inv_pow _ _).symm
      _ ≤ (1 - x) ^ T := pow_le_pow_left₀ (by positivity) h1 T
  rw [B0, show 194 * L + 5 = (194 * L + 4) + 1 by ring, pow_succ, mul_inv]
  have : (0 : ℝ) ≤ ((2 : ℝ) ^ (194 * L + 4))⁻¹ := by positivity
  generalize ((2 : ℝ) ^ (194 * L + 4))⁻¹ = P at h5 this ⊢
  nlinarith

theorem lominT_pos (h : Adm L β) : 0 < lominT 7 β := lt_of_lt_of_le (by positivity) (lominT_ge h)

/-! ## Chain constants -/

theorem betaN_eq (h : Adm L β) : betaN β = β := by
  unfold betaN; exact min_eq_left h.2

theorem half_sq_ge (h : Adm L β) : ((2 : ℝ) ^ (2 * L + 2))⁻¹ ≤ (β / 2) ^ 2 := by
  have h1 : ((2 : ℝ) ^ (L + 1))⁻¹ ≤ β / 2 := by
    rw [pow_succ, mul_inv]; have := h.1; linarith
  have h2 := pow_le_pow_left₀ (by positivity) h1 2
  rw [← inv_pow, ← pow_mul] at h2
  rw [show (L + 1) * 2 = 2 * L + 2 by ring] at h2
  rwa [inv_pow] at h2

theorem D0T_le (h : Adm L β) : D0T 7 β ≤ 2 ^ (A L + 2 * L + 14) := by
  unfold D0T
  rw [epsT_eq]
  set g := gamT 7 β with hgdef
  set N : ℝ := 2 ^ A L with hNdef
  set P : ℝ := 2 ^ (2 * L + 2) with hPdef
  have hg := @gamT_pos β
  have hNg := one_le_N_mul_gamT h
  rw [← hgdef, ← hNdef] at hNg
  rw [← hgdef] at hg
  have hN1 : (1 : ℝ) ≤ N := E19.Sched.one_le_two_pow (A L)
  have hP1 : (1 : ℝ) ≤ P := E19.Sched.one_le_two_pow _
  have hq := half_sq_ge h
  rw [← hPdef] at hq
  have hqpos : 0 < (β / 2) ^ 2 := by have := h.pos; positivity
  have hPq : 1 ≤ P * (β / 2) ^ 2 := by
    have := mul_le_mul_of_nonneg_left hq (show (0 : ℝ) ≤ P by positivity)
    rwa [mul_inv_cancel₀ (by positivity)] at this
  have h1 : 256 * ((7 : ℕ) : ℝ) / ((β / 2) ^ 2 * g) ≤ 1792 * P * N := by
    rw [div_le_iff₀ (by positivity)]; push_cast
    have : 1 ≤ (P * (β / 2) ^ 2) * (N * g) := by nlinarith
    nlinarith
  have h2 : 96 / (24 / 7 * g) ≤ 28 * N := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have h3 : (2 : ℝ) ^ (A L + 2 * L + 14) = 2 ^ 12 * P * N := by
    rw [hPdef, hNdef, show A L + 2 * L + 14 = 12 + (2 * L + 2) + A L by ring, pow_add, pow_add]
  rw [h3]
  have hPN : 1 ≤ P * N := by nlinarith
  nlinarith

theorem D0T_pos (h : Adm L β) : 0 < D0T 7 β := by
  unfold D0T; have := @gamT_pos β; have := @epsT_pos β; have := h.pos; positivity

theorem c0T_ge (h : Adm L β) :
    ((2 : ℝ) ^ (Ybig L + 3 * A L + 3 * L + 22))⁻¹ ≤ c0T 7 β := by
  unfold c0T
  have hc : ((2 : ℝ) ^ 17)⁻¹ ≤ (16384 * ((7 : ℕ) : ℝ))⁻¹ := by norm_num
  have e := E19.Sched.lb_mul (E19.Sched.lb_mul (E19.Sched.lb_mul (E19.Sched.lb_mul (excT_ge h)
    (E19.Sched.lb_mul (epsT_ge h) (epsT_ge h))) (gamT_ge h)) (half_sq_ge h)) hc
  have hexp : Ybig L + L + 3 + (A L + A L) + A L + (2 * L + 2) + 17
      = Ybig L + 3 * A L + 3 * L + 22 := by ring
  rw [hexp] at e
  rw [div_eq_mul_inv, sq (epsT 7 β)]
  exact e

theorem c0T_pos (h : Adm L β) : 0 < c0T 7 β := lt_of_lt_of_le (by positivity) (c0T_ge h)

theorem muT_ge (h : Adm L β) : ((2 : ℝ) ^ (Ybig L + Zc L))⁻¹ ≤ muT 7 β := by
  unfold muT
  have hA : A L ≤ Ybig L + Zc L := by unfold Zc; omega
  refine le_min ?_ (le_min ?_ (le_min ?_ ?_))
  · apply E19.Sched.lb_mono hA
    have := gamT_ge h; have := @gamT_pos β; linarith
  · have := E19.Sched.lb_mul (c0T_ge h) (lominT_ge h)
    rw [show Ybig L + 3 * A L + 3 * L + 22 + B0 L = Ybig L + Zc L by unfold Zc; ring] at this
    exact this
  · have hD := D0T_le h
    have hle : 2 * (D0T 7 β + 1) ≤ (2 : ℝ) ^ (A L + 2 * L + 16) := by
      have : (2 : ℝ) ^ (A L + 2 * L + 16) = 4 * 2 ^ (A L + 2 * L + 14) := by
        rw [show A L + 2 * L + 16 = (A L + 2 * L + 14) + 2 by ring, pow_add]; ring
      have := E19.Sched.one_le_two_pow (A L + 2 * L + 14)
      linarith
    have h' := E19.Sched.lb_of_ub_inv (by have := D0T_pos h; positivity) hle
    rw [one_div]
    exact E19.Sched.lb_mono (by unfold Zc; omega) h'
  · have : ((2 : ℝ) ^ (Ybig L + Zc L))⁻¹ ≤ ((2 : ℝ) ^ 1)⁻¹ :=
      inv_anti₀ (by positivity) (pow_le_pow_right₀ (by norm_num) (by unfold Zc; omega))
    simpa using this

theorem muT_pos (h : Adm L β) : 0 < muT 7 β := lt_of_lt_of_le (by positivity) (muT_ge h)

theorem d0T_le (h : Adm L β) : d0T 7 β ≤ 2 ^ (A L + 2 * L + 14 + B0 L) := by
  unfold d0T
  apply max_le (E19.Sched.one_le_two_pow _)
  rw [div_eq_mul_inv, pow_add]
  exact mul_le_mul (D0T_le h) (E19.Sched.inv_le_of_lb (lominT_ge h))
    (by have := lominT_pos h; positivity) (by positivity)

theorem kS_seven : (kS 7 : ℝ) = 50 := by norm_num [kS]

theorem DS_le (h : Adm L β) : (DS 7 β : ℝ) ≤ 2 ^ W L := by
  unfold DS muN d0N
  rw [betaN_eq h]
  push_cast
  rw [kS_seven]
  have hmu := muT_pos h
  have hd := d0T_le h
  have hc1 : (⌈d0T 7 β⌉₊ : ℝ) < d0T 7 β + 1 :=
    Nat.ceil_lt_add_one (le_trans zero_le_one (le_max_left _ _))
  have hc2 : (⌈4 * 50 / muT 7 β⌉₊ : ℝ) < 4 * 50 / muT 7 β + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hinv : (muT 7 β)⁻¹ ≤ 2 ^ (Ybig L + Zc L) := E19.Sched.inv_le_of_lb (muT_ge h)
  have hd' : d0T 7 β ≤ 2 ^ (Ybig L + Zc L) := E19.Sched.ub_mono (by unfold Zc; omega) hd
  have hW : (2 : ℝ) ^ W L = 256 * 2 ^ (Ybig L + Zc L) := by
    rw [W, pow_add]; norm_num; ring
  rw [hW]
  have h1 := E19.Sched.one_le_two_pow (Ybig L + Zc L)
  have h200 : 4 * 50 / muT 7 β ≤ 200 * 2 ^ (Ybig L + Zc L) := by
    rw [div_eq_mul_inv]; linarith
  have := max_le_iff.2 ⟨hc1.le.trans (by linarith : d0T 7 β + 1 ≤ 200 * 2 ^ (Ybig L + Zc L) + 1),
    hc2.le.trans (by linarith : 4 * 50 / muT 7 β + 1 ≤ 200 * 2 ^ (Ybig L + Zc L) + 1)⟩
  linarith

theorem DS_pos : (0 : ℝ) < DS 7 β := by
  unfold DS; positivity

theorem gamW_ge (h : Adm L β) : ((2 : ℝ) ^ W L)⁻¹ ≤ gamW 7 β := by
  unfold gamW
  apply le_min
  · rw [one_div]; exact E19.Sched.lb_of_ub_inv DS_pos (DS_le h)
  · unfold muN; rw [betaN_eq h]
    have h' := muT_ge h
    have : ((2 : ℝ) ^ W L)⁻¹ ≤ ((2 : ℝ) ^ (Ybig L + Zc L))⁻¹ / 4 := by
      rw [W, pow_add, mul_inv]
      have : (0 : ℝ) < ((2 : ℝ) ^ (Ybig L + Zc L))⁻¹ := by positivity
      norm_num
      nlinarith
    linarith

theorem gamR_ge (h : Adm L β) : ((2 : ℝ) ^ W L)⁻¹ ≤ gamR 6 β := by
  unfold gamR
  apply le_min (gamW_ge h)
  exact inv_le_one_of_one_le₀ (E19.Sched.one_le_two_pow _)

theorem gamR_pos (h : Adm L β) : 0 < gamR 6 β := lt_of_lt_of_le (by positivity) (gamR_ge h)

theorem gamR_le_one : gamR 6 β ≤ 1 := min_le_right _ _

end E35.Sched
