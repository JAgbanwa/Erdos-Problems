import E34.Params

/-!
# E34 — explicit parameters of Lemma 11

For `0 < ε < 1` and a tree with `K ≥ 1` nodes:
* `y11 ε K = ⌈256 K² / ε²⌉₊` — the size of the Claim 5 sample (Theorem 6 at `η = ε/(2K)`);
* `δ11 ε K = 1 / (4 y²)` — the conflict threshold;
* `B11 ε K = ⌊8K/δ⌋₊` — the number of rounds in Theorem 2;
and the sample size of Lemma 11 is `m11V ε K = ⌈2^58 (K+1)^15 / ε^12⌉₊`.
The lemmas below are the numerical conditions used in the proof of Lemma 11.
-/

namespace E34

open Real

/-- Sample size of Claim 5. -/
noncomputable def y11 (ε : ℝ) (K : ℕ) : ℕ := ⌈256 * (K : ℝ) ^ 2 / ε ^ 2⌉₊

/-- Conflict threshold. -/
noncomputable def δ11 (ε : ℝ) (K : ℕ) : ℝ := 1 / (4 * (y11 ε K : ℝ) ^ 2)

/-- Number of rounds of Theorem 2. -/
noncomputable def B11 (ε : ℝ) (K : ℕ) : ℕ := ⌊8 * (K : ℝ) / δ11 ε K⌋₊

section

variable {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) {K : ℕ} (hK : 1 ≤ K)
include hε0 hε1 hK

omit hε0 hε1 hK in
theorem y11_ge : 256 * (K : ℝ) ^ 2 / ε ^ 2 ≤ y11 ε K := Nat.le_ceil _

theorem KE_ge : 1 ≤ (K : ℝ) ^ 2 / ε ^ 2 := by
  have hK' : (1 : ℝ) ≤ K := by exact_mod_cast hK
  rw [le_div_iff₀ (by positivity)]; nlinarith

theorem y11_ge' : (256 : ℝ) ≤ y11 ε K := by
  have := y11_ge (ε := ε) (K := K)
  have := KE_ge hε0 hε1 hK
  have : (256 : ℝ) * (K : ℝ) ^ 2 / ε ^ 2 = 256 * ((K : ℝ) ^ 2 / ε ^ 2) := by ring
  nlinarith

theorem y11_le : (y11 ε K : ℝ) ≤ 257 * (K : ℝ) ^ 2 / ε ^ 2 := by
  have h1 := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 256 * (K : ℝ) ^ 2 / ε ^ 2 by positivity)
  have h2 := KE_ge hε0 hε1 hK
  have : (257 : ℝ) * (K : ℝ) ^ 2 / ε ^ 2 = 256 * (K : ℝ) ^ 2 / ε ^ 2 + (K : ℝ) ^ 2 / ε ^ 2 := by
    ring
  unfold y11; linarith

theorem two_le_y11 : 2 ≤ y11 ε K := by
  have := y11_ge' hε0 hε1 hK
  exact_mod_cast (show (2 : ℝ) ≤ y11 ε K by linarith)

theorem δ11_pos : 0 < δ11 ε K := by
  have := y11_ge' hε0 hε1 hK
  unfold δ11; positivity

theorem δ11_le_half : δ11 ε K ≤ ε / 2 := by
  have hy := y11_ge (ε := ε) (K := K)
  have hy' := y11_ge' hε0 hε1 hK
  have hK' : (1 : ℝ) ≤ K := by exact_mod_cast hK
  unfold δ11
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  have h1 : (256 : ℝ) / ε ≤ y11 ε K * ε := by
    have : 256 * (K : ℝ) ^ 2 / ε ^ 2 * ε ^ 2 ≤ y11 ε K * ε ^ 2 := by gcongr
    rw [div_mul_cancel₀ _ (by positivity)] at this
    rw [div_le_iff₀ hε0]
    nlinarith
  have h2 : (256 : ℝ) ≤ 256 / ε := by rw [le_div_iff₀ hε0]; nlinarith
  nlinarith

theorem δ11_le_one : δ11 ε K ≤ 1 := by
  have := δ11_le_half hε0 hε1 hK; linarith

theorem δ11_ge : ε ^ 4 / (2 ^ 19 * (K : ℝ) ^ 4) ≤ δ11 ε K := by
  have hy := y11_le hε0 hε1 hK
  have hy0 : (0 : ℝ) < y11 ε K := by have := y11_ge' hε0 hε1 hK; linarith
  unfold δ11
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : (y11 ε K : ℝ) ^ 2 ≤ (257 * (K : ℝ) ^ 2 / ε ^ 2) ^ 2 := by gcongr
  have h2 : (257 * (K : ℝ) ^ 2 / ε ^ 2) ^ 2 * ε ^ 4 = 66049 * (K : ℝ) ^ 4 := by
    field_simp; ring
  have h3 : ε ^ 4 * (4 * (y11 ε K : ℝ) ^ 2) ≤ 4 * (66049 * (K : ℝ) ^ 4) := by
    have := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 4 * ε ^ 4)
    nlinarith
  nlinarith

/-- **Claim 5 numerics**: `(y+1)(1-η)^(y-1) ≤ 1/4` for `η = ε/(2K)`. -/
theorem block_ineq :
    ((y11 ε K : ℝ) + 1) * (1 - ε / (2 * K)) ^ (y11 ε K - 1) ≤ 1 / 4 := by
  set y := y11 ε K
  have hK' : (1 : ℝ) ≤ K := by exact_mod_cast hK
  set t : ℝ := 2 * K / ε with ht
  have ht2 : 2 ≤ t := by rw [ht, le_div_iff₀ hε0]; nlinarith
  have hη : ε / (2 * K) = 1 / t := by rw [ht]; field_simp
  rw [hη]
  have hy : 64 * t ^ 2 ≤ y := by
    have := y11_ge (ε := ε) (K := K)
    have e : 64 * t ^ 2 = 256 * (K : ℝ) ^ 2 / ε ^ 2 := by rw [ht]; field_simp; ring
    rw [e]; exact this
  have hyle : (y : ℝ) ≤ 64 * t ^ 2 + 1 := by
    have := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 256 * (K : ℝ) ^ 2 / ε ^ 2 by positivity)
    have e : 64 * t ^ 2 = 256 * (K : ℝ) ^ 2 / ε ^ 2 := by rw [ht]; field_simp; ring
    rw [e]; exact this.le
  have hy1 : 1 ≤ y := by
    have : (1 : ℝ) ≤ y := by nlinarith
    exact_mod_cast this
  have hcast : ((y - 1 : ℕ) : ℝ) = (y : ℝ) - 1 := by rw [Nat.cast_sub hy1]; simp
  have ht0 : 0 < t := by linarith
  have h1t : 0 ≤ 1 - 1 / t := by rw [sub_nonneg, div_le_one ht0]; linarith
  have hexp : (1 - 1 / t) ^ (y - 1) ≤ Real.exp (-(((y : ℝ) - 1) / t)) := by
    have h1 : 1 - 1 / t ≤ Real.exp (-(1 / t)) := by
      have := Real.add_one_le_exp (-(1 / t)); linarith
    calc (1 - 1 / t) ^ (y - 1) ≤ Real.exp (-(1 / t)) ^ (y - 1) := pow_le_pow_left₀ h1t h1 _
      _ = Real.exp (-(((y : ℝ) - 1) / t)) := by
          rw [← Real.exp_nat_mul, hcast]; congr 1; ring
  have hX : 64 * t - 1 ≤ ((y : ℝ) - 1) / t := by
    rw [le_div_iff₀ ht0]; nlinarith
  have hX0 : 0 ≤ 64 * t - 1 := by linarith
  have hq := Real.quadratic_le_exp_of_nonneg hX0
  have hE : 4 * ((y : ℝ) + 1) ≤ Real.exp (((y : ℝ) - 1) / t) := by
    have : Real.exp (64 * t - 1) ≤ Real.exp (((y : ℝ) - 1) / t) := Real.exp_le_exp.2 hX
    nlinarith
  have hpos := Real.exp_pos (((y : ℝ) - 1) / t)
  have hprod : Real.exp (-(((y : ℝ) - 1) / t)) * Real.exp (((y : ℝ) - 1) / t) = 1 := by
    rw [← Real.exp_add]; simp
  have hy0 : (0 : ℝ) ≤ (y : ℝ) + 1 := by positivity
  calc ((y : ℝ) + 1) * (1 - 1 / t) ^ (y - 1) ≤ ((y : ℝ) + 1) * Real.exp (-(((y : ℝ) - 1) / t)) :=
        mul_le_mul_of_nonneg_left hexp hy0
    _ ≤ 1 / 4 := by nlinarith [Real.exp_pos (-(((y : ℝ) - 1) / t))]

omit hε0 hε1 hK in
theorem m11V_ge : (2 : ℝ) ^ 58 * ((K : ℝ) + 1) ^ 15 / ε ^ 12 ≤ m11V ε K := Nat.le_ceil _

theorem y11_le_m11V : y11 ε K ≤ m11V ε K := by
  have h1 := y11_le hε0 hε1 hK
  have h2 := m11V_ge (ε := ε) (K := K)
  have hK' : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have h3 : 257 * (K : ℝ) ^ 2 / ε ^ 2 ≤ (2 : ℝ) ^ 58 * ((K : ℝ) + 1) ^ 15 / ε ^ 12 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have e1 : ε ^ 12 ≤ ε ^ 2 := pow_le_pow_of_le_one hε0.le hε1.le (by norm_num)
    have e2 : (K : ℝ) ^ 2 ≤ ((K : ℝ) + 1) ^ 15 := by
      calc (K : ℝ) ^ 2 ≤ ((K : ℝ) + 1) ^ 2 := by gcongr; linarith
        _ ≤ ((K : ℝ) + 1) ^ 15 := pow_le_pow_right₀ (by linarith) (by norm_num)
    have : 257 * (K : ℝ) ^ 2 * ε ^ 12 ≤ 257 * ((K : ℝ) + 1) ^ 15 * ε ^ 2 := by
      gcongr
    nlinarith [pow_pos hε0 2, pow_pos (show (0 : ℝ) < K + 1 by linarith) 15]
  exact_mod_cast h1.trans (h3.trans h2)
end

/-! ### Theorem 2 numerics, split into small steps -/

theorem t2_geom {δ : ℝ} (hδ1 : δ ≤ 1) (m : ℕ) :
    (1 - δ / 4) ^ m ≤ Real.exp (-(δ * m / 4)) := by
  have h1 : 1 - δ / 4 ≤ Real.exp (-(δ / 4)) := by
    have := Real.add_one_le_exp (-(δ / 4)); linarith
  calc (1 - δ / 4) ^ m ≤ Real.exp (-(δ / 4)) ^ m := pow_le_pow_left₀ (by linarith) h1 _
    _ = Real.exp (-(δ * m / 4)) := by rw [← Real.exp_nat_mul]; congr 1; ring

theorem t2_base_aux {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) {K : ℕ} (hK' : (1 : ℝ) ≤ K) :
    4 * (2 ^ 59 * ((K : ℝ) + 1) ^ 15 / ε ^ 12 * 2 ^ K) ≤ Real.exp (89 * K / ε) := by
  have hX : (K : ℝ) ≤ K / ε := by rw [le_div_iff₀ hε0]; nlinarith
  have e2 : (2 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
  have hK1 : (K : ℝ) + 1 ≤ Real.exp K := by have := Real.add_one_le_exp (K : ℝ); linarith
  have hinv : 1 / ε ≤ Real.exp (1 / ε) := by have := Real.add_one_le_exp (1 / ε); linarith
  calc 4 * (2 ^ 59 * ((K : ℝ) + 1) ^ 15 / ε ^ 12 * 2 ^ K)
      = 2 ^ (61 + K) * ((K : ℝ) + 1) ^ 15 * (1 / ε) ^ 12 := by
        field_simp; ring
    _ ≤ Real.exp 1 ^ (61 + K) * Real.exp K ^ 15 * Real.exp (1 / ε) ^ 12 := by
        gcongr
    _ = Real.exp (61 + K + 15 * K + 12 * (1 / ε)) := by
        rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add,
          ← Real.exp_add]; push_cast; ring_nf
    _ ≤ Real.exp (89 * K / ε) := by
        apply Real.exp_le_exp.2
        have h1 : (1 : ℝ) / ε ≤ K / ε := by gcongr
        have h2 : (1 : ℝ) ≤ K / ε := le_trans hK' hX
        have : 89 * (K : ℝ) / ε = 89 * (K / ε) := by ring
        nlinarith

theorem t2_base {ε δ : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) {K m : ℕ} (hK' : (1 : ℝ) ≤ K)
    (hδ1 : δ ≤ 1) (hm1 : (1 : ℝ) ≤ m) (hmle : (m : ℝ) ≤ 2 ^ 59 * ((K : ℝ) + 1) ^ 15 / ε ^ 12) :
    1 + m * 2 ^ K / (1 - δ / 4) ≤ Real.exp (89 * K / ε) := by
  have hr : 1 / 2 ≤ 1 - δ / 4 := by linarith
  have hb : 1 + m * 2 ^ K / (1 - δ / 4) ≤ 4 * (m * 2 ^ K) := by
    have h2K : (1 : ℝ) ≤ 2 ^ K := one_le_pow₀ (by norm_num)
    have hm0 : (0 : ℝ) ≤ m := by positivity
    have : m * 2 ^ K / (1 - δ / 4) ≤ 2 * (m * 2 ^ K) := by
      rw [div_le_iff₀ (by linarith)]
      have hp : (0 : ℝ) ≤ 2 * (m * 2 ^ K) := by positivity
      have := mul_le_mul_of_nonneg_left hr hp
      linarith
    nlinarith
  refine hb.trans ((?_ : 4 * (m * 2 ^ K) ≤ 4 * (2 ^ 59 * ((K : ℝ) + 1) ^ 15 / ε ^ 12 * 2 ^ K)).trans
    (t2_base_aux hε0 hε1 hK'))
  gcongr

theorem t2_rounds {ε δ : ℝ} (hε0 : 0 < ε) {K B : ℕ} (hδ0 : 0 < δ)
    (hδge : ε ^ 4 / (2 ^ 19 * (K : ℝ) ^ 4) ≤ δ) (hK' : (1 : ℝ) ≤ K)
    (hB : (B : ℝ) ≤ 8 * K / δ) : (B : ℝ) ≤ 2 ^ 22 * (K : ℝ) ^ 5 / ε ^ 4 := by
  refine hB.trans ?_
  rw [div_le_div_iff₀ hδ0 (by positivity)]
  have := mul_le_mul_of_nonneg_left hδge (by positivity : (0 : ℝ) ≤ 2 ^ 22 * (K : ℝ) ^ 5)
  have e : 2 ^ 22 * (K : ℝ) ^ 5 * (ε ^ 4 / (2 ^ 19 * (K : ℝ) ^ 4)) = 8 * K * ε ^ 4 := by
    field_simp; ring
  nlinarith

theorem t2_dm {ε δ : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) {K m : ℕ} (hK' : (1 : ℝ) ≤ K)
    (hδ0 : 0 < δ) (hδge : ε ^ 4 / (2 ^ 19 * (K : ℝ) ^ 4) ≤ δ)
    (hm0 : (2 : ℝ) ^ 58 * ((K : ℝ) + 1) ^ 15 / ε ^ 12 ≤ m) :
    2 ^ 37 * ((K : ℝ) ^ 6 / ε ^ 5) ≤ δ * m / 4 := by
  have hdm : ε ^ 4 / (2 ^ 19 * (K : ℝ) ^ 4) * (2 ^ 58 * ((K : ℝ) + 1) ^ 15 / ε ^ 12) ≤ δ * m :=
    mul_le_mul hδge hm0 (by positivity) hδ0.le
  have e : ε ^ 4 / (2 ^ 19 * (K : ℝ) ^ 4) * (2 ^ 58 * ((K : ℝ) + 1) ^ 15 / ε ^ 12) =
      2 ^ 39 * ((K : ℝ) + 1) ^ 15 / ((K : ℝ) ^ 4 * ε ^ 8) := by
    rw [div_mul_div_comm, div_eq_div_iff (by positivity) (by positivity)]; ring
  rw [e] at hdm
  have h3 : 2 ^ 37 * ((K : ℝ) ^ 6 / ε ^ 5) ≤
      2 ^ 39 * ((K : ℝ) + 1) ^ 15 / ((K : ℝ) ^ 4 * ε ^ 8) / 4 := by
    rw [mul_div_assoc', div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have e1 : ε ^ 8 ≤ ε ^ 5 := pow_le_pow_of_le_one hε0.le hε1.le (by norm_num)
    have e2 : (K : ℝ) ^ 10 ≤ ((K : ℝ) + 1) ^ 15 := by
      calc (K : ℝ) ^ 10 ≤ ((K : ℝ) + 1) ^ 10 := by gcongr; linarith
        _ ≤ ((K : ℝ) + 1) ^ 15 := pow_le_pow_right₀ (by linarith) (by norm_num)
    have e3 : 2 ^ 37 * (K : ℝ) ^ 6 * ((K : ℝ) ^ 4 * ε ^ 8 * 4) = 2 ^ 39 * (K : ℝ) ^ 10 * ε ^ 8 := by
      ring
    rw [e3]
    have : 2 ^ 39 * (K : ℝ) ^ 10 * ε ^ 8 ≤ 2 ^ 39 * ((K : ℝ) + 1) ^ 15 * ε ^ 5 := by gcongr
    linarith
  linarith

theorem t2_expo {ε δ : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) {K m B : ℕ} (hK' : (1 : ℝ) ≤ K)
    (hdm : 2 ^ 37 * ((K : ℝ) ^ 6 / ε ^ 5) ≤ δ * m / 4)
    (hB' : (B : ℝ) ≤ 2 ^ 22 * (K : ℝ) ^ 5 / ε ^ 4) :
    1 + 89 * K / ε * B ≤ δ * m / 4 := by
  have h1 : 89 * (K : ℝ) / ε * B ≤ 89 * 2 ^ 22 * ((K : ℝ) ^ 6 / ε ^ 5) := by
    calc 89 * (K : ℝ) / ε * B ≤ 89 * K / ε * (2 ^ 22 * (K : ℝ) ^ 5 / ε ^ 4) := by gcongr
      _ = 89 * 2 ^ 22 * ((K : ℝ) ^ 6 / ε ^ 5) := by
        field_simp
  have h4 : (1 : ℝ) ≤ (K : ℝ) ^ 6 / ε ^ 5 := by
    rw [le_div_iff₀ (by positivity)]
    have : ε ^ 5 ≤ 1 := pow_le_one₀ hε0.le hε1.le
    have : (1 : ℝ) ≤ (K : ℝ) ^ 6 := one_le_pow₀ hK'
    nlinarith
  linarith

theorem t2_combine {ε δ : ℝ} {K m B : ℕ} (hδ1 : δ ≤ 1)
    (hbase : 1 + m * 2 ^ K / (1 - δ / 4) ≤ Real.exp (89 * K / ε))
    (hexpo : 1 + 89 * K / ε * B ≤ δ * m / 4) :
    2 * (1 - δ / 4) ^ m * (1 + m * 2 ^ K / (1 - δ / 4)) ^ B ≤ 1 := by
  have hr : 1 / 2 ≤ 1 - δ / 4 := by linarith
  have ha := t2_geom hδ1 m
  have e2 : (2 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
  have hpos1 : 0 ≤ (1 - δ / 4) ^ m := pow_nonneg (by linarith only [hr]) _
  have h0 : 0 ≤ 1 + m * 2 ^ K / (1 - δ / 4) := by
    have : 0 ≤ m * 2 ^ K / (1 - δ / 4) := div_nonneg (by positivity) (by linarith only [hr])
    linarith only [this]
  have hbB : (1 + m * 2 ^ K / (1 - δ / 4)) ^ B ≤ Real.exp (89 * K / ε * B) := by
    calc (1 + m * 2 ^ K / (1 - δ / 4)) ^ B ≤ Real.exp (89 * K / ε) ^ B :=
          pow_le_pow_left₀ h0 hbase _
      _ = Real.exp (89 * K / ε * B) := by rw [← Real.exp_nat_mul]; ring_nf
  have step1 : 2 * (1 - δ / 4) ^ m ≤ Real.exp 1 * Real.exp (-(δ * m / 4)) :=
    mul_le_mul e2 ha hpos1 (Real.exp_pos _).le
  have step2 : 2 * (1 - δ / 4) ^ m * (1 + m * 2 ^ K / (1 - δ / 4)) ^ B ≤
      Real.exp 1 * Real.exp (-(δ * m / 4)) * Real.exp (89 * K / ε * B) :=
    mul_le_mul step1 hbB (pow_nonneg h0 _) (by positivity)
  have e3 : Real.exp 1 * Real.exp (-(δ * m / 4)) * Real.exp (89 * K / ε * B) =
      Real.exp (1 + -(δ * m / 4) + 89 * K / ε * B) := by rw [Real.exp_add, Real.exp_add]
  rw [e3] at step2
  refine step2.trans ?_
  have hz : 1 + -(δ * m / 4) + 89 * K / ε * B ≤ 0 := by linarith only [hexpo]
  exact (Real.exp_le_exp.2 hz).trans_eq Real.exp_zero

theorem m11V_le {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) {K : ℕ} (hK' : (1 : ℝ) ≤ K) :
    (m11V ε K : ℝ) ≤ 2 ^ 59 * ((K : ℝ) + 1) ^ 15 / ε ^ 12 := by
  have := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 2 ^ 58 * ((K : ℝ) + 1) ^ 15 / ε ^ 12 by positivity)
  have h1 : (1 : ℝ) ≤ 2 ^ 58 * ((K : ℝ) + 1) ^ 15 / ε ^ 12 := by
    rw [le_div_iff₀ (by positivity)]
    have : ε ^ 12 ≤ 1 := pow_le_one₀ hε0.le hε1.le
    have : (1 : ℝ) ≤ ((K : ℝ) + 1) ^ 15 := one_le_pow₀ (by linarith)
    nlinarith
  have e : (2 : ℝ) ^ 59 * ((K : ℝ) + 1) ^ 15 / ε ^ 12 =
      2 * (2 ^ 58 * ((K : ℝ) + 1) ^ 15 / ε ^ 12) := by ring
  unfold m11V; linarith

/-- **Theorem 2 numerics** at `δ = δ11`, `B = B11`, `s = m11V`. -/
theorem thm2_ineq {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) {K : ℕ} (hK : 1 ≤ K) :
    2 * (1 - δ11 ε K / 4) ^ m11V ε K *
      (1 + m11V ε K * 2 ^ K / (1 - δ11 ε K / 4)) ^ B11 ε K ≤ 1 := by
  have hK' : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hδ0 : 0 < δ11 ε K := δ11_pos hε0 hε1 hK
  have hδ1 : δ11 ε K ≤ 1 := δ11_le_one hε0 hε1 hK
  have hδge := δ11_ge hε0 hε1 hK
  have hB : (B11 ε K : ℝ) ≤ 8 * K / δ11 ε K := Nat.floor_le (by positivity)
  have hm1 : (1 : ℝ) ≤ m11V ε K := by
    have := m11V_ge (ε := ε) (K := K)
    have : (1 : ℝ) ≤ 2 ^ 58 * ((K : ℝ) + 1) ^ 15 / ε ^ 12 := by
      rw [le_div_iff₀ (by positivity)]
      have : ε ^ 12 ≤ 1 := pow_le_one₀ hε0.le hε1.le
      have : (1 : ℝ) ≤ ((K : ℝ) + 1) ^ 15 := one_le_pow₀ (by linarith)
      nlinarith
    linarith
  exact t2_combine hδ1 (t2_base hε0 hε1 hK' hδ1 hm1 (m11V_le hε0 hε1 hK'))
    (t2_expo hε0 hε1 hK' (t2_dm hε0 hε1 hK' hδ0 hδge (m11V_ge (ε := ε) (K := K)))
      (t2_rounds hε0 hδ0 hδge hK' hB))

end E34
