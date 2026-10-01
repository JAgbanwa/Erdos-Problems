import E18.Far
import E35.Gate

/-!
# E35 — the far threshold `NE ε` at a generic accuracy `0 < ε ≤ 1/2`

For `0 < ε ≤ 1/2` (i.e. `NfarE η = NE (η/2)` with `0 < η ≤ 1`):

* closed forms `sE ε = ε/4500`, `zqE ε = ε/10`, `1/ε ≤ k0E ε`, `3001 ≤ k0E ε`;
* **`initialBound_eq`**: Mathlib's initial partition size is `k₀ = k0E ε`
  (via `log x ≤ x − 1`);
* `BE_eq`: `BE ε = T·16^T` with `T = stepBound^[hIterE ε] k₀`,
  `hIterE ε = ⌊4/(δ/8)^5⌋`;
* **`NE_le_of_B`**: `NE ε ≤ k₀ + 2208·4500²¹·k₀²¹·B + G3 + 16·4500⁶·k₀⁶·G1·B⁵
  + 50·k₀·(1 + 2 G2) + 1`, with `G1, G2, G3` the gate constants of `E35.Gate` at
  `zq = ε/10`.
-/

namespace E35

open SzemerediRegularity

/-- The regularity iteration count `⌊4/(δ/8)^5⌋` of the RC01 instance at accuracy `ε`. -/
noncomputable def hIterE (ε : ℚ) : ℕ := ⌊(4 : ℝ) / (((E18.δE ε / 8 : ℚ)) : ℝ) ^ 5⌋₊

/-- The real gate slack `zq = zqE ε`. -/
noncomputable def zqR (ε : ℚ) : ℝ := ((E18.zqE ε : ℚ) : ℝ)

variable {ε : ℚ}

theorem sE_eq (h0 : 0 < ε) (h1 : ε ≤ 1 / 2) : E18.sE ε = ε / 4500 := by
  unfold E18.sE; rw [min_eq_left (by linarith)]

theorem zqE_eq (h0 : 0 < ε) (h1 : ε ≤ 1 / 2) : E18.zqE ε = ε / 10 := by
  unfold E18.zqE; rw [min_eq_left (by linarith)]

theorem zqR_eq (h0 : 0 < ε) (h1 : ε ≤ 1 / 2) : zqR ε = (ε : ℝ) / 10 := by
  unfold zqR; rw [zqE_eq h0 h1]; push_cast; ring

theorem δE_eq (h0 : 0 < ε) (h1 : ε ≤ 1 / 2) : E18.δE ε = (ε / 4500) ^ 21 / 2208 := by
  unfold E18.δE; rw [sE_eq h0 h1]; rfl

theorem k0E_ge : 1500 / ε + 1 ≤ (E18.k0E ε : ℚ) := by
  unfold E18.k0E; push_cast; linarith [Nat.le_ceil (1500 / ε)]

theorem inv_le_k0E (h0 : 0 < ε) : 1 / ε ≤ (E18.k0E ε : ℚ) := by
  have := (k0E_ge (ε := ε))
  have : 1 / ε ≤ 1500 / ε := by
    rw [div_le_div_iff_of_pos_right h0]; norm_num
  linarith

theorem k0E_ge_3001 (h0 : 0 < ε) (h1 : ε ≤ 1 / 2) : 3001 ≤ E18.k0E ε := by
  have h := (k0E_ge (ε := ε))
  have : (3000 : ℚ) ≤ 1500 / ε := by rw [le_div_iff₀ h0]; linarith
  have : (3001 : ℚ) ≤ (E18.k0E ε : ℚ) := by linarith
  exact_mod_cast this

/-- The regularity accuracy as a real number. -/
theorem epsReg_eq (h0 : 0 < ε) (h1 : ε ≤ 1 / 2) :
    (((E18.δE ε / 8 : ℚ)) : ℝ) = (ε : ℝ) ^ 21 / (17664 * 4500 ^ 21) := by
  rw [δE_eq h0 h1]; push_cast; ring

theorem epsReg_pos (h0 : 0 < ε) (h1 : ε ≤ 1 / 2) : (0 : ℝ) < (((E18.δE ε / 8 : ℚ)) : ℝ) := by
  rw [epsReg_eq h0 h1]; have : (0 : ℝ) < ε := by exact_mod_cast h0
  positivity

theorem epsReg_le_one (h0 : 0 < ε) (h1 : ε ≤ 1 / 2) : (((E18.δE ε / 8 : ℚ)) : ℝ) ≤ 1 := by
  rw [epsReg_eq h0 h1]
  have e0 : (0 : ℝ) < ε := by exact_mod_cast h0
  have e1 : (ε : ℝ) ≤ 1 := by
    have : (ε : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) := by exact_mod_cast h1
    push_cast at this; linarith
  have : (ε : ℝ) ^ 21 ≤ 1 := pow_le_one₀ e0.le e1
  rw [div_le_one (by positivity)]
  nlinarith

theorem three_le_hIterE (h0 : 0 < ε) (h1 : ε ≤ 1 / 2) : 3 ≤ hIterE ε := by
  unfold hIterE
  have hp := epsReg_pos h0 h1
  have hl := epsReg_le_one h0 h1
  apply Nat.le_floor
  generalize (((E18.δE ε / 8 : ℚ)) : ℝ) = e at hp hl ⊢
  have : e ^ 5 ≤ 1 := pow_le_one₀ hp.le hl
  rw [le_div_iff₀ (by positivity)]
  norm_num
  linarith

set_option exponentiation.threshold 2000 in
/-- **Mathlib's initial partition size is `k₀`**, for every `0 < ε ≤ 1/2`. -/
theorem initialBound_eq (h0 : 0 < ε) (h1 : ε ≤ 1 / 2) :
    initialBound (((E18.δE ε / 8 : ℚ)) : ℝ) (E18.k0E ε) = E18.k0E ε := by
  set e : ℝ := (((E18.δE ε / 8 : ℚ)) : ℝ) with he
  have he' : e = (ε : ℝ) ^ 21 / (17664 * 4500 ^ 21) := epsReg_eq h0 h1
  have e0 : (0 : ℝ) < ε := by exact_mod_cast h0
  have hepos : 0 < e := by rw [he']; positivity
  set u : ℝ := (ε : ℝ)⁻¹ with hu
  have hu0 : 0 < u := inv_pos.2 e0
  have hu2 : 2 ≤ u := by
    have : (ε : ℝ) ≤ 1 / 2 := by
      have : (ε : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) := by exact_mod_cast h1
      push_cast at this; linarith
    rw [hu, le_inv_comm₀ (by norm_num) e0]; linarith
  have hk : 1500 * u + 1 ≤ (E18.k0E ε : ℝ) := by
    have := (k0E_ge (ε := ε))
    have : ((1500 / ε + 1 : ℚ) : ℝ) ≤ ((E18.k0E ε : ℚ) : ℝ) := by exact_mod_cast this
    push_cast at this; rw [hu]; linarith [show (1500 : ℝ) / ε = 1500 * (ε : ℝ)⁻¹ by ring]
  have hX : (100 : ℝ) / e ^ 5 = (100 * (17664 * 4500 ^ 21) ^ 5 : ℝ) * u ^ 105 := by
    rw [he', hu, div_pow, ← pow_mul]; field_simp
  have hC : Real.log (100 * (17664 * 4500 ^ 21) ^ 5 : ℝ) ≤ 1400 * Real.log 2 := by
    have : Real.log (100 * (17664 * 4500 ^ 21) ^ 5 : ℝ) ≤ Real.log ((2 : ℝ) ^ 1400) :=
      Real.log_le_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at this
    push_cast at this
    exact this
  have hlogu : Real.log u ≤ u - 1 := Real.log_le_sub_one_of_pos hu0
  have hlog : Real.log (100 / e ^ 5) / Real.log 4 ≤ (E18.k0E ε : ℝ) - 1 := by
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    have hl2 := Real.log_two_gt_d9
    have hl2' := Real.log_two_lt_d9
    rw [div_le_iff₀ (by rw [h4]; linarith), hX, Real.log_mul (by norm_num) (by positivity),
      Real.log_pow, h4]
    push_cast
    nlinarith
  have hfloor : ⌊Real.log (100 / e ^ 5) / Real.log 4⌋₊ + 1 ≤ E18.k0E ε := by
    have h' : ⌊Real.log (100 / e ^ 5) / Real.log 4⌋₊ ≤ E18.k0E ε - 1 := by
      apply Nat.floor_le_of_le
      have h3 := k0E_ge_3001 h0 h1
      push_cast [Nat.cast_sub (by omega : 1 ≤ E18.k0E ε)]
      exact hlog
    have h3 := k0E_ge_3001 h0 h1
    omega
  rw [initialBound]
  have h2 : 7 ≤ E18.k0E ε := le_trans (by norm_num) (k0E_ge_3001 h0 h1)
  rw [max_eq_left hfloor, max_eq_right h2]

/-- **`BE ε = T·16^T`, `T = stepBound^[hIterE ε] k₀`.** -/
theorem BE_eq (h0 : 0 < ε) (h1 : ε ≤ 1 / 2) :
    E18.BE ε = stepBound^[hIterE ε] (E18.k0E ε) * 16 ^ (stepBound^[hIterE ε] (E18.k0E ε)) := by
  rw [E18.BE, SzemerediRegularity.bound, initialBound_eq h0 h1]
  rfl

set_option maxHeartbeats 1000000 in
/-- **The far threshold in terms of an abstract regularity bound `B`** (generic `ε`). -/
theorem NE_le_of_B (h0 : 0 < ε) (h1 : ε ≤ 1 / 2) :
    E18.NE ε ≤ E18.k0E ε + 2208 * 4500 ^ 21 * E18.k0E ε ^ 21 * E18.BE ε + G3 (zqR ε)
      + 16 * 4500 ^ 6 * E18.k0E ε ^ 6 * G1 (zqR ε) * E18.BE ε ^ 5
      + 50 * E18.k0E ε * (1 + 2 * G2 (zqR ε)) + 1 := by
  unfold E18.NE E18.scaleBoundE E18.massBoundE E18.gammaQE E18.cstE
  have hG1 : (⌈1 / PaperIV.RC01UniformDenseGate.gamE ((E18.zqE ε : ℚ) : ℝ)⌉₊ : ℚ)
      = (G1 (zqR ε) : ℚ) := rfl
  have hG2 : (⌈PaperIV.RC01UniformDenseGate.CstE ((E18.zqE ε : ℚ) : ℝ)⌉₊ : ℚ)
      = (G2 (zqR ε) : ℚ) := rfl
  have hG3 : ⌈(12 + 10 * PaperIV.RC01UniformDenseGate.DE ((E18.zqE ε : ℚ) : ℝ))
      / ((E18.zqE ε : ℚ) : ℝ)⌉₊ = G3 (zqR ε) := rfl
  rw [hG1, hG2, hG3]
  have hk := inv_le_k0E h0
  have hsE := sE_eq h0 h1
  have hδE : E18.δE ε = (E18.sE ε) ^ 21 / 2208 := rfl
  rw [hδE, hsE]
  generalize E18.BE ε = B
  generalize G1 (zqR ε) = g1
  generalize G2 (zqR ε) = g2
  generalize G3 (zqR ε) = g3
  generalize E18.k0E ε = k at hk ⊢
  set s : ℚ := ε / 4500 with hs
  set u : ℚ := 1 / s with hu
  have hs0 : 0 < s := by positivity
  have hsu : s * u = 1 := by rw [hu]; field_simp
  have hu0 : 0 < u := by positivity
  have hs1 : s ≤ 1 := by rw [hs]; linarith
  have hu1 : 1 ≤ u := by rw [hu, le_div_iff₀ hs0]; linarith
  have huk : u ≤ 4500 * k := by
    rw [hu, hs, one_div_div]
    have : 4500 / ε = 4500 * (1 / ε) := by ring
    rw [this]; linarith
  have hk0 : (0 : ℚ) ≤ k := by positivity
  -- term 2
  have t2 : ⌈(B : ℚ) / (s ^ 21 / 2208)⌉₊ ≤ 2208 * 4500 ^ 21 * k ^ 21 * B := by
    apply Nat.ceil_le.2
    have e : (B : ℚ) / (s ^ 21 / 2208) = 2208 * u ^ 21 * B := by
      rw [hu]; field_simp
    rw [e]; push_cast
    have : u ^ 21 ≤ (4500 * k) ^ 21 := pow_le_pow_left₀ hu0.le huk 21
    have hB : (0 : ℚ) ≤ B := by positivity
    rw [mul_pow] at this
    nlinarith
  -- term 4
  have hab : ((s ^ 3 - 3 * (s ^ 21 / 2208)) + (s ^ 6 - 6 * (s ^ 21 / 2208)))
      / ((s ^ 3 - 3 * (s ^ 21 / 2208)) * (s ^ 6 - 6 * (s ^ 21 / 2208))) ≤ 4 * u ^ 6 := by
    set a := s ^ 3 - 3 * (s ^ 21 / 2208) with ha
    set b := s ^ 6 - 6 * (s ^ 21 / 2208) with hb
    have hs15 : s ^ 15 ≤ 1 := pow_le_one₀ hs0.le hs1
    have hs6 : 0 < s ^ 6 := by positivity
    have hs3 : 0 < s ^ 3 := by positivity
    have ha2 : s ^ 3 / 2 ≤ a := by
      have : s ^ 21 = s ^ 3 * s ^ 18 := by ring
      have h18 : s ^ 18 ≤ 1 := pow_le_one₀ hs0.le hs1
      rw [ha, this]; nlinarith
    have hb2 : s ^ 6 / 2 ≤ b := by
      have : s ^ 21 = s ^ 6 * s ^ 15 := by ring
      rw [hb, this]; nlinarith
    have ha0 : 0 < a := by linarith
    have hb0 : 0 < b := by linarith
    have hu3 : (s * u) ^ 3 = 1 := by rw [hsu]; norm_num
    have hu6 : (s * u) ^ 6 = 1 := by rw [hsu]; norm_num
    have hA : 1 ≤ 2 * u ^ 3 * a := by
      have : 2 * u ^ 3 * (s ^ 3 / 2) = (s * u) ^ 3 := by ring
      nlinarith [pow_pos hu0 3]
    have hB' : 1 ≤ 2 * u ^ 6 * b := by
      have : 2 * u ^ 6 * (s ^ 6 / 2) = (s * u) ^ 6 := by ring
      nlinarith [pow_pos hu0 6]
    have hu36 : u ^ 3 ≤ u ^ 6 := pow_le_pow_right₀ hu1 (by norm_num)
    rw [div_le_iff₀ (by positivity)]
    have e1 : a ≤ a * (2 * u ^ 6 * b) := by nlinarith
    have e2 : b ≤ b * (2 * u ^ 3 * a) := by nlinarith
    have e3 : b * (2 * u ^ 3 * a) ≤ b * (2 * u ^ 6 * a) := by
      have : 0 ≤ a * b := by positivity
      nlinarith
    nlinarith
  have t4 : ⌈4 * (B : ℚ) ^ 5 * ((s ^ 3 - 3 * (s ^ 21 / 2208)) + (s ^ 6 - 6 * (s ^ 21 / 2208))) /
        (1 / (g1 : ℚ) * (s ^ 3 - 3 * (s ^ 21 / 2208)) * (s ^ 6 - 6 * (s ^ 21 / 2208)))⌉₊
      ≤ 16 * 4500 ^ 6 * k ^ 6 * g1 * B ^ 5 := by
    apply Nat.ceil_le.2
    set a := s ^ 3 - 3 * (s ^ 21 / 2208) with ha
    set b := s ^ 6 - 6 * (s ^ 21 / 2208) with hb
    rcases Nat.eq_zero_or_pos g1 with hg | hpos
    · rw [hg]; simp
    have hG : (0 : ℚ) < g1 := by exact_mod_cast hpos
    have heq : 4 * (B : ℚ) ^ 5 * (a + b) / (1 / (g1 : ℚ) * a * b)
        = 4 * (B : ℚ) ^ 5 * (g1 : ℚ) * ((a + b) / (a * b)) := by
      field_simp
    rw [heq]
    push_cast
    have hB5 : (0 : ℚ) ≤ 4 * (B : ℚ) ^ 5 * (g1 : ℚ) := by positivity
    have key := mul_le_mul_of_nonneg_left hab hB5
    have hu6 : u ^ 6 ≤ (4500 * k) ^ 6 := pow_le_pow_left₀ hu0.le huk 6
    rw [mul_pow] at hu6
    have : 4 * (B : ℚ) ^ 5 * (g1 : ℚ) * (4 * u ^ 6) ≤
        4 * (B : ℚ) ^ 5 * (g1 : ℚ) * (4 * (4500 ^ 6 * k ^ 6)) :=
      mul_le_mul_of_nonneg_left (by linarith) hB5
    nlinarith
  -- term 5
  have t5 : ⌈50 * (1 + 2 * (g2 : ℚ)) / ε⌉₊ ≤ 50 * k * (1 + 2 * g2) := by
    apply Nat.ceil_le.2
    push_cast
    have e : 50 * (1 + 2 * (g2 : ℚ)) / ε = 50 * (1 + 2 * (g2 : ℚ)) * (1 / ε) := by ring
    rw [e]
    have : (0 : ℚ) ≤ 50 * (1 + 2 * (g2 : ℚ)) := by positivity
    nlinarith
  have hmax : ∀ a b c d e : ℕ, max (max a b) (max c (max d e)) ≤ a + b + c + d + e := by
    intro a b c d e; omega
  refine Nat.add_le_add_right (le_trans (hmax _ _ _ _ _) ?_) 1
  gcongr

end E35
