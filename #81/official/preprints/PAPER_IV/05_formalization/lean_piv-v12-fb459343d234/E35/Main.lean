import E35.Numeric
import E19.Tower

/-!
# E35 — T1: tower bound for the far threshold at every accuracy `0 < η ≤ 1`

* `absorb_gen`: absorption of variable constants `≤ T` into `B^6`, `B = T·16^T`.
* `two_pow_three_le_iterate`: `2^(2^(2^n)) ≤ stepBound^[3] n` (three iterations), so the
  gate constants `Gi ≤ 2^(2^(Kexp k₀))` with `Kexp k₀ = 1793 k₀ + 47 ≤ 2^k₀` are absorbed.
* **`NE_le_tower`**: `NE ε ≤ tower2 (hIterE ε + k0E ε + 4)` for `0 < ε ≤ 1/2`.
* **`NfarE_le_tower`**: `NfarE η ≤ tower2 (hR η + k0E (η/2) + 4)` for `0 < η ≤ 1`,
  `hR η = ⌊4/(δ/8)^5⌋` the regularity iteration count.
* **`NfarE_le_tower_poly`**: `NfarE η ≤ tower2 ⌈cPoly/η^105⌉₊`,
  `cPoly = 4·17664^5·9000^105 + 3006`.
-/

namespace E35

open SzemerediRegularity E19

/-! ## Abstract absorption -/

/-- Absorption, generic form: if `8 ≤ T` and all constants are `≤ T` then the right-hand side
of `NE_le_of_B`, with `B = T·16^T`, is at most `B^6`. -/
theorem absorb_gen (T c0 c1 c2 c3 g1 g2 g3 : ℕ) (hT : 8 ≤ T) (h0 : c0 ≤ T) (h1 : c1 ≤ T)
    (h2 : c2 ≤ T) (h3 : c3 ≤ T) (hg1 : g1 ≤ T) (hg2 : g2 ≤ T) (hg3 : g3 ≤ T) :
    c0 + c1 * (T * 16 ^ T) + g3 + c2 * g1 * (T * 16 ^ T) ^ 5 + c3 * (1 + 2 * g2) + 1
      ≤ (T * 16 ^ T) ^ 6 := by
  have hT1 : 1 ≤ T := le_trans (by norm_num) hT
  have h16 : 4 * T ≤ 16 ^ T :=
    le_trans (four_mul_le_four_pow T hT1) (Nat.pow_le_pow_left (by norm_num) T)
  have hTT : T * (4 * T) ≤ T * 16 ^ T := Nat.mul_le_mul_left T h16
  have h16one : 1 ≤ 16 ^ T := Nat.one_le_pow _ _ (by norm_num)
  have hTB : T ≤ T * 16 ^ T := by nlinarith
  generalize T * 16 ^ T = B at hTT hTB ⊢
  have hB4 : 4 ≤ B := by nlinarith
  have t2 : c1 * B ≤ B * B := Nat.mul_le_mul_right B (le_trans h1 hTB)
  have t4 : c2 * g1 * B ^ 5 ≤ T * T * B ^ 5 := Nat.mul_le_mul_right _ (Nat.mul_le_mul h2 hg1)
  have t4' : 4 * (T * T * B ^ 5) ≤ B ^ 6 := by
    have : 4 * (T * T) ≤ B := by nlinarith
    calc 4 * (T * T * B ^ 5) = 4 * (T * T) * B ^ 5 := by ring
      _ ≤ B * B ^ 5 := Nat.mul_le_mul_right _ this
      _ = B ^ 6 := by ring
  have t5 : c3 * (1 + 2 * g2) ≤ T * (1 + 2 * T) := Nat.mul_le_mul h3 (by omega)
  have t5' : T * (1 + 2 * T) ≤ 3 * (B * B) := by nlinarith
  have hBB : 256 * (B * B) ≤ B ^ 6 := by
    have h4 : 256 ≤ B ^ 4 := by
      calc 256 = 4 ^ 4 := by norm_num
        _ ≤ B ^ 4 := Nat.pow_le_pow_left hB4 4
    calc 256 * (B * B) ≤ B ^ 4 * (B * B) := Nat.mul_le_mul_right _ h4
      _ = B ^ 6 := by ring
  have hB1 : B ≤ B * B := by nlinarith
  omega

/-! ## Three iterations of `stepBound` -/

/-- `2^(2^(2^n)) ≤ stepBound^[3] n` for `n ≥ 1`. -/
theorem two_pow_three_le_iterate (n : ℕ) (hn : 1 ≤ n) :
    2 ^ (2 ^ (2 ^ n)) ≤ stepBound^[3] n := by
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id]
  have h1 := two_pow_le_stepBound n hn
  have h2 := two_pow_le_stepBound (stepBound n) (one_le_stepBound n hn)
  have h3 := two_pow_le_stepBound (stepBound (stepBound n))
    (one_le_stepBound _ (one_le_stepBound n hn))
  calc 2 ^ (2 ^ (2 ^ n)) ≤ 2 ^ (2 ^ stepBound n) :=
        Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_right (by norm_num) h1)
    _ ≤ 2 ^ stepBound (stepBound n) := Nat.pow_le_pow_right (by norm_num) h2
    _ ≤ _ := h3

/-- `2^(2^K) ≤ stepBound^[m] n` whenever `3 ≤ m`, `1 ≤ n`, `K ≤ 2^n`. -/
theorem two_pow_two_pow_le_iterate3 (m n K : ℕ) (hm : 3 ≤ m) (hn : 1 ≤ n) (hK : K ≤ 2 ^ n) :
    2 ^ (2 ^ K) ≤ stepBound^[m] n :=
  le_trans (Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_right (by norm_num) hK))
    (le_trans (two_pow_three_le_iterate n hn) (iterate_stepBound_mono_left n hm))

theorem Kexp_le_two_pow (n : ℕ) (hn : 16 ≤ n) : Kexp n ≤ 2 ^ n := by
  rw [Kexp_eq]
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih => rw [pow_succ]; omega

theorem three_mul_le_two_pow (n : ℕ) (hn : 4 ≤ n) : 3 * n ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih => rw [pow_succ]; omega

/-! ## Admissibility of `β = zq/320` with `L = k₀` -/

theorem adm_k0E {ε : ℚ} (h0 : 0 < ε) (h1 : ε ≤ 1 / 2) :
    E35.Sched.Adm (E18.k0E ε) (zqR ε / 320) := by
  rw [zqR_eq h0 h1]
  have e0 : (0 : ℝ) < ε := by exact_mod_cast h0
  have e1 : (ε : ℝ) ≤ 1 / 2 := by
    have : (ε : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) := by exact_mod_cast h1
    push_cast at this; linarith
  have hk3 := k0E_ge_3001 h0 h1
  have hk : ((1500 / ε + 1 : ℚ) : ℝ) ≤ ((E18.k0E ε : ℚ) : ℝ) := by exact_mod_cast (k0E_ge (ε := ε))
  push_cast at hk
  have h3k : ((3 * E18.k0E ε : ℕ) : ℝ) ≤ ((2 ^ E18.k0E ε : ℕ) : ℝ) := by
    exact_mod_cast three_mul_le_two_pow _ (by omega)
  push_cast at h3k
  refine ⟨?_, by linarith⟩
  rw [inv_le_comm₀ (by positivity) (by positivity)]
  rw [show ((ε : ℝ) / 10 / 320)⁻¹ = 3200 / ε by field_simp; norm_num]
  have : (1500 : ℝ) / ε ≤ E18.k0E ε := by linarith
  have h2 : (3200 : ℝ) / ε ≤ 3 * E18.k0E ε := by
    have e : (3200 : ℝ) / ε = 3200 / 1500 * (1500 / ε) := by field_simp
    rw [e]
    have := mul_le_mul_of_nonneg_left this (show (0 : ℝ) ≤ 3200 / 1500 by norm_num)
    have hk0 : (0 : ℝ) ≤ E18.k0E ε := Nat.cast_nonneg _
    linarith
  linarith

/-! ## Constants of the absorption -/

set_option exponentiation.threshold 400 in
theorem pow_le_two_pow_Kexp_c1 (k : ℕ) (hk : 1 ≤ k) :
    2208 * 4500 ^ 21 * k ^ 21 ≤ 2 ^ Kexp k := by
  have hk2 : k ≤ 2 ^ k := (Nat.lt_two_pow_self).le
  have e1 : 2208 * 4500 ^ 21 ≤ 2 ^ 285 := by norm_num
  have e2 : k ^ 21 ≤ (2 ^ k) ^ 21 := Nat.pow_le_pow_left hk2 21
  calc 2208 * 4500 ^ 21 * k ^ 21 ≤ 2 ^ 285 * (2 ^ k) ^ 21 := Nat.mul_le_mul e1 e2
    _ = 2 ^ (285 + 21 * k) := by rw [← pow_mul, ← pow_add]; ring_nf
    _ ≤ 2 ^ Kexp k := Nat.pow_le_pow_right (by norm_num) (by rw [Kexp_eq]; omega)

theorem pow_le_two_pow_Kexp_c2 (k : ℕ) (hk : 1 ≤ k) :
    16 * 4500 ^ 6 * k ^ 6 ≤ 2 ^ Kexp k := by
  have hk2 : k ≤ 2 ^ k := (Nat.lt_two_pow_self).le
  have e1 : 16 * 4500 ^ 6 ≤ 2 ^ 78 := by norm_num
  have e2 : k ^ 6 ≤ (2 ^ k) ^ 6 := Nat.pow_le_pow_left hk2 6
  calc 16 * 4500 ^ 6 * k ^ 6 ≤ 2 ^ 78 * (2 ^ k) ^ 6 := Nat.mul_le_mul e1 e2
    _ = 2 ^ (78 + 6 * k) := by rw [← pow_mul, ← pow_add]; ring_nf
    _ ≤ 2 ^ Kexp k := Nat.pow_le_pow_right (by norm_num) (by rw [Kexp_eq]; omega)

theorem pow_le_two_pow_Kexp_c3 (k : ℕ) : 50 * k ≤ 2 ^ Kexp k := by
  have hk2 : k ≤ 2 ^ k := (Nat.lt_two_pow_self).le
  calc 50 * k ≤ 2 ^ 6 * 2 ^ k := Nat.mul_le_mul (by norm_num) hk2
    _ = 2 ^ (6 + k) := by rw [← pow_add]
    _ ≤ 2 ^ Kexp k := Nat.pow_le_pow_right (by norm_num) (by rw [Kexp_eq]; omega)

theorem le_two_pow_two_pow (x : ℕ) : x ≤ 2 ^ x := (Nat.lt_two_pow_self).le

/-! ## The tower bound -/

/-- `(T·16^T)^6 ≤ 2^(2^t)` whenever `8 ≤ T` and `4T ≤ t` (copy of `E19.B6_le_two_pow_two_pow`,
restated here to keep the cone small). -/
theorem B6_le (T t : ℕ) (hT : 8 ≤ T) (h : 4 * T ≤ t) : (T * 16 ^ T) ^ 6 ≤ 2 ^ (2 ^ t) := by
  have h1 : T * 16 ^ T ≤ 2 ^ (5 * T) := by
    have hT2 : T ≤ 2 ^ T := (Nat.lt_two_pow_self).le
    have h16 : (16 : ℕ) ^ T = 2 ^ (4 * T) := by rw [pow_mul]; norm_num
    rw [h16, show 5 * T = T + 4 * T by ring, pow_add]
    exact Nat.mul_le_mul_right _ hT2
  have h2 : (T * 16 ^ T) ^ 6 ≤ 2 ^ (30 * T) := by
    calc (T * 16 ^ T) ^ 6 ≤ (2 ^ (5 * T)) ^ 6 := Nat.pow_le_pow_left h1 6
      _ = 2 ^ (30 * T) := by rw [← pow_mul]; ring_nf
  have h8 : ∀ t : ℕ, 6 ≤ t → 8 * t ≤ 2 ^ t := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base => norm_num
    | succ t ht ih => rw [pow_succ]; omega
  have h3 : 30 * T ≤ 2 ^ t := le_trans (by omega) (h8 t (by omega))
  exact le_trans h2 (Nat.pow_le_pow_right (by norm_num) h3)

/-- **T1 in the `ε`-form**: `NE ε ≤ tower2 (hIterE ε + k0E ε + 4)` for `0 < ε ≤ 1/2`. -/
theorem NE_le_tower {ε : ℚ} (h0 : 0 < ε) (h1 : ε ≤ 1 / 2) :
    E18.NE ε ≤ tower2 (hIterE ε + E18.k0E ε + 4) := by
  have hN := NE_le_of_B h0 h1
  rw [BE_eq h0 h1] at hN
  set k := E18.k0E ε with hkdef
  set h := hIterE ε with hhdef
  have hk3 : 3001 ≤ k := k0E_ge_3001 h0 h1
  have hh3 : 3 ≤ h := three_le_hIterE h0 h1
  have hadm := adm_k0E h0 h1
  rw [← hkdef] at hadm
  have hz0 : 0 < zqR ε := by
    rw [zqR_eq h0 h1]; have : (0 : ℝ) < ε := by exact_mod_cast h0
    positivity
  have hz1 : zqR ε ≤ 1 := by
    rw [zqR_eq h0 h1]
    have : (ε : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) := by exact_mod_cast h1
    push_cast at this; linarith
  set T := stepBound^[h] k with hTdef
  set D := 2 ^ (2 ^ Kexp k) with hD
  have hDT : D ≤ T := two_pow_two_pow_le_iterate3 h k (Kexp k) hh3 (by omega)
    (Kexp_le_two_pow k (by omega))
  have hKD : 2 ^ Kexp k ≤ D := le_two_pow_two_pow _
  have hK8 : 8 ≤ 2 ^ Kexp k :=
    le_trans (by norm_num : 8 ≤ 2 ^ 3) (Nat.pow_le_pow_right (by norm_num)
      (by rw [Kexp_eq]; omega))
  have hkK : k ≤ 2 ^ Kexp k :=
    le_trans (le_two_pow_two_pow k) (Nat.pow_le_pow_right (by norm_num) (by rw [Kexp_eq]; omega))
  have habs := absorb_gen T k (2208 * 4500 ^ 21 * k ^ 21) (16 * 4500 ^ 6 * k ^ 6) (50 * k)
    (G1 (zqR ε)) (G2 (zqR ε)) (G3 (zqR ε)) (by omega) (by omega)
    (le_trans (pow_le_two_pow_Kexp_c1 k (by omega)) (by omega))
    (le_trans (pow_le_two_pow_Kexp_c2 k (by omega)) (by omega))
    (le_trans (pow_le_two_pow_Kexp_c3 k) (by omega))
    (le_trans (G1_le hz0 hadm) hDT) (le_trans (G2_le hz0 hadm) hDT)
    (le_trans (G3_le hz0 hz1 hadm) hDT)
  have h4T : 4 * T ≤ tower2 (h + (k + 2)) :=
    four_mul_iterate_le_tower2 h k (k + 2) (by omega) (four_mul_le_tower2_add_two k)
  have hB6 := B6_le T (tower2 (h + (k + 2))) (by omega) h4T
  have ht : tower2 (h + k + 4) = 2 ^ (2 ^ tower2 (h + (k + 2))) := by
    rw [show h + k + 4 = (h + (k + 2)) + 1 + 1 by ring, tower2_succ, tower2_succ]
  rw [ht]
  exact le_trans hN (le_trans habs hB6)

/-- The regularity iteration count of the far instance at margin `η`: `hR η = ⌊4/(δ/8)^5⌋`
with `δ = δE (η/2)`. -/
noncomputable def hR (η : ℚ) : ℕ := hIterE (η / 2)

/-- **T1: `NfarE η ≤ tower2 (hR η + k0E (η/2) + 4)` for every `0 < η ≤ 1`.** -/
theorem NfarE_le_tower (η : ℚ) (h0 : 0 < η) (h1 : η ≤ 1) :
    E18.NfarE η ≤ tower2 (hR η + E18.k0E (η / 2) + 4) :=
  NE_le_tower (by positivity) (by linarith)

/-! ## Polynomial height -/

/-- The constant of the polynomial height: `cPoly = 4·17664^5·9000^105 + 3006`. -/
def cPoly : ℕ := 4 * 17664 ^ 5 * 9000 ^ 105 + 3006

theorem hR_le (η : ℚ) (h0 : 0 < η) (h1 : η ≤ 1) :
    (hR η : ℝ) ≤ (4 * 17664 ^ 5 * 9000 ^ 105 : ℝ) / (η : ℝ) ^ 105 := by
  unfold hR hIterE
  have e := epsReg_eq (ε := η / 2) (by positivity) (by linarith)
  have hp := epsReg_pos (ε := η / 2) (by positivity) (by linarith)
  refine le_trans (Nat.floor_le (by positivity)) (le_of_eq ?_)
  rw [e]
  have : (0 : ℝ) < η := by exact_mod_cast h0
  push_cast
  field_simp
  ring

theorem k0E_half_le (η : ℚ) (h0 : 0 < η) : (E18.k0E (η / 2) : ℝ) ≤ 3000 / (η : ℝ) + 2 := by
  unfold E18.k0E
  have e0 : (0 : ℚ) < η / 2 := by positivity
  have := Nat.ceil_lt_add_one (show (0 : ℚ) ≤ 1500 / (η / 2) by positivity)
  have e : (1500 : ℚ) / (η / 2) = 3000 / η := by field_simp; ring
  rw [e] at this
  have h' : ((⌈(1500 / (η / 2) : ℚ)⌉₊ : ℚ) : ℝ) < ((3000 / η + 1 : ℚ) : ℝ) := by
    rw [e]; exact_mod_cast this
  push_cast at h' ⊢
  linarith

/-- **T1, polynomial form: `NfarE η ≤ tower2 ⌈cPoly/η^105⌉₊`** for `0 < η ≤ 1`. -/
theorem NfarE_le_tower_poly (η : ℚ) (h0 : 0 < η) (h1 : η ≤ 1) :
    E18.NfarE η ≤ tower2 ⌈(cPoly : ℝ) / (η : ℝ) ^ 105⌉₊ := by
  refine le_trans (NfarE_le_tower η h0 h1) (tower2_mono ?_)
  have e0 : (0 : ℝ) < η := by exact_mod_cast h0
  have e1 : (η : ℝ) ≤ 1 := by exact_mod_cast h1
  have hp : (η : ℝ) ^ 105 ≤ 1 := pow_le_one₀ e0.le e1
  have hp0 : 0 < (η : ℝ) ^ 105 := by positivity
  have hq : (η : ℝ) ^ 105 ≤ η := by
    calc (η : ℝ) ^ 105 = (η : ℝ) * (η : ℝ) ^ 104 := by ring
      _ ≤ (η : ℝ) * 1 := mul_le_mul_of_nonneg_left (pow_le_one₀ e0.le e1) e0.le
      _ = (η : ℝ) := mul_one _
  have a1 := hR_le η h0 h1
  have a2 := k0E_half_le η h0
  have b1 : 3000 / (η : ℝ) ≤ 3000 / (η : ℝ) ^ 105 :=
    div_le_div_of_nonneg_left (by norm_num) hp0 hq
  have b2 : (6 : ℝ) ≤ 6 / (η : ℝ) ^ 105 := by rw [le_div_iff₀ hp0]; nlinarith
  apply (Nat.cast_le (α := ℝ)).1
  refine le_trans ?_ (Nat.le_ceil _)
  have hc : (cPoly : ℝ) / (η : ℝ) ^ 105 = (4 * 17664 ^ 5 * 9000 ^ 105 : ℝ) / (η : ℝ) ^ 105
      + 3000 / (η : ℝ) ^ 105 + 6 / (η : ℝ) ^ 105 := by
    unfold cPoly; push_cast; ring
  push_cast
  rw [hc]
  linarith

end E35
