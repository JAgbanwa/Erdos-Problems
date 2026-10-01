import E33.RemovalReduction

/-!
# E33 — closed forms of the parameters of `Fexp`

With `ε_s = epsS s = 1/(10⁴¹ (s+1)⁸)`:

* `eta0Of (ε_s/2) = ε_s²/64`, `rLoc ε_s = ε_s²/512`,
* `deltaLoc s ε_s = ε_s⁴ / (2¹⁹ (s+1))` (the precision at which `Nedit`, resp. the removal
  functions, are evaluated),
* `etaNF s = etaLoc s ε_s = ε_s²/64 − ε_s⁴/(2¹⁷ (s+1))` (the far margin),
* `N0Of (ε_s/2) = max stabThreshold (16·10¹⁰⁰ (s+1)¹⁶)`, with
  `stabThreshold ≤ tower2 (hIter + 7)`,
* `NTerm s = 10⁵⁰ (s+1)⁸`.
-/

namespace E33

open A4S1.IndepAll

theorem epsS_le (s : ℕ) : epsS s ≤ 1 / 10 ^ 41 := by
  unfold epsS
  have h : (1 : ℚ) ≤ ((s : ℚ) + 1) ^ 8 :=
    one_le_pow₀ (by linarith [(Nat.cast_nonneg s : (0 : ℚ) ≤ s)])
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
  nlinarith

theorem eta0Of_epsS_half (s : ℕ) : eta0Of (epsS s / 2) = epsS s ^ 2 / 64 := by
  have h0 := epsS_pos' s
  have h1 := epsS_le s
  unfold eta0Of
  have hγ : PaperIV.IntegralStability.gamma = 1 / (4 * 10 ^ 16) := by
    norm_num [PaperIV.IntegralStability.gamma, PaperIV.NearH1Calibration.eta]
  rw [hγ]
  have ha : (epsS s / 2) ^ 2 / 16 ≤ epsS s / 2 / 32 := by nlinarith
  have hb : (epsS s / 2) ^ 2 / 16 ≤ 1 / (4 * 10 ^ 16) / 2 := by nlinarith
  rw [min_eq_right ha, min_eq_right hb]
  ring

theorem rLoc_epsS (s : ℕ) : rLoc (epsS s) = epsS s ^ 2 / 512 := by
  have h0 := epsS_pos' s
  have h1 := epsS_le s
  unfold rLoc
  rw [eta0Of_epsS_half]
  have ha : epsS s ^ 2 / 64 / 8 ≤ 1 := by nlinarith
  have hb : epsS s ^ 2 / 64 / 8 ≤ epsS s / 8 := by nlinarith
  rw [min_eq_right ha, min_eq_right (by linarith)]
  ring

theorem deltaLoc_epsS (s : ℕ) :
    deltaLoc s (epsS s) = epsS s ^ 4 / (2 ^ 19 * ((s : ℚ) + 1)) := by
  unfold deltaLoc
  rw [rLoc_epsS]
  have : ((s : ℚ) + 1) ≠ 0 := by positivity
  field_simp
  ring

theorem etaNF_eq (s : ℕ) :
    etaNF s = epsS s ^ 2 / 64 - epsS s ^ 4 / (2 ^ 17 * ((s : ℚ) + 1)) := by
  have hle := etaLoc_le s (epsS_pos' s)
  unfold etaNF
  rw [min_eq_left hle]
  unfold etaLoc
  rw [eta0Of_epsS_half, deltaLoc_epsS]
  have : ((s : ℚ) + 1) ≠ 0 := by positivity
  field_simp
  ring

theorem N0Of_epsS_half (s : ℕ) :
    N0Of (epsS s / 2) = max stabThreshold (16 * 10 ^ 100 * (s + 1) ^ 16) := by
  have hγ : PaperIV.IntegralStability.gamma = 1 / (4 * 10 ^ 16) := by
    norm_num [PaperIV.IntegralStability.gamma, PaperIV.NearH1Calibration.eta]
  have h : (100 : ℚ) / (PaperIV.IntegralStability.gamma * (epsS s / 2) ^ 2) =
      ((16 * 10 ^ 100 * (s + 1) ^ 16 : ℕ) : ℚ) := by
    rw [hγ]; unfold epsS; push_cast
    have : ((s : ℚ) + 1) ≠ 0 := by positivity
    field_simp
    ring
  have hc : ⌈(100 : ℚ) / (PaperIV.IntegralStability.gamma * (epsS s / 2) ^ 2)⌉₊ =
      16 * 10 ^ 100 * (s + 1) ^ 16 := by
    rw [h, Nat.ceil_natCast]
  unfold N0Of
  rw [hc]

theorem NTerm_eq (s : ℕ) : NTerm s = 10 ^ 50 * (s + 1) ^ 8 := by
  unfold NTerm
  have h : (10 : ℚ) ^ 50 * ((s : ℚ) + 1) ^ 8 = ((10 ^ 50 * (s + 1) ^ 8 : ℕ) : ℚ) := by
    push_cast; ring
  rw [h, Nat.ceil_natCast]

/-- **The fully unfolded threshold.**  `F(s) = N₀ + (N₀² + 1)·10⁴¹(s+1)⁸ + 1` with
`N₀ = max (max stabThreshold (16·10¹⁰⁰ (s+1)¹⁶)) (Nedit s (ε_s⁴/(2¹⁹(s+1))))
      + NfarE (ε_s²/64 − ε_s⁴/(2¹⁷(s+1))) + 10⁵⁰ (s+1)⁸ + s + 3`. -/
theorem N0_eq (Nedit : ℕ → ℚ → ℕ) (s : ℕ) :
    N0 Nedit s =
      max (max stabThreshold (16 * 10 ^ 100 * (s + 1) ^ 16))
          (Nedit s (epsS s ^ 4 / (2 ^ 19 * ((s : ℚ) + 1))))
        + E18.NfarE (epsS s ^ 2 / 64 - epsS s ^ 4 / (2 ^ 17 * ((s : ℚ) + 1)))
        + 10 ^ 50 * (s + 1) ^ 8 + s + 3 := by
  unfold N0 NLoc
  rw [N0Of_epsS_half, deltaLoc_epsS, etaNF_eq, NTerm_eq]

end E33
