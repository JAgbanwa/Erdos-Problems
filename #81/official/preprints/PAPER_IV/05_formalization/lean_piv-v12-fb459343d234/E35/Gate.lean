import E18.Gate
import E35.Sched

/-!
# E35 — the dense-gate constants at a generic gate slack `zq`

Generic version of `E19/GateBounds.lean`.  For `0 < zq ≤ 1` the dense gate uses
`gamQ 6 (zq/4) (zq/20) = gamR 6 β` with `β = zq/320`.  If `2^(-L) ≤ β` then, with
`W = E35.Sched.W L`:

* `G1 zq = ⌈1/gamE zq⌉ ≤ 2^(W+2)`, `G2 zq = ⌈CstE zq⌉ ≤ 2^(W+3)`,
  `G3 zq = ⌈(12 + 10 DE zq)/zq⌉ ≤ 2^(W+L+9)`;
* `W + L + 9 ≤ 2^(Kexp L)`, `Kexp L = 2 A + L + 11 = 1793 L + 47`, hence
  **`Gi zq ≤ 2^(2^(Kexp L))`**.
-/

namespace E35

open E18.Nib E35.Sched

/-- `G₁ = ⌈1/gamE zq⌉`. -/
noncomputable def G1 (zq : ℝ) : ℕ := ⌈1 / PaperIV.RC01UniformDenseGate.gamE zq⌉₊
/-- `G₂ = ⌈CstE zq⌉`. -/
noncomputable def G2 (zq : ℝ) : ℕ := ⌈PaperIV.RC01UniformDenseGate.CstE zq⌉₊
/-- `G₃ = ⌈(12 + 10 DE zq)/zq⌉`. -/
noncomputable def G3 (zq : ℝ) : ℕ :=
  ⌈(12 + 10 * PaperIV.RC01UniformDenseGate.DE zq) / zq⌉₊

/-- The double-exponential exponent of the gate constants, `Kexp L = 2 A + L + 11`. -/
def Kexp (L : ℕ) : ℕ := 2 * A L + L + 11

theorem Kexp_eq (L : ℕ) : Kexp L = 1793 * L + 47 := by unfold Kexp; rw [A_eq]; ring

namespace GateG

variable {L : ℕ} {zq : ℝ}

theorem bQ_eq (hz : 0 < zq) : PaperIV.MarkedQuotaSlackGate.bQ (zq / 4) (zq / 20) = zq / 40 := by
  unfold PaperIV.MarkedQuotaSlackGate.bQ
  rw [min_eq_right (by linarith)]
  ring

theorem bLE_eq : Nibble.bLE 7 (zq / 40) = zq / 320 := by
  unfold Nibble.bLE; norm_num; ring

theorem gamQ_eq (hz : 0 < zq) :
    PaperIV.MarkedQuotaSlackGate.gamQ 6 (zq / 4) (zq / 20) = gamR 6 (zq / 320) := by
  unfold PaperIV.MarkedQuotaSlackGate.gamQ
  rw [bQ_eq hz]
  unfold Nibble.γE
  rw [show (6 + 1 : ℕ) - 1 = 6 by rfl, show (6 + 1 : ℕ) = 7 by rfl, bLE_eq]
  exact min_eq_left gamR_le_one

theorem gamQ_ge (hz : 0 < zq) (h : Adm L (zq / 320)) : ((2 : ℝ) ^ W L)⁻¹
    ≤ PaperIV.MarkedQuotaSlackGate.gamQ 6 (zq / 4) (zq / 20) := by
  rw [gamQ_eq hz]; exact gamR_ge h

theorem gamQ_pos (hz : 0 < zq) (h : Adm L (zq / 320)) :
    0 < PaperIV.MarkedQuotaSlackGate.gamQ 6 (zq / 4) (zq / 20) := by
  rw [gamQ_eq hz]; exact gamR_pos h

theorem inv_gamQ_le (hz : 0 < zq) (h : Adm L (zq / 320)) :
    (PaperIV.MarkedQuotaSlackGate.gamQ 6 (zq / 4) (zq / 20))⁻¹ ≤ 2 ^ W L :=
  E19.Sched.inv_le_of_lb (gamQ_ge hz h)

end GateG

open GateG

variable {L : ℕ} {zq : ℝ}

theorem G1_le_pow (hz : 0 < zq) (h : Adm L (zq / 320)) : G1 zq ≤ 2 ^ (W L + 2) := by
  unfold G1 PaperIV.RC01UniformDenseGate.gamE PaperIV.RC01MarkedRounding.gamZ
  apply Nat.ceil_le.2
  have h' := inv_gamQ_le hz h
  have hpos := gamQ_pos hz h
  push_cast
  rw [one_div_div, pow_add, div_eq_mul_inv]
  have := E19.Sched.one_le_two_pow (W L)
  norm_num
  linarith

theorem G2_le_pow (hz : 0 < zq) (h : Adm L (zq / 320)) : G2 zq ≤ 2 ^ (W L + 3) := by
  unfold G2 PaperIV.RC01UniformDenseGate.CstE PaperIV.RC01MarkedRounding.CZ
  apply Nat.ceil_le.2
  have h' := inv_gamQ_le hz h
  have hpos := gamQ_pos hz h
  push_cast
  rw [pow_add, div_eq_mul_inv]
  have := E19.Sched.one_le_two_pow (W L)
  norm_num
  linarith

theorem DE_le (hz : 0 < zq) (hz1 : zq ≤ 1) (h : Adm L (zq / 320)) :
    PaperIV.RC01UniformDenseGate.DE zq ≤ 10 * 2 ^ W L + 28 := by
  unfold PaperIV.RC01UniformDenseGate.DE PaperIV.RC01MarkedRounding.DZ
    PaperIV.MarkedQuotaSlackGate.CQ PaperIV.MarkedQuotaSlackGate.kQ
  rw [bQ_eq hz]
  unfold Nibble.CE
  rw [show (6 + 1 : ℕ) - 1 = 6 by rfl, show (6 + 1 : ℕ) = 7 by rfl, bLE_eq]
  have hR : (gamR 6 (zq / 320))⁻¹ ≤ 2 ^ W L := E19.Sched.inv_le_of_lb (gamR_ge h)
  have hQ := inv_gamQ_le hz h
  have hQpos := gamQ_pos hz h
  have hk : (⌈(1 : ℝ) / PaperIV.MarkedQuotaSlackGate.gamQ 6 (zq / 4) (zq / 20)⌉₊ : ℝ)
      ≤ 2 ^ W L + 1 := by
    have := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 1 / PaperIV.MarkedQuotaSlackGate.gamQ 6
      (zq / 4) (zq / 20) by positivity)
    rw [one_div] at this ⊢
    linarith
  have hk0 : (0 : ℝ) ≤ (⌈(1 : ℝ) / PaperIV.MarkedQuotaSlackGate.gamQ 6 (zq / 4)
      (zq / 20)⌉₊ : ℝ) := Nat.cast_nonneg _
  rw [one_div (gamR 6 (zq / 320))]
  push_cast
  have hRpos : 0 ≤ (gamR 6 (zq / 320))⁻¹ := inv_nonneg.2 (gamR_pos h).le
  have hb : zq / 320 * 7 * ((gamR 6 (zq / 320))⁻¹ + 3) ≤ 7 * ((gamR 6 (zq / 320))⁻¹ + 3) := by
    have h0 : 0 ≤ 7 * ((gamR 6 (zq / 320))⁻¹ + 3) := by positivity
    have : zq / 320 ≤ 1 := by linarith
    nlinarith
  have hk' : zq / 40 * (2 + 2 * (⌈(1 : ℝ) / PaperIV.MarkedQuotaSlackGate.gamQ 6
      (zq / 4) (zq / 20)⌉₊ : ℝ)) ≤ 2 + 2 * (2 ^ W L + 1) := by
    have h0 : 0 ≤ 2 + 2 * (⌈(1 : ℝ) / PaperIV.MarkedQuotaSlackGate.gamQ 6
      (zq / 4) (zq / 20)⌉₊ : ℝ) := by positivity
    have : zq / 40 ≤ 1 := by linarith
    nlinarith
  linarith

theorem G3_le_pow (hz : 0 < zq) (hz1 : zq ≤ 1) (h : Adm L (zq / 320)) :
    G3 zq ≤ 2 ^ (W L + L + 9) := by
  unfold G3
  apply Nat.ceil_le.2
  have hD := DE_le hz hz1 h
  have h1 := E19.Sched.one_le_two_pow (W L)
  have hinv : zq⁻¹ ≤ 2 ^ L := by
    have := h.inv_le
    have e : (zq / 320)⁻¹ = 320 * zq⁻¹ := by field_simp
    rw [e] at this
    have : 0 ≤ zq⁻¹ := inv_nonneg.2 hz.le
    linarith
  have hnum : 12 + 10 * PaperIV.RC01UniformDenseGate.DE zq ≤ 392 * 2 ^ W L := by linarith
  push_cast
  rw [div_eq_mul_inv]
  have hRHS : (392 * 2 ^ W L) * 2 ^ L ≤ (2 : ℝ) ^ (W L + L + 9) := by
    rw [pow_add, pow_add]
    have : (0 : ℝ) ≤ 2 ^ W L * 2 ^ L := by positivity
    nlinarith
  rcases le_total 0 (12 + 10 * PaperIV.RC01UniformDenseGate.DE zq) with hn | hn
  · exact le_trans (mul_le_mul hnum hinv (inv_nonneg.2 hz.le) (by positivity)) hRHS
  · have : (12 + 10 * PaperIV.RC01UniformDenseGate.DE zq) * zq⁻¹ ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hn (inv_nonneg.2 hz.le)
    exact le_trans this (by positivity)

theorem W_add_le (L : ℕ) : W L + L + 9 ≤ 2 ^ Kexp L := by
  have hY : 2 ^ (2 * A L + L + 11) = 2 * Ybig L := by
    rw [Ybig, show 2 * A L + L + 11 = (2 * A L + L + 10) + 1 by ring, pow_succ]; ring
  have h1 : Zc L + L + 17 ≤ 2 ^ (2 * A L + L + 10) := by
    have := four_mul_le_two_pow_of_four_le (2 * A L + L + 10) (by omega)
    unfold Zc B0
    rw [A_eq] at this ⊢
    omega
  unfold Kexp W
  rw [hY, Ybig]
  omega

theorem G1_le (hz : 0 < zq) (h : Adm L (zq / 320)) : G1 zq ≤ 2 ^ (2 ^ Kexp L) :=
  le_trans (G1_le_pow hz h) (Nat.pow_le_pow_right (by norm_num)
    (le_trans (by omega) (W_add_le L)))

theorem G2_le (hz : 0 < zq) (h : Adm L (zq / 320)) : G2 zq ≤ 2 ^ (2 ^ Kexp L) :=
  le_trans (G2_le_pow hz h) (Nat.pow_le_pow_right (by norm_num)
    (le_trans (by omega) (W_add_le L)))

theorem G3_le (hz : 0 < zq) (hz1 : zq ≤ 1) (h : Adm L (zq / 320)) :
    G3 zq ≤ 2 ^ (2 ^ Kexp L) :=
  le_trans (G3_le_pow hz hz1 h) (Nat.pow_le_pow_right (by norm_num) (W_add_le L))

end E35
