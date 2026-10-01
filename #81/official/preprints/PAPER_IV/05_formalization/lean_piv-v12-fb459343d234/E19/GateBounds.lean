import E18.Numeric
import E19.ChainBounds

/-!
# E19 — numerical bounds for the far-instance gate constants `G1`, `G2`, `G3`

At `zq₀ = 1/(2·10^17)` the dense gate uses `gamQ 6 (zq₀/4) (zq₀/20) = γE 7 b` with
`b = bQ (zq₀/4) (zq₀/20) = zq₀/40 = 1/(8·10^18)`, hence `gamR 6 (b/8) = gamR 6 β₀`.
With `W = Wexp = Ybig + Zc + 8` (`E19.ChainBounds`):

* `2^(-W) ≤ gamQ 6 (zq₀/4) (zq₀/20) ≤ 1`;
* `G1 ≤ 2^(W+2)`, `G2 ≤ 2^(W+3)`, `G3 ≤ 2^(W+67)`;
* `W + 67 ≤ 2^K` with `K = K1 = K2 = K3 = 59517`, hence **`Gi ≤ 2^(2^Ki)`**.
-/

namespace E19

open E18.Nib E19.Sched

/-- The exponent `K1 = 59517` of the bound `G1 ≤ 2^(2^K1)`. -/
irreducible_def K1 : ℕ := 59517
/-- The exponent `K2 = 59517` of the bound `G2 ≤ 2^(2^K2)`. -/
irreducible_def K2 : ℕ := 59517
/-- The exponent `K3 = 59517` of the bound `G3 ≤ 2^(2^K3)`. -/
irreducible_def K3 : ℕ := 59517

theorem K1_eq : K1 = 59517 := K1_def
theorem K2_eq : K2 = 59517 := K2_def
theorem K3_eq : K3 = 59517 := K3_def

namespace GateB

/-- The gate slack as a real number. -/
theorem zq0_eq : E18.Numeric.zq0 = 1 / (2 * 10 ^ 17) := by
  rw [E18.Numeric.zq0]; push_cast; ring

/-- `bQ (zq₀/4) (zq₀/20) = 1/(8·10^18)`. -/
theorem bQ_eq : PaperIV.MarkedQuotaSlackGate.bQ (E18.Numeric.zq0 / 4) (E18.Numeric.zq0 / 20)
    = 1 / (8 * 10 ^ 18) := by
  unfold PaperIV.MarkedQuotaSlackGate.bQ
  rw [zq0_eq]
  norm_num

theorem bLE_eq : Nibble.bLE 7 (1 / (8 * 10 ^ 18)) = beta0 := by
  unfold Nibble.bLE beta0; norm_num

/-- `gamQ 6 (zq₀/4) (zq₀/20) = gamR 6 β₀`. -/
theorem gamQ_eq : PaperIV.MarkedQuotaSlackGate.gamQ 6 (E18.Numeric.zq0 / 4) (E18.Numeric.zq0 / 20)
    = gamR 6 beta0 := by
  unfold PaperIV.MarkedQuotaSlackGate.gamQ
  rw [bQ_eq]
  unfold Nibble.γE
  rw [show (6 + 1 : ℕ) - 1 = 6 by rfl, show (6 + 1 : ℕ) = 7 by rfl, bLE_eq]
  exact min_eq_left gamR_le_one

/-- **`2^(-W) ≤ gamQ 6 (zq₀/4) (zq₀/20)`**. -/
theorem gamQ_ge : ((2 : ℝ) ^ Wexp)⁻¹
    ≤ PaperIV.MarkedQuotaSlackGate.gamQ 6 (E18.Numeric.zq0 / 4) (E18.Numeric.zq0 / 20) := by
  rw [gamQ_eq]; exact gamR_ge

theorem gamQ_pos :
    0 < PaperIV.MarkedQuotaSlackGate.gamQ 6 (E18.Numeric.zq0 / 4) (E18.Numeric.zq0 / 20) := by
  rw [gamQ_eq]; exact gamR_pos

theorem inv_gamQ_le :
    (PaperIV.MarkedQuotaSlackGate.gamQ 6 (E18.Numeric.zq0 / 4) (E18.Numeric.zq0 / 20))⁻¹
      ≤ 2 ^ Wexp := inv_le_of_lb gamQ_ge

end GateB

open GateB

/-- **`G1 ≤ 2^(W+2)`**. -/
theorem G1_le_pow : E18.Numeric.G1 ≤ 2 ^ (Wexp + 2) := by
  unfold E18.Numeric.G1 PaperIV.RC01UniformDenseGate.gamE PaperIV.RC01MarkedRounding.gamZ
  apply Nat.ceil_le.2
  have h := inv_gamQ_le
  have hpos := gamQ_pos
  push_cast
  rw [one_div_div, pow_add, div_eq_mul_inv]
  have := one_le_two_pow Wexp
  norm_num
  linarith

/-- **`G2 ≤ 2^(W+3)`**. -/
theorem G2_le_pow : E18.Numeric.G2 ≤ 2 ^ (Wexp + 3) := by
  unfold E18.Numeric.G2 PaperIV.RC01UniformDenseGate.CstE PaperIV.RC01MarkedRounding.CZ
  apply Nat.ceil_le.2
  have h := inv_gamQ_le
  have hpos := gamQ_pos
  push_cast
  rw [pow_add, div_eq_mul_inv]
  have := one_le_two_pow Wexp
  norm_num
  linarith

/-- **`DE zq₀ ≤ 10·2^W + 28`**. -/
theorem DE_le : PaperIV.RC01UniformDenseGate.DE E18.Numeric.zq0 ≤ 10 * 2 ^ Wexp + 28 := by
  unfold PaperIV.RC01UniformDenseGate.DE PaperIV.RC01MarkedRounding.DZ
    PaperIV.MarkedQuotaSlackGate.CQ PaperIV.MarkedQuotaSlackGate.kQ
  rw [bQ_eq]
  unfold Nibble.CE
  rw [show (6 + 1 : ℕ) - 1 = 6 by rfl, show (6 + 1 : ℕ) = 7 by rfl, bLE_eq]
  have hR : (gamR 6 beta0)⁻¹ ≤ 2 ^ Wexp := inv_le_of_lb gamR_ge
  have hQ := inv_gamQ_le
  have hQpos := gamQ_pos
  have hk : (⌈(1 : ℝ) / PaperIV.MarkedQuotaSlackGate.gamQ 6 (E18.Numeric.zq0 / 4)
      (E18.Numeric.zq0 / 20)⌉₊ : ℝ) ≤ 2 ^ Wexp + 1 := by
    have := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 1 / PaperIV.MarkedQuotaSlackGate.gamQ 6
      (E18.Numeric.zq0 / 4) (E18.Numeric.zq0 / 20) by positivity)
    rw [one_div] at this ⊢
    linarith
  have hk0 : (0 : ℝ) ≤ (⌈(1 : ℝ) / PaperIV.MarkedQuotaSlackGate.gamQ 6 (E18.Numeric.zq0 / 4)
      (E18.Numeric.zq0 / 20)⌉₊ : ℝ) := Nat.cast_nonneg _
  rw [one_div (gamR 6 beta0)]
  push_cast
  have hRpos : 0 ≤ (gamR 6 beta0)⁻¹ := inv_nonneg.2 gamR_pos.le
  have hb : beta0 * 7 * ((gamR 6 beta0)⁻¹ + 3) ≤ 7 * ((gamR 6 beta0)⁻¹ + 3) := by
    have := beta0_lt_one
    have h0 : 0 ≤ 7 * ((gamR 6 beta0)⁻¹ + 3) := by positivity
    nlinarith
  have hk' : 1 / (8 * 10 ^ 18) * (2 + 2 * (⌈(1 : ℝ) / PaperIV.MarkedQuotaSlackGate.gamQ 6
      (E18.Numeric.zq0 / 4) (E18.Numeric.zq0 / 20)⌉₊ : ℝ)) ≤ 2 + 2 * (2 ^ Wexp + 1) := by
    have h0 : 0 ≤ 2 + 2 * (⌈(1 : ℝ) / PaperIV.MarkedQuotaSlackGate.gamQ 6
      (E18.Numeric.zq0 / 4) (E18.Numeric.zq0 / 20)⌉₊ : ℝ) := by positivity
    nlinarith
  linarith

/-- **`G3 ≤ 2^(W+67)`**. -/
theorem G3_le_pow : E18.Numeric.G3 ≤ 2 ^ (Wexp + 67) := by
  unfold E18.Numeric.G3
  apply Nat.ceil_le.2
  have hD := DE_le
  have h1 := one_le_two_pow Wexp
  push_cast
  rw [pow_add]
  have h2 : (2 * 10 ^ 17 : ℝ) * 392 ≤ 2 ^ 67 := by norm_num
  nlinarith

/-- `W + 67 ≤ 2^59517`. -/
theorem Wexp_add_le : Wexp + 67 ≤ 2 ^ 59517 := by
  have h31 : 2 ^ 31 ≤ 2 ^ (A0 + 31) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hZ : Zc + 75 ≤ 2 ^ 31 := by rw [Zc_def]; norm_num [A0, Ae, B0]
  have hK : (2 : ℕ) ^ 59517 = 2 * 2 ^ (A0 + 31) := by
    rw [show 59517 = (A0 + 31) + 1 by rfl, pow_succ']
  rw [Wexp_def, Ybig_def, hK]
  generalize 2 ^ (A0 + 31) = Y at h31 ⊢
  omega

/-- **G1 numerical bound: `G1 = ⌈1/gamE zq₀⌉ ≤ 2^(2^K1)`, `K1 = 59517`.** -/
theorem G1_le : E18.Numeric.G1 ≤ 2 ^ (2 ^ K1) := by
  rw [K1_def]
  exact le_trans G1_le_pow (Nat.pow_le_pow_right (by norm_num) (le_trans (by omega) Wexp_add_le))

/-- **G2 numerical bound: `G2 = ⌈CstE zq₀⌉ ≤ 2^(2^K2)`, `K2 = 59517`.** -/
theorem G2_le : E18.Numeric.G2 ≤ 2 ^ (2 ^ K2) := by
  rw [K2_def]
  exact le_trans G2_le_pow (Nat.pow_le_pow_right (by norm_num) (le_trans (by omega) Wexp_add_le))

/-- **G3 numerical bound: `G3 = ⌈2·10^17(12+10·DE zq₀)⌉ ≤ 2^(2^K3)`, `K3 = 59517`.** -/
theorem G3_le : E18.Numeric.G3 ≤ 2 ^ (2 ^ K3) := by
  rw [K3_def]
  exact le_trans G3_le_pow (Nat.pow_le_pow_right (by norm_num) Wexp_add_le)

end E19
