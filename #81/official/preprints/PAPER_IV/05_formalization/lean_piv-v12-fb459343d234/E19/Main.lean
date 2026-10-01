import E19.GateBounds
import E19.Tower

/-!
# E19 — absorption of the gate constants and the tower statement

* `E19.NfarE_eta0_le_clean : NfarE η₀ ≤ Bnum ^ 6`, `Bnum = Tnum · 16^Tnum`,
  `Tnum = stepBound^[hIter] (3·10^19+1)`.  The gate constants `G1, G2, G3 ≤ 2^(2^59517)`
  are absorbed because already `stepBound^[2] k₀ ≥ 2^(2^k₀)`.
* `E19.NfarE_eta0_le_tower : NfarE η₀ ≤ tower2 (hIter + 7)`.
* `E19.farRegime_eta0_tower`: Corollary 3.5 at `η₀ = 10⁻¹⁶` for every `n ≥ tower2 (hIter + 7)`.

`hIter` is never evaluated in a way that matters: it only appears symbolically as an
iteration count / tower height, apart from the single check `2 ≤ hIter`.
-/

namespace E19

open SzemerediRegularity E18.Numeric

/-! ## Abstract absorption -/

set_option exponentiation.threshold 2100 in
/-- Absorption, abstract form: if `2^2000 ≤ T` and `g₁, g₂, g₃ ≤ T` then the right-hand side
of `E18.Numeric.NfarE_eta0_le`, with `B = T·16^T`, is at most `B^6`. -/
theorem absorb_abstract (T g1 g2 g3 : ℕ) (hT : 2 ^ 2000 ≤ T) (h1 : g1 ≤ T) (h2 : g2 ≤ T)
    (h3 : g3 ≤ T) :
    k0num + 2208 * (9 * 10 ^ 19) ^ 21 * (T * 16 ^ T) + g3
      + 8 * (9 * 10 ^ 19) ^ 6 * g1 * (T * 16 ^ T) ^ 5 + 10 ^ 18 * (1 + 2 * g2) + 1
      ≤ (T * 16 ^ T) ^ 6 := by
  have hc1 : 2208 * (9 * 10 ^ 19) ^ 21 ≤ T := le_trans (by norm_num) hT
  have hc2 : 8 * (9 * 10 ^ 19) ^ 6 ≤ T := le_trans (by norm_num) hT
  have hk0 : k0num ≤ T := le_trans (by norm_num [k0num]) hT
  have h18 : 10 ^ 18 ≤ T := le_trans (by norm_num) hT
  have hT1 : 1 ≤ T := le_trans (by norm_num) hT
  have h16 : 4 * T ≤ 16 ^ T :=
    le_trans (four_mul_le_four_pow T hT1) (Nat.pow_le_pow_left (by norm_num) T)
  have hTT : T * (4 * T) ≤ T * 16 ^ T := Nat.mul_le_mul_left T h16
  have h16one : 1 ≤ 16 ^ T := Nat.one_le_pow _ _ (by norm_num)
  have hTB : T ≤ T * 16 ^ T := by nlinarith
  generalize T * 16 ^ T = B at hTT hTB ⊢
  have hB4 : 4 ≤ B := by nlinarith
  -- the five terms
  have t2 : 2208 * (9 * 10 ^ 19) ^ 21 * B ≤ B * B :=
    Nat.mul_le_mul_right B (le_trans hc1 hTB)
  have t4 : 8 * (9 * 10 ^ 19) ^ 6 * g1 * B ^ 5 ≤ T * T * B ^ 5 :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul hc2 h1)
  have t4' : 4 * (T * T * B ^ 5) ≤ B ^ 6 := by
    have : 4 * (T * T) ≤ B := by nlinarith
    calc 4 * (T * T * B ^ 5) = 4 * (T * T) * B ^ 5 := by ring
      _ ≤ B * B ^ 5 := Nat.mul_le_mul_right _ this
      _ = B ^ 6 := by ring
  have t5 : 10 ^ 18 * (1 + 2 * g2) ≤ T * (1 + 2 * T) := Nat.mul_le_mul h18 (by omega)
  have t5' : T * (1 + 2 * T) ≤ 3 * (B * B) := by nlinarith
  have hBB : 256 * (B * B) ≤ B ^ 6 := by
    have h4 : 256 ≤ B ^ 4 := by
      calc 256 = 4 ^ 4 := by norm_num
        _ ≤ B ^ 4 := Nat.pow_le_pow_left hB4 4
    calc 256 * (B * B) ≤ B ^ 4 * (B * B) := Nat.mul_le_mul_right _ h4
      _ = B ^ 6 := by ring
  have hB1 : B ≤ B * B := by nlinarith
  omega

/-! ## Lower bound for `Tnum` -/

theorem two_le_hIter : 2 ≤ hIter := by norm_num [hIter]

theorem one_le_k0num : 1 ≤ k0num := by norm_num [k0num]

/-- `2^(2^K) ≤ Tnum` for every `K ≤ k₀` (two iterations of `stepBound` already suffice). -/
theorem two_pow_two_pow_le_Tnum (K : ℕ) (hK : K ≤ k0num) : 2 ^ (2 ^ K) ≤ Tnum :=
  two_pow_two_pow_le_iterate hIter k0num K two_le_hIter one_le_k0num hK

theorem K1_le_k0num : K1 ≤ k0num := by rw [K1_def]; norm_num [k0num]
theorem K2_le_k0num : K2 ≤ k0num := by rw [K2_def]; norm_num [k0num]
theorem K3_le_k0num : K3 ≤ k0num := by rw [K3_def]; norm_num [k0num]

theorem G1_le_Tnum : G1 ≤ Tnum := le_trans G1_le (two_pow_two_pow_le_Tnum K1 K1_le_k0num)
theorem G2_le_Tnum : G2 ≤ Tnum := le_trans G2_le (two_pow_two_pow_le_Tnum K2 K2_le_k0num)
theorem G3_le_Tnum : G3 ≤ Tnum := le_trans G3_le (two_pow_two_pow_le_Tnum K3 K3_le_k0num)

set_option exponentiation.threshold 2100 in
theorem two_pow_2000_le_Tnum : 2 ^ 2000 ≤ Tnum :=
  le_trans (Nat.pow_le_pow_right (by norm_num)
    (le_trans (by norm_num : 2000 ≤ 2 ^ 11)
      (Nat.pow_le_pow_right (by norm_num) (by rw [K1_def]; norm_num))))
    (two_pow_two_pow_le_Tnum K1 K1_le_k0num)

/-- **G2 (absorption): `NfarE η₀ ≤ Bnum^6`**, `Bnum = Tnum·16^Tnum`,
`Tnum = stepBound^[hIter] (3·10^19+1)`. -/
theorem NfarE_eta0_le_clean : E18.NfarE eta0 ≤ Bnum ^ 6 :=
  le_trans NfarE_eta0_le
    (absorb_abstract Tnum G1 G2 G3 two_pow_2000_le_Tnum G1_le_Tnum G2_le_Tnum G3_le_Tnum)

/-! ## Tower of twos -/

/-- `4 k₀ ≤ tower2 5 = 2^65536`. -/
theorem four_mul_k0num_le_tower2_five : 4 * k0num ≤ tower2 5 := by
  have h4 : tower2 4 = 65536 := by decide +kernel
  rw [tower2_succ]
  exact le_trans (by norm_num [k0num] : 4 * k0num ≤ 2 ^ 67)
    (Nat.pow_le_pow_right (by norm_num) (by rw [h4]; norm_num))

/-- `4 · Tnum ≤ tower2 (hIter + 5)` (explicit offset `L(k₀) = 5`). -/
theorem four_mul_Tnum_le : 4 * Tnum ≤ tower2 (hIter + 5) :=
  four_mul_iterate_le_tower2 hIter k0num 5 one_le_k0num four_mul_k0num_le_tower2_five

/-- `Tnum ≤ tower2 (hIter + 5)`. -/
theorem Tnum_le_tower2 : Tnum ≤ tower2 (hIter + 5) :=
  iterate_le_tower2 hIter k0num 5 one_le_k0num four_mul_k0num_le_tower2_five

theorem eight_mul_le_two_pow (t : ℕ) (ht : 6 ≤ t) : 8 * t ≤ 2 ^ t := by
  induction t, ht using Nat.le_induction with
  | base => norm_num
  | succ t ht ih => rw [pow_succ]; omega

/-- `(T·16^T)^6 ≤ 2^(2^t)` whenever `8 ≤ T` and `4T ≤ t`. -/
theorem B6_le_two_pow_two_pow (T t : ℕ) (hT : 8 ≤ T) (h : 4 * T ≤ t) :
    (T * 16 ^ T) ^ 6 ≤ 2 ^ (2 ^ t) := by
  have h1 : T * 16 ^ T ≤ 2 ^ (5 * T) := by
    have hT2 : T ≤ 2 ^ T := (Nat.lt_two_pow_self).le
    have h16 : (16 : ℕ) ^ T = 2 ^ (4 * T) := by rw [pow_mul]; norm_num
    rw [h16, show 5 * T = T + 4 * T by ring, pow_add]
    exact Nat.mul_le_mul_right _ hT2
  have h2 : (T * 16 ^ T) ^ 6 ≤ 2 ^ (30 * T) := by
    calc (T * 16 ^ T) ^ 6 ≤ (2 ^ (5 * T)) ^ 6 := Nat.pow_le_pow_left h1 6
      _ = 2 ^ (30 * T) := by rw [← pow_mul]; ring_nf
  have h3 : 30 * T ≤ 2 ^ t := le_trans (by omega) (eight_mul_le_two_pow t (by omega))
  exact le_trans h2 (Nat.pow_le_pow_right (by norm_num) h3)

/-- **G3 (tower): `NfarE η₀ ≤ tower2 (hIter + 7)`**, i.e. `c₀ = 7`. -/
theorem NfarE_eta0_le_tower : E18.NfarE eta0 ≤ tower2 (hIter + 7) := by
  have hT8 : 8 ≤ Tnum :=
    le_trans (le_trans (by norm_num : 8 ≤ 2 ^ 3) (Nat.pow_le_pow_right (by norm_num) (by norm_num)))
      two_pow_2000_le_Tnum
  have h := B6_le_two_pow_two_pow Tnum (tower2 (hIter + 5)) hT8 four_mul_Tnum_le
  rw [tower2_add_seven hIter]
  exact le_trans NfarE_eta0_le_clean h

/-- **Corollary 3.5 at `η₀ = 10⁻¹⁶` with a tower threshold**: every graph of order
`n ≥ tower2 (hIter + 7)` with `F4'(G) < n²/6 − η₀ n²` has an order-`≤ 4` clique partition of
size `≤ targetSize n`. -/
theorem farRegime_eta0_tower :
    ∀ n : ℕ, tower2 (hIter + 7) ≤ n →
      ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      PaperIV.VertexCopyGate.F4' G < (n : ℝ) ^ 2 / 6 - ((eta0 : ℚ) : ℝ) * (n : ℝ) ^ 2 →
        ∃ Q : PaperIV.FarRounding.CliquePartition G, Q.OrderAtMost 4 ∧
          Q.size ≤ PaperIV.FarRounding.targetSize n := by
  intro n hn G _ hfar
  exact E18.farRegime_allGraphs_explicit eta0 (by norm_num [eta0]) n
    (le_trans NfarE_eta0_le_tower hn) G hfar

end E19
