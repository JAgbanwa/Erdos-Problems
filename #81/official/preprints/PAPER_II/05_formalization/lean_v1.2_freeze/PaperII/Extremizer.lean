import Mathlib
import PaperII.Arith

/-!
# Paper II — v1.0.1 additions: extremizer uniqueness (P1) and level-set bound (P2)

Two additions to Theorem 1.1 / §7, both pure arithmetic over the saturated-branch functional
`Fsat n p = p(2n+1−3p)/2` from `PaperII.Arith`. Neither touches the graph theory. Anchored on the
completed-square identity `twelve_mul_twoFsat` (ledger 7.1). The signatures are frozen for audit.

Since `Fsat_le_floor` gives `Fsat n p ≤ ⌊(2n+1)²/24⌋` and `exists_Fsat_eq_floor` attains it, the set
`{p | Fsat n p = ⌊(2n+1)²/24⌋}` is exactly the set of integer maximizers — so "being a maximizer" is
encoded as `Fsat n p = (2n+1)^2 / 24` (no `IsMaxOn` needed).
-/

namespace PaperII

open scoped BigOperators

private lemma Fsat_eq_floor_iff_sq (n p : ℤ) :
    Fsat n p = (2 * n + 1) ^ 2 / 24 ↔
      (6 * p - (2 * n + 1)) ^ 2 = (2 * n + 1) ^ 2 % 24 := by
  have hid : 24 * Fsat n p =
      (2 * n + 1) ^ 2 - (6 * p - (2 * n + 1)) ^ 2 := by
    have htwo := two_mul_Fsat n p
    have htwelve := twelve_mul_twoFsat n p
    linarith
  have hdiv := Int.ediv_mul_add_emod ((2 * n + 1) ^ 2) 24
  constructor <;> intro h
  · omega
  · omega

private lemma odd_square_mod_twenty_four (n : ℤ) :
    (2 * n + 1) ^ 2 % 24 = if n % 3 = 1 then 9 else 1 := by
  let r : ℤ := n % 6
  obtain ⟨q, hq⟩ : ∃ q : ℤ, n = 6 * q + r :=
    ⟨n / 6, by dsimp [r]; omega⟩
  have hsquare : (2 * n + 1) ^ 2 =
      24 * (6 * q ^ 2 + (2 * r + 1) * q) + (2 * r + 1) ^ 2 := by
    calc
      (2 * n + 1) ^ 2 = (2 * (6 * q + r) + 1) ^ 2 := by rw [hq]
      _ = 24 * (6 * q ^ 2 + (2 * r + 1) * q) + (2 * r + 1) ^ 2 := by ring
  have hmod (x y : ℤ) : (24 * x + y) % 24 = y % 24 := by omega
  rw [hsquare, hmod]
  have hr : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 := by
    dsimp [r]
    omega
  have hn3 : n % 3 = r % 3 := by
    dsimp [r]
    omega
  rcases hr with hr | hr | hr | hr | hr | hr <;> rw [hn3, hr] <;> norm_num

/-- **P1 (uniqueness).** For `n ≢ 1 (mod 3)`, the integer maximizer of `Fsat n` — i.e. the unique `p`
attaining the maximum `⌊(2n+1)²/24⌋` — is unique. -/
theorem Fsat_argmax_unique (n : ℤ) (h : n % 3 ≠ 1) :
    ∃! p : ℤ, Fsat n p = (2 * n + 1) ^ 2 / 24 := by
  obtain ⟨p, hp⟩ := exists_Fsat_eq_floor n
  refine ⟨p, hp, ?_⟩
  intro q hq
  have hmod : (2 * n + 1) ^ 2 % 24 = 1 := by
    rw [odd_square_mod_twenty_four n, if_neg h]
  have hp' : (6 * p - (2 * n + 1)) ^ 2 = 1 :=
    ((Fsat_eq_floor_iff_sq n p).mp hp).trans hmod
  have hq' : (6 * q - (2 * n + 1)) ^ 2 = 1 :=
    ((Fsat_eq_floor_iff_sq n q).mp hq).trans hmod
  rcases (sq_eq_one_iff.mp hp') with hp1 | hp1 <;>
    rcases (sq_eq_one_iff.mp hq') with hq1 | hq1
  · omega
  · exfalso; apply h; omega
  · exfalso; apply h; omega
  · omega

/-- **P1 (tie).** For `n ≡ 1 (mod 3)`, exactly two consecutive integers `p, p+1` attain the maximum
`⌊(2n+1)²/24⌋`. -/
theorem Fsat_argmax_tie (n : ℤ) (h : n % 3 = 1) :
    ∃ p : ℤ, Fsat n p = (2 * n + 1) ^ 2 / 24 ∧ Fsat n (p + 1) = (2 * n + 1) ^ 2 / 24 ∧
      ∀ p' : ℤ, Fsat n p' = (2 * n + 1) ^ 2 / 24 → p' = p ∨ p' = p + 1 := by
  let p : ℤ := (n - 1) / 3
  have hpmod : 6 * p - (2 * n + 1) = -3 := by
    dsimp [p]
    omega
  have hp1mod : 6 * (p + 1) - (2 * n + 1) = 3 := by omega
  refine ⟨p, (Fsat_eq_floor_iff_sq n p).mpr ?_,
    (Fsat_eq_floor_iff_sq n (p + 1)).mpr ?_, ?_⟩
  · rw [odd_square_mod_twenty_four n, if_pos h, hpmod]
    norm_num
  · rw [odd_square_mod_twenty_four n, if_pos h, hp1mod]
    norm_num
  · intro p' hp'
    have hmod : (2 * n + 1) ^ 2 % 24 = 9 := by
      rw [odd_square_mod_twenty_four n, if_pos h]
    have hs : (6 * p' - (2 * n + 1)) ^ 2 = 9 :=
      ((Fsat_eq_floor_iff_sq n p').mp hp').trans hmod
    have hb : -3 ≤ 6 * p' - (2 * n + 1) ∧ 6 * p' - (2 * n + 1) ≤ 3 := by
      constructor <;> nlinarith [sq_nonneg (6 * p' - (2 * n + 1) + 3),
        sq_nonneg (6 * p' - (2 * n + 1) - 3)]
    have hroot : 6 * p' - (2 * n + 1) = -3 ∨ 6 * p' - (2 * n + 1) = 3 := by
      rcases hb with ⟨hb1, hb2⟩
      omega
    rcases hroot with hroot | hroot
    · left; omega
    · right; omega

/-- **P2 (level-set bound).** From the completed-square identity (7.1), for the real saturated-branch
functional `F_n(p) = p(2n+1−3p)/2` and any `δ ≥ 0`, measured from the **continuous** maximum
`(2n+1)²/24`:  `F_n(p) ≥ (2n+1)²/24 − δ  ↔  |p − (2n+1)/6| ≤ √(2δ/3)`. Exact equivalence. -/
theorem level_set_iff (n p δ : ℝ) (hδ : 0 ≤ δ) :
    p * (2 * n + 1 - 3 * p) / 2 ≥ (2 * n + 1) ^ 2 / 24 - δ
      ↔ |p - (2 * n + 1) / 6| ≤ Real.sqrt (2 * δ / 3) := by
  let q : ℝ := 2 * n + 1
  have complete_square : ∀ p : ℝ, p * (q - 3 * p) / 2 = -(3/2) * (p - q/6)^2 + q^2/24 := by
    intro p; ring
  simp_rw [show p * (2 * n + 1 - 3 * p) / 2 = -(3/2) * (p - q/6)^2 + q^2/24 from complete_square p]
  constructor
  · intro h
    have h1 : -(3/2) * (p - q/6)^2 + q^2/24 ≥ q^2/24 - δ := by 
      simp only [q] at *
      linarith
    have h2 : -(3/2) * (p - q/6)^2 ≥ -δ := by linarith
    have h3 : (3/2) * (p - q/6)^2 ≤ δ := by linarith
    have h4 : (p - q/6)^2 ≤ 2 * δ / 3 := by linarith
    have h5 : |p - q/6| ≤ Real.sqrt (2 * δ / 3) := by
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt h4
    simpa [q] using h5
  · intro h
    have h5 : |p - q/6| ≤ Real.sqrt (2 * δ / 3) := h
    rw [← Real.sqrt_sq_eq_abs] at h5
    have h4 : (p - q/6)^2 ≤ 2 * δ / 3 := by
      rwa [Real.sqrt_le_sqrt_iff (by positivity)] at h5
    have h3 : (3/2) * (p - q/6)^2 ≤ δ := by linarith
    have h2 : -(3/2) * (p - q/6)^2 ≥ -δ := by linarith
    simp only [q] at *
    linarith

end PaperII
