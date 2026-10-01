import E18.Far

/-!
# E18 — the numerical far threshold at Paper IV's `η₀ = 10⁻¹⁶`

For `η₀ = 1/10^16` the far threshold is `NfarE η₀ = NE (η₀/2)`, i.e. RC01 at
`ε = 1/(2·10^16)`.  The parameters of that single instance are exact rationals:

* `s = 1/(9·10^19)`, `δ = s^21/2208`, `zq = 1/(2·10^17)`, `k₀ = 3·10^19 + 1`;
* the regularity iteration count is `h = ⌊4/(δ/8)^5⌋ = 4·8^5·2208^5·4500^105·(2·10^16)^105`;
* Mathlib's initial partition size is `initialBound (δ/8) k₀ = k₀`, so
  `B = SzemerediRegularity.bound (δ/8) k₀ = T·16^T` with `T = stepBound^[h] (3·10^19+1)`.

`NfarE_eta0_le` bounds `NfarE η₀` by an explicit expression in `B` and the three
explicit nibble/gate constants `⌈1/gamE zq⌉`, `⌈CstE zq⌉`, `DE zq`.
-/

namespace E18.Numeric

open SzemerediRegularity

/-- Paper IV's quadratic margin `η₀ = 10⁻¹⁶`. -/
def eta0 : ℚ := 1 / 10 ^ 16

/-- The regularity iteration count of the far instance,
`h = 4·8^5·2208^5·4500^105·(2·10^16)^105` (2118 decimal digits). -/
def hIter : ℕ := 4 * 8 ^ 5 * 2208 ^ 5 * 4500 ^ 105 * (2 * 10 ^ 16) ^ 105

/-- `k₀ = 3·10^19 + 1`. -/
def k0num : ℕ := 3 * 10 ^ 19 + 1

/-- The iterate `T = stepBound^[h] k₀` (a notation, not a definition, so that no
definitional unfolding can ever ask to evaluate this astronomically large number). -/
scoped notation "Tnum" => SzemerediRegularity.stepBound^[E18.Numeric.hIter] E18.Numeric.k0num

/-- The regularity bound `B = T · 16^T`. -/
scoped notation "Bnum" => Tnum * 16 ^ Tnum

theorem sE_eta0 : sE (eta0 / 2) = 1 / (9 * 10 ^ 19) := by
  norm_num [sE, eta0]

theorem δE_eta0 : δE (eta0 / 2) = 1 / (2208 * (9 * 10 ^ 19) ^ 21) := by
  rw [δE, sE_eta0, PaperIV.RC01Final.deltaOf]
  norm_num

theorem zqE_eta0 : zqE (eta0 / 2) = 1 / (2 * 10 ^ 17) := by
  norm_num [zqE, eta0]

theorem k0E_eta0 : k0E (eta0 / 2) = k0num := by
  have h : (1500 / (eta0 / 2) : ℚ) = 3 * 10 ^ 19 := by norm_num [eta0]
  rw [k0E, h, k0num]
  norm_num

/-- The regularity accuracy of the far instance, as a real number. -/
theorem epsReg_eq : (((δE (eta0 / 2) / 8 : ℚ)) : ℝ)
    = ((1 / (8 * (2208 * (9 * 10 ^ 19) ^ 21)) : ℚ) : ℝ) := by
  rw [δE_eta0]; norm_num

set_option exponentiation.threshold 5000 in
set_option maxRecDepth 100000 in
/-- **The iteration count is exactly `hIter`.** -/
theorem floor_iter_eq :
    ⌊(4 : ℝ) / (((δE (eta0 / 2) / 8 : ℚ)) : ℝ) ^ 5⌋₊ = hIter := by
  have hQ : (4 : ℚ) / ((1 / (8 * (2208 * (9 * 10 ^ 19) ^ 21)) : ℚ)) ^ 5 = (hIter : ℚ) := by
    rw [hIter]; push_cast; norm_num
  have hR : (4 : ℝ) / (((δE (eta0 / 2) / 8 : ℚ)) : ℝ) ^ 5 = ((hIter : ℕ) : ℝ) := by
    rw [epsReg_eq]
    have := congrArg (fun q : ℚ => (q : ℝ)) hQ
    push_cast at this ⊢
    linarith [this]
  rw [hR, Nat.floor_natCast]

set_option exponentiation.threshold 5000 in
set_option maxRecDepth 100000 in
/-- **Mathlib's initial partition size is `k₀`.** -/
theorem initialBound_eq :
    initialBound (((δE (eta0 / 2) / 8 : ℚ)) : ℝ) k0num = k0num := by
  set e : ℝ := (((δE (eta0 / 2) / 8 : ℚ)) : ℝ) with he
  have he' : e = ((1 / (8 * (2208 * (9 * 10 ^ 19) ^ 21)) : ℚ) : ℝ) := epsReg_eq
  have hepos : 0 < e := by rw [he']; positivity
  have hX : (100 : ℝ) / e ^ 5 ≤ (4 : ℝ) ^ (4000 : ℕ) := by
    have hQ : (100 : ℚ) / ((1 / (8 * (2208 * (9 * 10 ^ 19) ^ 21)) : ℚ)) ^ 5
        ≤ (4 : ℚ) ^ (4000 : ℕ) := by norm_num
    have := (Rat.cast_le (K := ℝ)).2 hQ
    rw [he']
    push_cast at this ⊢
    exact this
  have hlog : Real.log (100 / e ^ 5) / Real.log 4 ≤ 4000 := by
    have h4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
    rw [div_le_iff₀ h4]
    have hpos : 0 < (100 : ℝ) / e ^ 5 := by positivity
    calc Real.log (100 / e ^ 5) ≤ Real.log ((4 : ℝ) ^ (4000 : ℕ)) :=
          Real.log_le_log hpos hX
      _ = 4000 * Real.log 4 := by rw [Real.log_pow]; norm_num
  have hfloor : ⌊Real.log (100 / e ^ 5) / Real.log 4⌋₊ ≤ 4000 :=
    Nat.floor_le_of_le (by exact_mod_cast hlog)
  rw [initialBound]
  have h1 : ⌊Real.log (100 / e ^ 5) / Real.log 4⌋₊ + 1 ≤ k0num := by
    rw [k0num]; omega
  have h2 : 7 ≤ k0num := by rw [k0num]; norm_num
  rw [max_eq_left h1, max_eq_right h2]

/-- **The regularity bound of the far instance is `B = T·16^T`, `T = stepBound^[h] k₀`.** -/
theorem BE_eta0 : BE (eta0 / 2) = Bnum := by
  have h1 : BE (eta0 / 2) = SzemerediRegularity.bound (((δE (eta0 / 2) / 8 : ℚ)) : ℝ) k0num := by
    rw [BE, k0E_eta0]
  rw [h1, SzemerediRegularity.bound, initialBound_eq, floor_iter_eq]

/-- The gate slack of the far instance as a real number, `zq = 1/(2·10^17)`. -/
noncomputable def zq0 : ℝ := ((1 / (2 * 10 ^ 17) : ℚ) : ℝ)

/-- `G₁ = ⌈1/gamE zq⌉`, the reciprocal of the rational codegree constant `gammaQE`. -/
noncomputable def G1 : ℕ := ⌈1 / PaperIV.RC01UniformDenseGate.gamE zq0⌉₊
/-- `G₂ = ⌈CstE zq⌉`, the integer triangle-mass constant. -/
noncomputable def G2 : ℕ := ⌈PaperIV.RC01UniformDenseGate.CstE zq0⌉₊
/-- `G₃ = ⌈2·10^17 (12 + 10 DE zq)⌉`, the additive-constant threshold. -/
noncomputable def G3 : ℕ := ⌈(2 * 10 ^ 17 : ℝ) * (12 + 10 * PaperIV.RC01UniformDenseGate.DE zq0)⌉₊

set_option maxHeartbeats 1000000 in
set_option exponentiation.threshold 5000 in
set_option maxRecDepth 100000 in
/-- The far threshold at `η₀`, in terms of an abstract value `B` of the regularity bound. -/
theorem NfarE_eta0_le_of_B :
    NfarE eta0 ≤ k0num + 2208 * (9 * 10 ^ 19) ^ 21 * BE (eta0 / 2) + G3
      + 8 * (9 * 10 ^ 19) ^ 6 * G1 * BE (eta0 / 2) ^ 5 + 10 ^ 18 * (1 + 2 * G2) + 1 := by
  have hzq : ((zqE (eta0 / 2) : ℚ) : ℝ) = zq0 := by rw [zqE_eta0, zq0]
  unfold NfarE NE scaleBoundE massBoundE gammaQE cstE
  rw [hzq, k0E_eta0, sE_eta0, δE_eta0]
  have hG1 : (⌈1 / PaperIV.RC01UniformDenseGate.gamE zq0⌉₊ : ℚ) = (G1 : ℚ) := rfl
  have hG2 : (⌈PaperIV.RC01UniformDenseGate.CstE zq0⌉₊ : ℚ) = (G2 : ℚ) := rfl
  rw [hG1, hG2]
  generalize BE (eta0 / 2) = B
  -- the five terms
  have t2 : ⌈(B : ℚ) / (1 / (2208 * (9 * 10 ^ 19) ^ 21))⌉₊ ≤ 2208 * (9 * 10 ^ 19) ^ 21 * B := by
    apply Nat.ceil_le.2
    push_cast
    rw [div_div_eq_mul_div, div_one, mul_comm]
    norm_num
  have t3 : ⌈(12 + 10 * PaperIV.RC01UniformDenseGate.DE zq0) / zq0⌉₊ ≤ G3 := by
    have : (12 + 10 * PaperIV.RC01UniformDenseGate.DE zq0) / zq0
        = (2 * 10 ^ 17 : ℝ) * (12 + 10 * PaperIV.RC01UniformDenseGate.DE zq0) := by
      rw [zq0]; push_cast; field_simp
    rw [this, G3]
  have hab : ((1 / (9 * 10 ^ 19) : ℚ) ^ 3 - 3 * (1 / (2208 * (9 * 10 ^ 19) ^ 21))
        + ((1 / (9 * 10 ^ 19)) ^ 6 - 6 * (1 / (2208 * (9 * 10 ^ 19) ^ 21))))
      / (((1 / (9 * 10 ^ 19) : ℚ) ^ 3 - 3 * (1 / (2208 * (9 * 10 ^ 19) ^ 21)))
        * ((1 / (9 * 10 ^ 19)) ^ 6 - 6 * (1 / (2208 * (9 * 10 ^ 19) ^ 21))))
      ≤ 2 * (9 * 10 ^ 19) ^ 6 := by norm_num
  have t4 : ⌈4 * (B : ℚ) ^ 5 * (((1 / (9 * 10 ^ 19) : ℚ) ^ 3 - 3 * (1 / (2208 * (9 * 10 ^ 19) ^ 21)))
        + ((1 / (9 * 10 ^ 19)) ^ 6 - 6 * (1 / (2208 * (9 * 10 ^ 19) ^ 21)))) /
        (1 / (G1 : ℚ) * ((1 / (9 * 10 ^ 19) : ℚ) ^ 3 - 3 * (1 / (2208 * (9 * 10 ^ 19) ^ 21)))
          * ((1 / (9 * 10 ^ 19)) ^ 6 - 6 * (1 / (2208 * (9 * 10 ^ 19) ^ 21))))⌉₊
      ≤ 8 * (9 * 10 ^ 19) ^ 6 * G1 * B ^ 5 := by
    apply Nat.ceil_le.2
    set a : ℚ := (1 / (9 * 10 ^ 19) : ℚ) ^ 3 - 3 * (1 / (2208 * (9 * 10 ^ 19) ^ 21)) with ha
    set b : ℚ := (1 / (9 * 10 ^ 19) : ℚ) ^ 6 - 6 * (1 / (2208 * (9 * 10 ^ 19) ^ 21)) with hb
    have ha0 : 0 < a := by rw [ha]; norm_num
    have hb0 : 0 < b := by rw [hb]; norm_num
    rcases Nat.eq_zero_or_pos G1 with h0 | hpos
    · rw [h0]; simp
    have hG : (0 : ℚ) < G1 := by exact_mod_cast hpos
    have heq : 4 * (B : ℚ) ^ 5 * (a + b) / (1 / (G1 : ℚ) * a * b)
        = 4 * (B : ℚ) ^ 5 * (G1 : ℚ) * ((a + b) / (a * b)) := by
      field_simp
    rw [heq]
    push_cast
    have hB5 : (0 : ℚ) ≤ 4 * (B : ℚ) ^ 5 * (G1 : ℚ) := by positivity
    have key := mul_le_mul_of_nonneg_left hab hB5
    linarith [key]
  have t5 : ⌈50 * (1 + 2 * (G2 : ℚ)) / (eta0 / 2)⌉₊ ≤ 10 ^ 18 * (1 + 2 * G2) := by
    apply Nat.ceil_le.2
    rw [eta0]; push_cast
    rw [div_le_iff₀ (by norm_num)]
    ring_nf; rfl
  have hmax : ∀ a b c d e : ℕ, max (max a b) (max c (max d e)) ≤ a + b + c + d + e := by
    intro a b c d e; omega
  refine Nat.add_le_add_right (le_trans (hmax _ _ _ _ _) ?_) 1
  gcongr

/-- **The explicit far threshold at `η₀ = 10⁻¹⁶`**, written with the regularity iterate
`T = stepBound^[h] (3·10^19+1)`, `h = hIter`, `B = T·16^T`. -/
theorem NfarE_eta0_le :
    NfarE eta0 ≤ k0num + 2208 * (9 * 10 ^ 19) ^ 21 * Bnum + G3
      + 8 * (9 * 10 ^ 19) ^ 6 * G1 * Bnum ^ 5 + 10 ^ 18 * (1 + 2 * G2) + 1 := by
  have h := NfarE_eta0_le_of_B
  rw [BE_eta0] at h
  exact h

/-- **Numerical corollary of A3** (Corollary 3.5 at Paper IV's `η₀ = 10⁻¹⁶`): every graph
whose order is at least the explicit bound of `NfarE_eta0_le` and with
`F4'(G) < n²/6 − η₀ n²` has an order-`≤ 4` clique partition of size `≤ targetSize n`. -/
theorem farRegime_eta0_explicit :
    ∀ n : ℕ, k0num + 2208 * (9 * 10 ^ 19) ^ 21 * Bnum + G3
        + 8 * (9 * 10 ^ 19) ^ 6 * G1 * Bnum ^ 5 + 10 ^ 18 * (1 + 2 * G2) + 1 ≤ n →
      ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      PaperIV.VertexCopyGate.F4' G < (n : ℝ) ^ 2 / 6 - ((eta0 : ℚ) : ℝ) * (n : ℝ) ^ 2 →
        ∃ Q : PaperIV.FarRounding.CliquePartition G, Q.OrderAtMost 4 ∧
          Q.size ≤ PaperIV.FarRounding.targetSize n := by
  intro n hn G _ hfar
  exact farRegime_allGraphs_explicit eta0 (by norm_num [eta0]) n
    (le_trans NfarE_eta0_le hn) G hfar

end E18.Numeric
