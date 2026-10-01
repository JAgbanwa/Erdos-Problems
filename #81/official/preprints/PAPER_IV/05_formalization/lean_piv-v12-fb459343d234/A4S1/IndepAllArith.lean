import A4S1.IndepAllTools

/-!
# E14: the final arithmetic of the E10 count (copied from `A4S1.OwnAllConstructor`)

Only the pure arithmetic part of `A4S1.OwnAllConstructor` is reproduced here (that module also
contains the shared constructor `caseA_general` and imports `A4S1.T1Cases`, so it cannot be
imported):

* `own_targetSize_ge`: `c(m − c) ≤ C(c,2) + M(m)` for every `c ≤ m`;
* `own_defectTarget_add`: `Q_s(m) + k ⌊(m+s+2)/3⌋ ≤ Q_s(m+k)`;
* `own_final_all`: the final count.
-/

namespace A4S1.IndepAll

open Finset PaperIV.FarRounding PaperIV.RootedSimplicialDefect A4S1.TerminalPacking
  PaperIV.DefectTargetArithmetic

/-! ## Arithmetic -/

theorem own_targetSize_ge (m c : ℕ) (hc : c ≤ m) :
    c * (m - c) ≤ c.choose 2 + PaperIV.FarRounding.targetSize m := by
  obtain ⟨b, rfl⟩ : ∃ b, m = c + b := ⟨m - c, by omega⟩
  rw [Nat.add_sub_cancel_left]
  have hch : 2 * c.choose 2 + c = c * c := by
    rw [Nat.choose_two_right]
    rcases c with _ | c
    · simp
    · have := Nat.div_mul_cancel (Nat.even_mul_pred_self (c + 1)).two_dvd
      rw [Nat.add_sub_cancel] at this ⊢
      nlinarith
  have key : 6 * (c * b) ≤ 6 * c.choose 2 + (c + b) * (c + b + 1) := by
    have hZ : (6 * (c * b) : ℤ) ≤ 6 * (c.choose 2 : ℤ) + ((c : ℤ) + b) * ((c : ℤ) + b + 1) := by
      have hch' : (2 * c.choose 2 : ℤ) + c = (c : ℤ) * c := by exact_mod_cast hch
      have hy : (0 : ℤ) ≤ ((b : ℤ) - 2 * c) * ((b : ℤ) - 2 * c + 1) := by
        rcases le_or_gt 0 ((b : ℤ) - 2 * c) with h | h
        · exact mul_nonneg h (by linarith)
        · exact mul_nonneg_of_nonpos_of_nonpos h.le (by linarith)
      nlinarith
    exact_mod_cast hZ
  unfold PaperIV.FarRounding.targetSize
  have hdiv := Nat.div_add_mod ((c + b) * (c + b + 1)) 6
  have hmod := Nat.mod_lt ((c + b) * (c + b + 1)) (show 0 < 6 by norm_num)
  omega

theorem own_defectTarget_add (s m k : ℕ) (hm : s + 2 ≤ m) :
    defectTarget s m + k * ((m + s + 2) / 3) ≤ defectTarget s (m + k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show m + (k + 1) = m + k + 1 by ring,
      A4S1.MinDegreeAll.defectTarget_succ s (m + k) (by omega)]
    have h : (m + s + 2) / 3 ≤ (m + k + s + 2) / 3 := Nat.div_le_div_right (by omega)
    rw [Nat.succ_mul]
    omega

theorem own_three_div (x : ℕ) : x ≤ 3 * ((x + 2) / 3) := by
  have := Nat.div_add_mod (x + 2) 3
  have := Nat.mod_lt (x + 2) (show 0 < 3 by norm_num)
  omega

/-- **The final count.** From the constructor count and the rational budget
`dg + 2k(L+k) + C(c,2) + C(s+1,2) ≤ e_C + 2 mn + s c + k (c+b+s)/3`, the partition has at most
`Q_s(c+b+k)` pieces. -/
theorem own_final_all (Qs c b s k dg mn L eC : ℕ) (hm : s + 2 ≤ c + b)
    (hQ : Qs + eC + 2 * mn ≤ c * b + dg + 2 * k * (L + k))
    (hkey : (dg : ℚ) + 2 * k * (L + k) + c.choose 2 + (s + 1).choose 2 ≤
      eC + 2 * mn + s * c + k * ((c + b + s : ℕ) : ℚ) / 3) :
    Qs ≤ defectTarget s (c + b + k) := by
  have hts := own_targetSize_ge (c + b + s) c (by omega)
  rw [show c + b + s - c = b + s by omega] at hts
  have hadd := own_defectTarget_add s (c + b) k hm
  set Z := k * ((c + b + s + 2) / 3) with hZ
  have h3 := own_three_div (c + b + s)
  have hZq : (k : ℚ) * ((c + b + s : ℕ) : ℚ) / 3 ≤ (Z : ℚ) := by
    have h3q : ((c + b + s : ℕ) : ℚ) ≤ 3 * (((c + b + s + 2) / 3 : ℕ) : ℚ) := by exact_mod_cast h3
    have hk : (0 : ℚ) ≤ k := by positivity
    rw [hZ]; push_cast at h3q ⊢; nlinarith
  have hkeyN : dg + 2 * k * (L + k) + c.choose 2 + (s + 1).choose 2 ≤ eC + 2 * mn + s * c + Z := by
    have : (dg : ℚ) + 2 * k * (L + k) + c.choose 2 + (s + 1).choose 2 ≤
        eC + 2 * mn + s * c + Z := by linarith
    exact_mod_cast this
  unfold defectTarget at hadd ⊢
  rw [show c + b + k + s = c + b + s + k by ring] at hadd ⊢
  rw [show c + b + s = c + b + s by rfl] at hadd
  have hmul : c * (b + s) = c * b + s * c := by ring
  set Y := 2 * k * (L + k)
  set X := c * b
  set T := PaperIV.FarRounding.targetSize (c + b + s)
  omega

end A4S1.IndepAll
