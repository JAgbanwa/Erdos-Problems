import E34.Bridge

/-!
# E34 — explicit parameters for Theorem 1 relative to Lemma 11

We fix the explicit sample size of Lemma 11
`m11V ε K = ⌈2^58 (K+1)^15 / ε^12⌉₊`
(an explicit polynomial bound, see `data/E34_RESULTS.md` for its derivation from the paper's
proof with corrected constants), and the parameters of Section 6:
* `sV ε = ⌈102400 / ε²⌉₊`, `qV ε = (sV ε)²` (number of sampled pairs);
* `ℓV q = ⌈log₂ (4 · nCodes q)⌉` (number of independent Lemma-11 blocks);
* `MV ε q = m11V (ε²/512) (kMax q)` (size of each block);
* `mV ε = 2 qV ε + MV ε (qV ε) · ℓV (qV ε)`.

`hq_V` is the numerical condition `4 ℓ M (1 − ε²/256)^q ≤ 1` of `thm1_of_lemma11`.
-/

namespace E34

open Finset Real

/-- The explicit sample size of Lemma 11 used in this project. -/
noncomputable def m11V (ε : ℝ) (K : ℕ) : ℕ := ⌈(2 : ℝ) ^ 58 * ((K : ℝ) + 1) ^ 15 / ε ^ 12⌉₊

/-- Square root of the number of sampled pairs. -/
noncomputable def sV (ε : ℝ) : ℕ := ⌈(102400 : ℝ) / ε ^ 2⌉₊

/-- Number of sampled pairs in Section 6. -/
noncomputable def qV (ε : ℝ) : ℕ := sV ε ^ 2

/-- Number of independent blocks. -/
def ellV (q : ℕ) : ℕ := Nat.clog 2 (4 * nCodes q)

/-- Size of each block. -/
noncomputable def MV (ε : ℝ) (q : ℕ) : ℕ := m11V (ε ^ 2 / 256 / 2) (kMax q)

/-- The final sample size. -/
noncomputable def mV (ε : ℝ) : ℕ := 2 * qV ε + MV ε (qV ε) * ellV (qV ε)

theorem m11V_mono (ε : ℝ) {K K' : ℕ} (h : K ≤ K') : m11V ε K ≤ m11V ε K' := by
  unfold m11V
  apply Nat.ceil_mono
  have : ((K : ℝ) + 1) ^ 15 ≤ ((K' : ℝ) + 1) ^ 15 := by
    apply pow_le_pow_left₀ (by positivity); exact_mod_cast Nat.add_le_add_right h 1
  rw [div_eq_mul_inv, div_eq_mul_inv]
  apply mul_le_mul_of_nonneg_right _ (inv_nonneg.2 (by
    rcases le_or_gt 0 ε with h | h
    · positivity
    · exact (Even.pow_nonneg (by decide) _)))
  exact mul_le_mul_of_nonneg_left this (by positivity)

theorem kMax_succ_le {q : ℕ} (hq : 1 ≤ q) : kMax q + 1 ≤ 26 * q ^ 4 := by
  unfold kMax
  have h1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq
  have h2 : q ^ 4 = q ^ 2 * q ^ 2 := by ring
  nlinarith

theorem one_le_kMax (q : ℕ) : 1 ≤ kMax q := by
  unfold kMax; exact Nat.one_le_pow _ _ (by omega)

theorem nCodes_le (q : ℕ) :
    nCodes q ≤ (kMax q + 1) ^ (kMax q + 4 * q ^ 2 + 2) := by
  unfold nCodes
  set k := kMax q
  have hk : 1 ≤ k := one_le_kMax q
  calc ∑ K0 ∈ range (k + 1), K0 ^ K0 * K0 ^ (4 * q ^ 2 + 1)
      ≤ ∑ _K0 ∈ range (k + 1), (k + 1) ^ (k + 4 * q ^ 2 + 1) := by
        refine sum_le_sum (fun K0 hK0 => ?_)
        rw [mem_range] at hK0
        rw [← pow_add]
        rcases Nat.eq_zero_or_pos K0 with h0 | h0
        · subst h0; simp
        · calc K0 ^ (K0 + (4 * q ^ 2 + 1)) ≤ (k + 1) ^ (K0 + (4 * q ^ 2 + 1)) :=
                Nat.pow_le_pow_left (by omega) _
            _ ≤ (k + 1) ^ (k + 4 * q ^ 2 + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    _ = (k + 1) * (k + 1) ^ (k + 4 * q ^ 2 + 1) := by rw [sum_const, card_range, smul_eq_mul]
    _ = (k + 1) ^ (k + 4 * q ^ 2 + 2) := by ring

theorem ellV_le (q : ℕ) : ellV q ≤ 4 * (kMax q + 1) ^ 2 := by
  unfold ellV
  set k := kMax q
  have hk : 1 ≤ k := one_le_kMax q
  have hq2 : 4 * q ^ 2 + 1 ≤ k := by
    show 4 * q ^ 2 + 1 ≤ (4 * q ^ 2 + 1) ^ 2
    nlinarith
  apply Nat.clog_le_of_le_pow
  have h1 := nCodes_le q
  have h2 : k + 1 ≤ 2 ^ (k + 1) := (Nat.lt_two_pow_self).le
  calc 4 * nCodes q ≤ 2 ^ 2 * (2 ^ (k + 1)) ^ (k + 4 * q ^ 2 + 2) :=
        Nat.mul_le_mul (by norm_num) (h1.trans (Nat.pow_le_pow_left h2 _))
    _ = 2 ^ (2 + (k + 1) * (k + 4 * q ^ 2 + 2)) := by rw [← pow_mul, ← pow_add]
    _ ≤ 2 ^ (4 * (k + 1) ^ 2) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)

theorem MV_le {ε : ℝ} (hε0 : 0 < ε) (q : ℕ) :
    (MV ε q : ℝ) ≤ 2 ^ 166 * ((kMax q : ℝ) + 1) ^ 15 / ε ^ 24 + 1 := by
  unfold MV m11V
  refine (Nat.ceil_lt_add_one (by positivity)).le.trans (le_of_eq ?_)
  have h : (ε ^ 2 / 256 / 2) ^ 12 = ε ^ 24 / 2 ^ 108 := by ring
  rw [h, div_div_eq_mul_div]
  ring

/-- The numerical condition of `thm1_of_lemma11` for the explicit parameters. -/
theorem hq_V {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    4 * ((ellV (qV ε) * MV ε (qV ε) : ℕ) : ℝ) * (1 - ε ^ 2 / 256) ^ qV ε ≤ 1 := by
  set s : ℕ := sV ε with hsdef
  have hs : (102400 : ℝ) / ε ^ 2 ≤ s := Nat.le_ceil _
  have he2 : 0 < ε ^ 2 := by positivity
  have he2' : ε ^ 2 ≤ 1 := by nlinarith
  have hinv : 1 ≤ 1 / ε ^ 2 := by rw [le_div_iff₀ he2]; linarith
  have hx1 : 1 / ε ≤ 1 / ε ^ 2 := by
    apply one_div_le_one_div_of_le he2; nlinarith
  have hsε : 102400 ≤ (s : ℝ) * ε ^ 2 := by rwa [div_le_iff₀ he2] at hs
  have hs1 : (102400 : ℝ) ≤ s := by
    have : (102400 : ℝ) ≤ 102400 / ε ^ 2 := by
      rw [le_div_iff₀ he2]; nlinarith
    linarith
  have hs0 : (0 : ℝ) < s := by linarith
  have hsn : 1 ≤ s := by exact_mod_cast (show (1 : ℝ) ≤ s by linarith)
  have hq1 : 1 ≤ qV ε := Nat.one_le_pow _ _ hsn
  -- bounds on ℓ and M
  have hP := kMax_succ_le hq1
  have hPr : ((kMax (qV ε) : ℝ) + 1) ≤ 26 * (s : ℝ) ^ 8 := by
    have : ((kMax (qV ε) + 1 : ℕ) : ℝ) ≤ ((26 * qV ε ^ 4 : ℕ) : ℝ) := by exact_mod_cast hP
    push_cast at this; unfold qV at this; push_cast at this
    calc _ ≤ 26 * ((s : ℝ) ^ 2) ^ 4 := this
      _ = 26 * (s : ℝ) ^ 8 := by ring
  have hP0 : (0 : ℝ) ≤ (kMax (qV ε) : ℝ) + 1 := by positivity
  have hℓ : (ellV (qV ε) : ℝ) ≤ 2704 * (s : ℝ) ^ 16 := by
    have h := ellV_le (qV ε)
    have : ((ellV (qV ε) : ℕ) : ℝ) ≤ 4 * ((kMax (qV ε) : ℝ) + 1) ^ 2 := by exact_mod_cast h
    calc _ ≤ 4 * ((kMax (qV ε) : ℝ) + 1) ^ 2 := this
      _ ≤ 4 * (26 * (s : ℝ) ^ 8) ^ 2 := by gcongr
      _ = 2704 * (s : ℝ) ^ 16 := by ring
  have hM : (MV ε (qV ε) : ℝ) ≤ 2 ^ 238 * (s : ℝ) ^ 120 / ε ^ 24 := by
    have h := MV_le hε0 (qV ε)
    have hpow : ((kMax (qV ε) : ℝ) + 1) ^ 15 ≤ (26 * (s : ℝ) ^ 8) ^ 15 := by gcongr
    have h26 : (26 : ℝ) ^ 15 ≤ 2 ^ 71 := by norm_num
    have he24 : 0 < ε ^ 24 := by positivity
    have he24' : ε ^ 24 ≤ 1 := pow_le_one₀ hε0.le hε1
    have hs120 : 1 ≤ (s : ℝ) ^ 120 := one_le_pow₀ (by linarith)
    calc (MV ε (qV ε) : ℝ) ≤ 2 ^ 166 * ((kMax (qV ε) : ℝ) + 1) ^ 15 / ε ^ 24 + 1 := h
      _ ≤ 2 ^ 166 * (26 * (s : ℝ) ^ 8) ^ 15 / ε ^ 24 + (s : ℝ) ^ 120 / ε ^ 24 := by
          gcongr
          rw [le_div_iff₀ he24]; nlinarith
      _ = (2 ^ 166 * 26 ^ 15 + 1) * (s : ℝ) ^ 120 / ε ^ 24 := by ring
      _ ≤ 2 ^ 238 * (s : ℝ) ^ 120 / ε ^ 24 := by
          gcongr; nlinarith
  have hA : 4 * ((ellV (qV ε) * MV ε (qV ε) : ℕ) : ℝ) ≤ 2 ^ 252 * (s : ℝ) ^ 136 / ε ^ 24 := by
    push_cast
    have hM0 : (0 : ℝ) ≤ MV ε (qV ε) := by positivity
    calc 4 * ((ellV (qV ε) : ℝ) * (MV ε (qV ε) : ℝ))
        ≤ 4 * ((2704 * (s : ℝ) ^ 16) * (2 ^ 238 * (s : ℝ) ^ 120 / ε ^ 24)) := by gcongr
      _ = (4 * 2704 * 2 ^ 238) * (s : ℝ) ^ 136 / ε ^ 24 := by ring
      _ ≤ 2 ^ 252 * (s : ℝ) ^ 136 / ε ^ 24 := by gcongr; norm_num
  -- the exponential estimate
  have hη0 : 0 ≤ 1 - ε ^ 2 / 256 := by linarith
  have hexp1 : (1 - ε ^ 2 / 256) ^ qV ε ≤ Real.exp (-(ε ^ 2 / 256 * (s : ℝ) ^ 2)) := by
    have h1 : 1 - ε ^ 2 / 256 ≤ Real.exp (-(ε ^ 2 / 256)) := by
      have := Real.add_one_le_exp (-(ε ^ 2 / 256)); linarith
    calc (1 - ε ^ 2 / 256) ^ qV ε ≤ Real.exp (-(ε ^ 2 / 256)) ^ qV ε :=
          pow_le_pow_left₀ hη0 h1 _
      _ = Real.exp (-(ε ^ 2 / 256) * (qV ε : ℝ)) := by rw [← Real.exp_nat_mul]; ring_nf
      _ = Real.exp (-(ε ^ 2 / 256 * (s : ℝ) ^ 2)) := by
          rw [show (qV ε : ℝ) = (s : ℝ) ^ 2 from by rw [hsdef]; unfold qV; push_cast; rfl]
          ring_nf
  have hbig : 2 ^ 252 * (s : ℝ) ^ 136 / ε ^ 24 ≤ Real.exp (ε ^ 2 / 256 * (s : ℝ) ^ 2) := by
    have hexps : (s : ℝ) ≤ Real.exp (s : ℝ) := by
      have := Real.add_one_le_exp (s : ℝ); linarith
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ); linarith
    have hx : 1 / ε ≤ Real.exp ((s : ℝ) / 102400) := by
      have : 1 / ε ≤ (s : ℝ) / 102400 := by
        calc 1 / ε ≤ 1 / ε ^ 2 := hx1
          _ ≤ (s : ℝ) / 102400 := by
            rw [div_le_div_iff₀ he2 (by norm_num)]; linarith
      have := Real.add_one_le_exp ((s : ℝ) / 102400); linarith
    have hx0 : 0 ≤ 1 / ε := by positivity
    calc 2 ^ 252 * (s : ℝ) ^ 136 / ε ^ 24 = 2 ^ 252 * (s : ℝ) ^ 136 * (1 / ε) ^ 24 := by
          field_simp
      _ ≤ Real.exp 1 ^ 252 * Real.exp (s : ℝ) ^ 136 * Real.exp ((s : ℝ) / 102400) ^ 24 := by
          gcongr
      _ = Real.exp (252 + 136 * (s : ℝ) + 24 * ((s : ℝ) / 102400)) := by
          rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add,
            ← Real.exp_add]
          push_cast; ring_nf
      _ ≤ Real.exp (ε ^ 2 / 256 * (s : ℝ) ^ 2) := by
          apply Real.exp_le_exp.2
          have : 400 * (s : ℝ) ≤ ε ^ 2 / 256 * (s : ℝ) ^ 2 := by
            have := mul_le_mul_of_nonneg_right hsε hs0.le
            nlinarith
          nlinarith
  have hE0 : 0 ≤ (1 - ε ^ 2 / 256) ^ qV ε := pow_nonneg hη0 _
  calc 4 * ((ellV (qV ε) * MV ε (qV ε) : ℕ) : ℝ) * (1 - ε ^ 2 / 256) ^ qV ε
      ≤ Real.exp (ε ^ 2 / 256 * (s : ℝ) ^ 2) * Real.exp (-(ε ^ 2 / 256 * (s : ℝ) ^ 2)) := by
        apply mul_le_mul (hA.trans hbig) hexp1 hE0 (Real.exp_pos _).le
    _ = 1 := by rw [← Real.exp_add]; simp

theorem hcodes_V (q : ℕ) : 4 * nCodes q ≤ 2 ^ ellV q := Nat.le_pow_clog (by norm_num) _

theorem hM_V (ε : ℝ) (q : ℕ) : ∀ K0 ≤ kMax q, m11V (ε ^ 2 / 256 / 2) K0 ≤ MV ε q :=
  fun _ h => m11V_mono _ h

end E34
