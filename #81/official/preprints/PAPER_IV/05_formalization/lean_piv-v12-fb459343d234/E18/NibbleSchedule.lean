import Nibble.TightNibble

/-!
# E18 — the tight-band nibble schedule with explicit constants

`Nibble.exists_tightParams` only states `Nonempty (TightParams r β)`.  The schedule
built in its proof is, however, a closed formula.  This file writes the scalar
parameters down as definitions and re-proves the existence statement recording
their values (adapted copy of the original proof; no original file is modified).
-/

open Finset Hypergraph

namespace E18.Nib

/-! ## 1. The explicit schedule parameters (for `0 < β < 1`) -/

/-- The drop constant `a = (r-1)/r`. -/
noncomputable def aT (r : ℕ) : ℝ := ((r : ℝ) - 1) / r
/-- The logarithmic scale `L = log (1/β)`. -/
noncomputable def LT (β : ℝ) : ℝ := -Real.log β
/-- `M = 16 r L + 1`. -/
noncomputable def MT (r : ℕ) (β : ℝ) : ℝ := 16 * (r : ℝ) * LT β + 1
/-- The round rate `γ = min (1/8) (exp(-8M-1)/32)`. -/
noncomputable def gamT (r : ℕ) (β : ℝ) : ℝ := min (1 / 8) (Real.exp (-(8 * MT r β) - 1) / 32)
/-- The band tolerance `ε = 4 a γ`. -/
noncomputable def epsT (r : ℕ) (β : ℝ) : ℝ := 4 * aT r * gamT r β
/-- `q = 1 - a γ`. -/
noncomputable def qT (r : ℕ) (β : ℝ) : ℝ := 1 - aT r * gamT r β
/-- The number of rounds `T = ⌈M/γ⌉`. -/
noncomputable def TT (r : ℕ) (β : ℝ) : ℕ := ⌈MT r β / gamT r β⌉₊
/-- The exceptional growth factor `G = (2 + r/(εγ))²`. -/
noncomputable def GgT (r : ℕ) (β : ℝ) : ℝ := (2 + (r : ℝ) / (epsT r β * gamT r β)) ^ 2
/-- The exceptional fraction `θ = η = β / (8 (2G)^T)`. -/
noncomputable def excT (r : ℕ) (β : ℝ) : ℝ := β / (8 * (2 * GgT r β) ^ TT r β)
/-- The band floor `3/4 · q^T`. -/
noncomputable def lominT (r : ℕ) (β : ℝ) : ℝ := 3 / 4 * qT r β ^ TT r β

set_option maxHeartbeats 400000 in
/-- **The tight-band schedule with its explicit parameters.**  Adapted copy of
`Nibble.exists_tightParams`, additionally recording the values of the scalar fields. -/
theorem exists_tightParams_explicit (r : ℕ) (hr : 2 ≤ r) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ Pm : Nibble.TightParams r β, Pm.gam = gamT r β ∧ Pm.eps = epsT r β ∧
      Pm.exc = excT r β ∧ Pm.eta = excT r β ∧ Pm.wid = 8 * gamT r β ∧
      Pm.lomin = lominT r β ∧ Pm.T = TT r β := by
  classical
  have hrR : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hr0 : (0 : ℝ) < (r : ℝ) := by linarith only [hrR]
  obtain ⟨a, hadef⟩ : ∃ x : ℝ, x = ((r : ℝ) - 1) / r := ⟨_, rfl⟩
  have ha1 : (1 : ℝ) / 2 ≤ a := by rw [hadef, le_div_iff₀ hr0]; linarith only [hrR]
  have ha2 : a ≤ 1 := by rw [hadef, div_le_one hr0]; linarith only []
  have ha0 : (0 : ℝ) ≤ a := by linarith only [ha1]
  obtain ⟨L, hLdef⟩ : ∃ x : ℝ, x = -Real.log β := ⟨_, rfl⟩
  have hLpos : 0 < L := by rw [hLdef]; have := Real.log_neg hβ0 hβ1; linarith only [this]
  obtain ⟨M, hMdef⟩ : ∃ x : ℝ, x = 16 * (r : ℝ) * L + 1 := ⟨_, rfl⟩
  have hM1 : (1 : ℝ) ≤ M := by rw [hMdef]; linarith only [mul_pos hr0 hLpos]
  have hM0 : (0 : ℝ) < M := by linarith only [hM1]
  obtain ⟨gam, hgdef⟩ : ∃ x : ℝ, x = min (1 / 8) (Real.exp (-(8 * M) - 1) / 32) := ⟨_, rfl⟩
  have hgam8 : gam ≤ 1 / 8 := by rw [hgdef]; exact min_le_left _ _
  have hgamE : gam ≤ Real.exp (-(8 * M) - 1) / 32 := by rw [hgdef]; exact min_le_right _ _
  have hgam : 0 < gam := by
    rw [hgdef]; exact lt_min (by norm_num) (by positivity)
  obtain ⟨eps, hepsdef⟩ : ∃ x : ℝ, x = 4 * a * gam := ⟨_, rfl⟩
  have hagam : (0 : ℝ) < a * gam := mul_pos (by linarith only [ha1]) hgam
  have hagam8 : a * gam ≤ 1 * (1 / 8) :=
    mul_le_mul ha2 hgam8 hgam.le (by norm_num)
  have hepspos : 0 < eps := by rw [hepsdef]; linarith only [hagam]
  have hepsle : eps ≤ 1 := by rw [hepsdef]; linarith only [hagam8]
  obtain ⟨q, hqdef⟩ : ∃ x : ℝ, x = 1 - a * gam := ⟨_, rfl⟩
  have hqpos : 0 < q := by rw [hqdef]; linarith only [hagam8]
  have hq1 : q ≤ 1 := by rw [hqdef]; linarith only [hagam]
  obtain ⟨T, hTdef⟩ : ∃ m : ℕ, m = ⌈M / gam⌉₊ := ⟨_, rfl⟩
  have hgamT_lb : M ≤ gam * (T : ℝ) := by
    have h := Nat.le_ceil (M / gam)
    rw [← hTdef] at h
    rw [div_le_iff₀ hgam] at h
    linarith only [h]
  have hgamT_ub : gam * (T : ℝ) ≤ M + gam := by
    have h := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ M / gam by positivity)
    rw [← hTdef] at h
    have h2 : (T : ℝ) * gam < (M / gam + 1) * gam :=
      mul_lt_mul_of_pos_right h hgam
    rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hgam)] at h2
    linarith only [h2]
  obtain ⟨nf, hnfdef⟩ : ∃ f : ℕ → ℝ, f = fun k => 8 * gam * (1 + 8 * a * gam) ^ k := ⟨_, rfl⟩
  have hnfa : ∀ k, nf k = 8 * gam * (1 + 8 * a * gam) ^ k := by intro k; rw [hnfdef]
  have hbase1 : (1 : ℝ) ≤ 1 + 8 * a * gam := by linarith only [hagam]
  have hnf_lb : ∀ k, 8 * gam ≤ nf k := by
    intro k
    rw [hnfa k]
    have : (1 : ℝ) ≤ (1 + 8 * a * gam) ^ k := one_le_pow₀ hbase1
    linarith only [mul_nonneg hgam.le (sub_nonneg.mpr this)]
  have hnf_ub : ∀ k, k ≤ T → nf k ≤ 1 / 4 := by
    intro k hk
    have hp1 : (1 + 8 * a * gam) ^ k ≤ (1 + 8 * a * gam) ^ T := pow_le_pow_right₀ hbase1 hk
    have hexpb : 1 + 8 * a * gam ≤ Real.exp (8 * a * gam) := by
      linarith only [Real.add_one_le_exp (8 * a * gam)]
    have hp2 : (1 + 8 * a * gam) ^ T ≤ Real.exp (8 * a * gam) ^ T :=
      pow_le_pow_left₀ (by linarith) hexpb T
    have hp3 : Real.exp (8 * a * gam) ^ T = Real.exp ((T : ℝ) * (8 * a * gam)) :=
      (Real.exp_nat_mul _ _).symm
    have hle : (T : ℝ) * (8 * a * gam) ≤ 8 * M + 1 := by
      have h1 : (T : ℝ) * (8 * a * gam) = 8 * a * (gam * (T : ℝ)) := by ring
      have h2 : gam * (T : ℝ) ≤ M + gam := hgamT_ub
      have h3 : (0 : ℝ) ≤ gam * (T : ℝ) := by positivity
      linarith only [h1, hgam8,
        mul_le_mul_of_nonneg_left h2 (show (0 : ℝ) ≤ 8 * a by linarith only [ha0]),
        mul_le_mul_of_nonneg_right ha2 (show (0 : ℝ) ≤ M + gam by linarith only [hM0, hgam])]
    have hp4 : Real.exp ((T : ℝ) * (8 * a * gam)) ≤ Real.exp (8 * M + 1) :=
      Real.exp_le_exp.mpr hle
    have hchain : (1 + 8 * a * gam) ^ k ≤ Real.exp (8 * M + 1) := by
      calc (1 + 8 * a * gam) ^ k ≤ (1 + 8 * a * gam) ^ T := hp1
        _ ≤ Real.exp (8 * a * gam) ^ T := hp2
        _ = Real.exp ((T : ℝ) * (8 * a * gam)) := hp3
        _ ≤ Real.exp (8 * M + 1) := hp4
    have hexpprod : Real.exp (-(8 * M) - 1) * Real.exp (8 * M + 1) = 1 := by
      rw [← Real.exp_add]
      norm_num
    have hEpos : (0 : ℝ) < Real.exp (8 * M + 1) := Real.exp_pos _
    rw [hnfa k]
    calc 8 * gam * (1 + 8 * a * gam) ^ k
        ≤ 8 * gam * Real.exp (8 * M + 1) := by
          linarith only [mul_le_mul_of_nonneg_left hchain
            (show (0 : ℝ) ≤ 8 * gam by linarith only [hgam])]
      _ ≤ 8 * (Real.exp (-(8 * M) - 1) / 32) * Real.exp (8 * M + 1) := by
          linarith only [mul_le_mul_of_nonneg_right hgamE hEpos.le]
      _ = (Real.exp (-(8 * M) - 1) * Real.exp (8 * M + 1)) / 4 := by ring
      _ = 1 / 4 := by rw [hexpprod]
  obtain ⟨lo, hlodef⟩ : ∃ f : ℕ → ℝ, f = fun k => q ^ k * (1 - nf k) := ⟨_, rfl⟩
  obtain ⟨hi, hhidef⟩ : ∃ f : ℕ → ℝ, f = fun k => q ^ k * (1 + nf k) := ⟨_, rfl⟩
  have hloa : ∀ k, lo k = q ^ k * (1 - nf k) := by intro k; rw [hlodef]
  have hhia : ∀ k, hi k = q ^ k * (1 + nf k) := by intro k; rw [hhidef]
  have hqk : ∀ k : ℕ, (0 : ℝ) < q ^ k := fun k => pow_pos hqpos k
  obtain ⟨Gg, hGdef⟩ : ∃ x : ℝ, x = (2 + (r : ℝ) / (eps * gam)) ^ 2 := ⟨_, rfl⟩
  have hGge : (4 : ℝ) ≤ Gg := by
    rw [hGdef]
    have hpos : (0 : ℝ) < (r : ℝ) / (eps * gam) := by positivity
    nlinarith only [hpos]
  have hGpow : ∀ k : ℕ, (1 : ℝ) ≤ (2 * Gg) ^ k := by
    intro k; exact one_le_pow₀ (by linarith)
  have hGpowpos : ∀ k : ℕ, (0 : ℝ) < (2 * Gg) ^ k := fun k => lt_of_lt_of_le one_pos (hGpow k)
  obtain ⟨exc, hexcdef⟩ : ∃ x : ℝ, x = β / (8 * (2 * Gg) ^ T) := ⟨_, rfl⟩
  have hexcpos : 0 < exc := by
    rw [hexcdef]; exact div_pos hβ0 (by linarith only [hGpowpos T])
  have hexcle : exc ≤ 1 := by
    rw [hexcdef, div_le_one (by linarith only [hGpowpos T])]
    linarith only [hGpow T, hβ1]
  obtain ⟨sig, hsigdef⟩ : ∃ f : ℕ → ℝ, f = fun k => 2 * exc * (2 * Gg) ^ k := ⟨_, rfl⟩
  have hsiga : ∀ k, sig k = 2 * exc * (2 * Gg) ^ k := by intro k; rw [hsigdef]
  have key : ∃ Pm : Nibble.TightParams r β, Pm.gam = gam ∧ Pm.eps = eps ∧
      Pm.exc = exc ∧ Pm.eta = exc ∧ Pm.wid = 8 * gam ∧
      Pm.lomin = 3 / 4 * q ^ T ∧ Pm.T = T := by
    refine ⟨{
      gam := gam
      eps := eps
      exc := exc
      eta := exc
      wid := 8 * gam
      lomin := 3 / 4 * q ^ T
      T := T
      lo := lo
      hi := hi
      sig := sig
      gam_pos := hgam
      gam_le := by linarith only [hgam8]
      eps_pos := hepspos
      eps_le := hepsle
      two_gam_le_eps := by
        rw [hepsdef]
        linarith only [mul_nonneg (show (0 : ℝ) ≤ 4 * a - 2 by linarith only [ha1]) hgam.le]
      exc_pos := hexcpos
      exc_le := hexcle
      eta_pos := hexcpos
      wid_pos := by linarith only [hgam]
      lomin_pos := by positivity
      lomin_le := ?_
      hi_le_two_lo := ?_
      lo_le_hi := ?_
      init_lo := ?_
      init_hi := ?_
      step_lo := ?_
      step_hi := ?_
      sig_init := ?_
      sig_step := ?_
      sig_le := ?_
      decay := ?_ }, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · intro k hk
      rw [hloa k]
      have h1 : q ^ T ≤ q ^ k := pow_le_pow_of_le_one hqpos.le hq1 hk
      have h2 : nf k ≤ 1 / 4 := hnf_ub k hk
      linarith only [h1, mul_le_mul_of_nonneg_left h2 (hqk k).le]
    · intro k hk
      rw [hloa k, hhia k]
      have h2 : nf k ≤ 1 / 4 := hnf_ub k hk
      linarith only [mul_le_mul_of_nonneg_left h2 (hqk k).le, (hqk k).le]
    · intro k _
      rw [hloa k, hhia k]
      have h0 : (0 : ℝ) ≤ nf k := le_trans (by positivity) (hnf_lb k)
      linarith only [mul_nonneg (hqk k).le h0]
    · rw [hloa 0, hnfa 0]
      norm_num
    · rw [hhia 0, hnfa 0]
      norm_num
    · intro k hk
      have hkT : k ≤ T := le_of_lt hk
      have hnk : 8 * gam ≤ nf k := hnf_lb k
      have hnk4 : nf k ≤ 1 / 4 := hnf_ub k hkT
      have hsucc : nf (k + 1) = nf k * (1 + 8 * a * gam) := by
        rw [hnfa (k + 1), hnfa k, pow_succ]; ring
      have hcore := Nibble.tight_band_step_lo_core ha2 hgam hgam8 hnk hnk4
      have hprod : 0 ≤ a * gam * (6 * nf k - 8 * gam - 8 * gam * nf k - 8 * a * gam * nf k) :=
        mul_nonneg (mul_nonneg ha0 hgam.le) hcore
      have hscal : q * (1 - nf k * (1 + 8 * a * gam))
          ≤ (1 - nf k) - (a + 2 * eps) * gam * (1 + nf k) := by
        rw [hqdef, hepsdef]
        linarith only [hprod]
      have hmul : q ^ k * (q * (1 - nf k * (1 + 8 * a * gam)))
          ≤ q ^ k * ((1 - nf k) - (a + 2 * eps) * gam * (1 + nf k)) :=
        mul_le_mul_of_nonneg_left hscal (hqk k).le
      rw [hloa (k + 1), hloa k, hhia k, hsucc, pow_succ, ← hadef]
      linarith only [hmul]
    · intro k hk
      have hkT : k ≤ T := le_of_lt hk
      have hnk : 8 * gam ≤ nf k := hnf_lb k
      have hnk4 : nf k ≤ 1 / 4 := hnf_ub k hkT
      have hn0 : (0 : ℝ) ≤ nf k := by linarith [hgam]
      have h1n : (0 : ℝ) < 1 + nf k := by linarith only [hn0]
      have hsucc : nf (k + 1) = nf k * (1 + 8 * a * gam) := by
        rw [hnfa (k + 1), hnfa k, pow_succ]; ring
      have hcore := Nibble.tight_band_step_hi_core ha1 ha2 hgam hgam8 hnk hnk4
      have hinner : 0 ≤ 4 * a * nf k + 8 * a * (nf k) ^ 2 - a * gam * (1 - nf k) ^ 2
          - 8 * a ^ 2 * gam * nf k * (1 + nf k) - eps * (1 + nf k) ^ 2
          - a * eps * gam * (1 + nf k) * (1 - nf k) * (1 - gam) := by
        rw [hepsdef]; linarith only [hcore]
      have hprod : 0 ≤ gam * (4 * a * nf k + 8 * a * (nf k) ^ 2 - a * gam * (1 - nf k) ^ 2
          - 8 * a ^ 2 * gam * nf k * (1 + nf k) - eps * (1 + nf k) ^ 2
          - a * eps * gam * (1 + nf k) * (1 - nf k) * (1 - gam)) :=
        mul_nonneg hgam.le hinner
      have hexpand : ((1 + nf k)
            - a * gam * ((1 - nf k - eps * gam * (1 + nf k)) * (1 - nf k) * (1 - gam)) / (1 + nf k)
            + eps * gam * (1 + nf k)) * (1 + nf k)
          = (1 + nf k) ^ 2 + eps * gam * (1 + nf k) ^ 2
            - a * gam * ((1 - nf k - eps * gam * (1 + nf k)) * (1 - nf k) * (1 - gam)) := by
        field_simp
        ring
      have hpoly : (1 + nf k) ^ 2 + eps * gam * (1 + nf k) ^ 2
            - a * gam * ((1 - nf k - eps * gam * (1 + nf k)) * (1 - nf k) * (1 - gam))
          ≤ ((1 - a * gam) * (1 + nf k * (1 + 8 * a * gam))) * (1 + nf k) := by
        linarith only [hprod]
      have hscal : (1 + nf k)
            - a * gam * ((1 - nf k - eps * gam * (1 + nf k)) * (1 - nf k) * (1 - gam)) / (1 + nf k)
            + eps * gam * (1 + nf k)
          ≤ (1 - a * gam) * (1 + nf k * (1 + 8 * a * gam)) := by
        refine le_of_mul_le_mul_right ?_ h1n
        rw [hexpand]
        exact hpoly
      rw [← hqdef] at hscal
      have hmul := mul_le_mul_of_nonneg_left hscal (hqk k).le
      rw [hhia (k + 1), hhia k, hloa k, hsucc, pow_succ, ← hadef]
      have hqkne : q ^ k ≠ 0 := ne_of_gt (hqk k)
      have h1nne : (1 : ℝ) + nf k ≠ 0 := ne_of_gt h1n
      have hLHS : q ^ k * (1 + nf k)
            - a * gam * (q ^ k * (1 - nf k) - eps * gam * (q ^ k * (1 + nf k))) * (q ^ k * (1 - nf k))
                * (1 - gam) / (q ^ k * (1 + nf k))
            + eps * gam * (q ^ k * (1 + nf k))
          = q ^ k * ((1 + nf k)
            - a * gam * ((1 - nf k - eps * gam * (1 + nf k)) * (1 - nf k) * (1 - gam)) / (1 + nf k)
            + eps * gam * (1 + nf k)) := by
        field_simp
      rw [hLHS]
      linarith only [hmul]
    · rw [hsiga 0, pow_zero]
      linarith only [hexcpos]
    · intro k _
      rw [hsiga k, hsiga (k + 1), ← hGdef]
      have h1 : (1 : ℝ) ≤ (2 * Gg) ^ k := hGpow k
      have hpow : (2 * Gg) ^ (k + 1) = 2 * Gg * (2 * Gg) ^ k := by rw [pow_succ]; ring
      rw [hpow]
      linarith only [mul_nonneg (mul_nonneg (show (0 : ℝ) ≤ Gg by linarith only [hGge])
          hexcpos.le) (show (0 : ℝ) ≤ (2 * Gg) ^ k - 1 by linarith only [h1]),
        mul_nonneg (show (0 : ℝ) ≤ Gg by linarith only [hGge]) hexcpos.le]
    · intro k hk
      rw [hsiga k, hexcdef]
      have h1 : (2 * Gg) ^ k ≤ (2 * Gg) ^ T := pow_le_pow_right₀ (by linarith) hk
      have hTpos : (0 : ℝ) < (2 * Gg) ^ T := hGpowpos T
      have hrw : 2 * (β / (8 * (2 * Gg) ^ T)) * (2 * Gg) ^ k
          = β * (2 * Gg) ^ k / (4 * (2 * Gg) ^ T) := by
        field_simp
        ring
      rw [hrw, div_le_iff₀ (by linarith : (0 : ℝ) < 4 * (2 * Gg) ^ T)]
      linarith only [mul_le_mul_of_nonneg_left h1 hβ0.le, mul_nonneg hβ0.le hTpos.le]
    · have hcpos : (0 : ℝ) < gam / (16 * r) := by positivity
      have hcsmall : gam / (16 * r) ≤ 1 / 8 := by
        rw [div_le_div_iff₀ (by linarith) (by norm_num)]
        linarith only [hgam8, hrR]
      have h1 : (1 : ℝ) - gam / (16 * r) ≤ Real.exp (-(gam / (16 * r))) := by
        linarith only [Real.add_one_le_exp (-(gam / (16 * r)))]
      have h2 : (0 : ℝ) ≤ 1 - gam / (16 * r) := by linarith only [hcsmall]
      have h3 : (1 - gam / (16 * r)) ^ T ≤ Real.exp (-(gam / (16 * r))) ^ T :=
        pow_le_pow_left₀ h2 h1 T
      have h4 : Real.exp (-(gam / (16 * r))) ^ T = Real.exp ((T : ℝ) * -(gam / (16 * r))) :=
        (Real.exp_nat_mul _ _).symm
      have h5 : (T : ℝ) * -(gam / (16 * r)) ≤ -L := by
        have hML : L ≤ M / (16 * (r : ℝ)) := by
          rw [le_div_iff₀ (by linarith), hMdef]
          linarith only [hLpos]
        have h6 : M / (16 * (r : ℝ)) ≤ gam * (T : ℝ) / (16 * (r : ℝ)) := by
          apply div_le_div_of_nonneg_right hgamT_lb (by linarith)
        have h7 : (T : ℝ) * -(gam / (16 * r)) = -(gam * (T : ℝ) / (16 * (r : ℝ))) := by
          field_simp
        rw [h7]
        linarith only [hML, h6]
      have h8 : Real.exp ((T : ℝ) * -(gam / (16 * r))) ≤ Real.exp (-L) := Real.exp_le_exp.mpr h5
      have h9 : Real.exp (-L) = β := by rw [hLdef, neg_neg]; exact Real.exp_log hβ0
      calc (1 - gam / (16 * r)) ^ T ≤ Real.exp (-(gam / (16 * r))) ^ T := h3
        _ = Real.exp ((T : ℝ) * -(gam / (16 * r))) := h4
        _ ≤ Real.exp (-L) := h8
        _ = β := h9
  subst hadef hLdef hMdef hgdef hepsdef hqdef hTdef hGdef hexcdef
  exact key

end E18.Nib
