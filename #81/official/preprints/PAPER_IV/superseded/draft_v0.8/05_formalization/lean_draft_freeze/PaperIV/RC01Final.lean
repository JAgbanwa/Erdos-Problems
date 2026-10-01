import PaperIV.RC01UniformDenseGate
import PaperIV.RC01TriangleTransfer
import PaperIV.RC01DenseAssembly
import PaperIV.RC01TriangleSchedule

/-!
# RC01: the final assembly

This module closes the RC01 route: for every positive rational `ε`, the uniform
rounding target `MixedRounding.UniformRoundingTarget ε` holds.

Nothing new is proved about the geometry or about the nibble.  The module fixes
one rational hierarchy `δ, d, θ, u, v, k₀` from `ε`, one order threshold `N`
large enough for regularity, for the cluster scale, for the additive nibble
constant `12 + 10 D` and for the triangle threshold, and then chains the pieces
that are already available:

* `RegularityFormat.exists_equalRegularity` produces the partition;
* `RC01GlobalSchedule` discharges the codegree and light-profile accounts from
  the polynomial profile cardinality bounds;
* `RC01TriangleTransfer` turns a large triangle mass of the input into a large
  triangle mass of the cleaned packing, which is the last hypothesis of the
  physical gate;
* `RC01UniformDenseGate` runs the gate and `RC01DenseAssembly` charges the whole
  deterministic ledger to `ε n² / 2`;
* `RC01TriangleSchedule` joins that high-mass branch with the low-triangle
  branch of `TriangleSwap`.
-/

namespace PaperIV.RC01Final

open Finset
open MixedRounding
open PaperIV.PatternTransfer
open PaperIV.PartitionBridge
open PaperIV.RegularityFormat
open PaperIV.RC01CleanedGate
open PaperIV.RC01CleanFiber
open PaperIV.RC01RootwiseReference
open PaperIV.RC01ResidualTransferClosure
open PaperIV.RC01DenseRootwiseRetention
open PaperIV.RC01MixedPatterns

/-! ## 1. The one-parameter rational hierarchy -/

/-- The scale parameter of the hierarchy: `d = u = v = s`. -/
theorem exists_scale (ε : ℚ) (hε : 0 < ε) :
    ∃ s : ℚ, 0 < s ∧ s ≤ 1 / 10 ∧ 15 * s ≤ ε / 300 := by
  refine ⟨min (ε / 4500) (1 / 10), ?_, min_le_right _ _, ?_⟩
  · exact lt_min (by linarith) (by norm_num)
  · have h : min (ε / 4500) (1 / 10) ≤ ε / 4500 := min_le_left _ _
    linarith

section Hierarchy

variable {s : ℚ}

/-- The regularity parameter attached to the scale `s`. -/
def deltaOf (s : ℚ) : ℚ := s ^ 21 / 2208

theorem deltaOf_pos (hs : 0 < s) : 0 < deltaOf s := by
  have : 0 < s ^ 21 := pow_pos hs 21
  rw [deltaOf]; positivity

theorem deltaOf_le (hs : 0 < s) (hs1 : s ≤ 1 / 10) : deltaOf s ≤ s := by
  have h1 : s ^ 21 ≤ s ^ 1 := pow_le_pow_of_le_one hs.le (by linarith) (by norm_num)
  rw [deltaOf]
  simp only [pow_one] at h1
  linarith

theorem deltaOf_le_pow3 (hs : 0 < s) (hs1 : s ≤ 1 / 10) :
    deltaOf s ≤ s ^ 3 / 2208 := by
  have h1 : s ^ 21 ≤ s ^ 3 := pow_le_pow_of_le_one hs.le (by linarith) (by norm_num)
  rw [deltaOf]
  linarith

theorem deltaOf_le_pow6 (hs : 0 < s) (hs1 : s ≤ 1 / 10) :
    deltaOf s ≤ s ^ 6 / 2208 := by
  have h1 : s ^ 21 ≤ s ^ 6 := pow_le_pow_of_le_one hs.le (by linarith) (by norm_num)
  rw [deltaOf]
  linarith

theorem deltaOf_le_pow12 (hs : 0 < s) (hs1 : s ≤ 1 / 10) :
    deltaOf s ≤ s ^ 12 / 2208 := by
  have h1 : s ^ 21 ≤ s ^ 12 := pow_le_pow_of_le_one hs.le (by linarith) (by norm_num)
  rw [deltaOf]
  linarith

theorem pow3_half_le (hs : 0 < s) (hs1 : s ≤ 1 / 10) :
    s ^ 3 / 2 ≤ s ^ 3 - 3 * deltaOf s := by
  have h := deltaOf_le_pow3 hs hs1
  have h3 : 0 < s ^ 3 := pow_pos hs 3
  linarith

theorem pow6_half_le (hs : 0 < s) (hs1 : s ≤ 1 / 10) :
    s ^ 6 / 2 ≤ s ^ 6 - 6 * deltaOf s := by
  have h := deltaOf_le_pow6 hs hs1
  have h6 : 0 < s ^ 6 := pow_pos hs 6
  linarith

theorem cube3_pos (hs : 0 < s) (hs1 : s ≤ 1 / 10) : 0 < s ^ 3 - 3 * deltaOf s := by
  have h := pow3_half_le hs hs1
  have h3 : 0 < s ^ 3 := pow_pos hs 3
  linarith

theorem cube4_pos (hs : 0 < s) (hs1 : s ≤ 1 / 10) : 0 < s ^ 6 - 6 * deltaOf s := by
  have h := pow6_half_le hs hs1
  have h6 : 0 < s ^ 6 := pow_pos hs 6
  linarith

theorem choice3 (hs : 0 < s) (hs1 : s ≤ 1 / 10) :
    33 * deltaOf s ≤ s * s ^ 2 * (s ^ 3 - 3 * deltaOf s) ^ 3 := by
  have hcube : (s ^ 3 / 2) ^ 3 ≤ (s ^ 3 - 3 * deltaOf s) ^ 3 := by
    refine pow_le_pow_left₀ ?_ (pow3_half_le hs hs1) 3
    have : 0 < s ^ 3 := pow_pos hs 3
    linarith
  have hs3 : (0 : ℚ) < s ^ 3 := pow_pos hs 3
  have hmul : s ^ 3 * (s ^ 3 / 2) ^ 3 ≤ s ^ 3 * (s ^ 3 - 3 * deltaOf s) ^ 3 :=
    mul_le_mul_of_nonneg_left hcube hs3.le
  have hlhs : 33 * deltaOf s ≤ s ^ 12 / 8 := by
    have h := deltaOf_le_pow12 hs hs1
    have h12 : (0 : ℚ) ≤ s ^ 12 := by positivity
    linarith
  have hchain : s ^ 12 / 8 ≤ s ^ 3 * (s ^ 3 - 3 * deltaOf s) ^ 3 := by
    calc s ^ 12 / 8 = s ^ 3 * (s ^ 3 / 2) ^ 3 := by ring
      _ ≤ s ^ 3 * (s ^ 3 - 3 * deltaOf s) ^ 3 := hmul
  have hid2 : s * s ^ 2 * (s ^ 3 - 3 * deltaOf s) ^ 3
      = s ^ 3 * (s ^ 3 - 3 * deltaOf s) ^ 3 := by ring
  rw [hid2]
  linarith

theorem choice4 (hs : 0 < s) (hs1 : s ≤ 1 / 10) :
    138 * deltaOf s ≤ s * s ^ 2 * (s ^ 6 - 6 * deltaOf s) ^ 3 := by
  have hcube : (s ^ 6 / 2) ^ 3 ≤ (s ^ 6 - 6 * deltaOf s) ^ 3 := by
    refine pow_le_pow_left₀ ?_ (pow6_half_le hs hs1) 3
    have : 0 < s ^ 6 := pow_pos hs 6
    linarith
  have hs3 : (0 : ℚ) < s ^ 3 := pow_pos hs 3
  have hmul : s ^ 3 * (s ^ 6 / 2) ^ 3 ≤ s ^ 3 * (s ^ 6 - 6 * deltaOf s) ^ 3 :=
    mul_le_mul_of_nonneg_left hcube hs3.le
  have hlhs : 138 * deltaOf s ≤ s ^ 21 / 16 := by
    rw [deltaOf]; linarith
  have hchain : s ^ 21 / 8 ≤ s ^ 3 * (s ^ 6 - 6 * deltaOf s) ^ 3 := by
    calc s ^ 21 / 8 = s ^ 3 * (s ^ 6 / 2) ^ 3 := by ring
      _ ≤ s ^ 3 * (s ^ 6 - 6 * deltaOf s) ^ 3 := hmul
  have hid2 : s * s ^ 2 * (s ^ 6 - 6 * deltaOf s) ^ 3
      = s ^ 3 * (s ^ 6 - 6 * deltaOf s) ^ 3 := by ring
  have h21 : (0 : ℚ) < s ^ 21 := pow_pos hs 21
  rw [hid2]
  linarith

/-- The retained triangular mass after the transfer budget. -/
theorem retained_mass_bound {cst Sum tri budget bud : ℚ}
    (hs : 0 < s) (hs1 : s ≤ 1 / 10) (hcst : 0 ≤ cst)
    (htrans : tri ≤ Sum + budget) (hbudget : budget ≤ bud)
    (htri : 2 * cst + bud ≤ tri) :
    cst ≤ (1 - s - s) * Sum := by
  have h1 : 2 * cst ≤ Sum := by linarith
  have h2 : (1 / 2 : ℚ) * (2 * cst) ≤ (1 - s - s) * Sum :=
    mul_le_mul (by linarith) h1 (by linarith) (by linarith)
  linarith

end Hierarchy

/-! ## 2. The final theorem -/

set_option maxHeartbeats 1600000 in
/-- **RC01.**  For every positive rational `ε`, every large graph and every
mixed fractional packing have a physical packing that loses at most `ε n²`. -/
theorem rc01_uniformRoundingTarget (ε : ℚ) (hε : 0 < ε) :
    MixedRounding.UniformRoundingTarget ε := by
  classical
  obtain ⟨s, hs0, hs1, hsbudget⟩ := exists_scale ε hε
  set δ : ℚ := deltaOf s with hδdef
  have hδ0 : 0 < δ := deltaOf_pos hs0
  have hδs : δ ≤ s := deltaOf_le hs0 hs1
  have hc3 : 0 < s ^ 3 - 3 * δ := cube3_pos hs0 hs1
  have hc4 : 0 < s ^ 6 - 6 * δ := cube4_pos hs0 hs1
  have hchoice3 : 33 * δ ≤ s * s ^ 2 * (s ^ 3 - 3 * δ) ^ 3 := choice3 hs0 hs1
  have hchoice4 : 138 * δ ≤ s * s ^ 2 * (s ^ 6 - 6 * δ) ^ 3 := choice4 hs0 hs1
  -- the gate slack
  set zq : ℚ := min (ε / 10) 1 with hzqdef
  have hzq0 : 0 < zq := lt_min (by linarith) one_pos
  have hzq1 : zq ≤ 1 := min_le_right _ _
  have hzqε : zq ≤ ε / 10 := min_le_left _ _
  have hzqR0 : (0 : ℝ) < ((zq : ℚ) : ℝ) := by exact_mod_cast hzq0
  have hzqR1 : ((zq : ℚ) : ℝ) ≤ 1 := by exact_mod_cast hzq1
  obtain ⟨gam, hgam, Cst, hCst, D, hD, hgate⟩ :=
    PaperIV.RC01UniformDenseGate.exists_packing_mass_loss_le_denseActive_uniform
      ((zq : ℚ) : ℝ) hzqR0 hzqR1
  obtain ⟨gamma, hgamma0, hgammagam⟩ : ∃ q : ℚ, 0 < q ∧ (q : ℝ) ≤ gam := by
    obtain ⟨q, hq0, hqgam⟩ := exists_rat_btwn hgam
    exact ⟨q, by exact_mod_cast hq0, hqgam.le⟩
  set cst : ℚ := (⌈Cst⌉₊ : ℚ) with hcstdef
  have hcstR : Cst ≤ ((cst : ℚ) : ℝ) := by
    rw [hcstdef]; push_cast; exact Nat.le_ceil Cst
  have hcst0 : (0 : ℚ) ≤ cst := by rw [hcstdef]; positivity
  set k₀ : ℕ := ⌈(1500 / ε : ℚ)⌉₊ + 1 with hk₀def
  have hk₀pos : 0 < k₀ := Nat.succ_pos _
  have hk₀Q : (1500 / ε : ℚ) ≤ (k₀ : ℚ) := by
    have h := Nat.le_ceil (1500 / ε : ℚ)
    rw [hk₀def]
    push_cast
    linarith
  have hk₀Qpos : (0 : ℚ) < (k₀ : ℚ) := by exact_mod_cast hk₀pos
  have hk₀ε : 5 / (k₀ : ℚ) ≤ ε / 300 := by
    have h1500 : (1500 : ℚ) ≤ ε * (k₀ : ℚ) := by
      rw [div_le_iff₀ hε] at hk₀Q
      linarith [hk₀Q]
    rw [div_le_iff₀ hk₀Qpos]
    linarith
  obtain ⟨B, hBdef⟩ : ∃ B : ℕ,
      SzemerediRegularity.bound (((δ / 8 : ℚ) : ℝ)) k₀ = B := ⟨_, rfl⟩
  set light : ℚ := ε / 300 with hlightdef
  set a : ℚ := s ^ 3 - 3 * δ with hadef
  set b : ℚ := s ^ 6 - 6 * δ with hbdef
  set scaleBound : ℚ := 4 * (B : ℚ) ^ 5 * (a + b) / (gamma * a * b) with hscaledef
  set massBound : ℚ := 50 * (1 + 2 * cst) / ε with hmassdef
  set N : ℕ :=
    max (max k₀ ⌈(B : ℚ) / δ⌉₊)
      (max ⌈(12 + 10 * D) / ((zq : ℚ) : ℝ)⌉₊ (max ⌈scaleBound⌉₊ ⌈massBound⌉₊)) + 1
    with hNdef
  refine ⟨N, ?_⟩
  intro n hn G _ x
  -- unpacking the threshold
  have hn1 : 1 ≤ n := le_trans (Nat.le_add_left 1 _) hn
  haveI : NeZero n := ⟨by omega⟩
  have hnk₀ : k₀ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _))
    (le_trans (Nat.le_add_right _ 1) hn)
  have hnB : ⌈(B : ℚ) / δ⌉₊ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _))
    (le_trans (Nat.le_add_right _ 1) hn)
  have hnD : ⌈(12 + 10 * D) / ((zq : ℚ) : ℝ)⌉₊ ≤ n :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
      (le_trans (Nat.le_add_right _ 1) hn)
  have hnS : ⌈scaleBound⌉₊ ≤ n :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _))
      (le_trans (Nat.le_add_right _ 1) hn)
  have hnM : ⌈massBound⌉₊ ≤ n :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _))
      (le_trans (Nat.le_add_right _ 1) hn)
  have hnQ : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hn1
  -- the regularity partition
  have hcardfin : Fintype.card (Fin n) = n := Fintype.card_fin n
  have hregn : ((SzemerediRegularity.bound (((δ / 8 : ℚ) : ℝ)) k₀ : ℕ) : ℚ)
      ≤ δ * (Fintype.card (Fin n) : ℚ) := by
    rw [hcardfin, hBdef]
    have h1 : ((B : ℚ) / δ) ≤ (n : ℚ) := by
      refine le_trans (Nat.le_ceil ((B : ℚ) / δ)) ?_
      exact_mod_cast hnB
    rw [div_le_iff₀ hδ0] at h1
    linarith
  obtain ⟨R, hkl, hkL⟩ := PaperIV.RegularityFormat.exists_equalRegularity (G := G)
    hδ0 hk₀pos (by rw [hcardfin]; exact hnk₀) hregn
  rw [hBdef] at hkL
  set k : ℕ := R.parts.card with hkdef
  have hk1 : 1 ≤ k := le_trans hk₀pos hkl
  have hBk : (k : ℚ) ≤ (B : ℚ) := by exact_mod_cast hkL
  have hB1 : (1 : ℚ) ≤ (B : ℚ) := le_trans (by exact_mod_cast hk1) hBk
  set θ : ℚ := light * (n : ℚ) ^ 2 / (10 * (B : ℚ) ^ 4) with hθdef
  have hθ0 : 0 ≤ θ := by
    rw [hθdef]
    have : (0:ℚ) ≤ light * (n:ℚ)^2 := by positivity
    positivity
  -- the size of a cluster
  have hsizeQ : (0 : ℚ) < (R.size : ℚ) := by exact_mod_cast R.size_pos
  have hsizelow : (n : ℚ) / (2 * (B : ℚ)) ≤ (R.size : ℚ) := by
    have hg := R.garbage
    rw [hcardfin] at hg
    rw [← hkdef] at hg
    have hδhalf : δ ≤ 1 / 2 := by linarith
    have hBpos : (0 : ℚ) < 2 * (B : ℚ) := by linarith
    rw [div_le_iff₀ hBpos]
    nlinarith [mul_le_mul_of_nonneg_left hBk hsizeQ.le]
  -- the codegree scale inequality
  have hscale : (2 * (k : ℚ) ^ 4) * (a + b) ≤ gamma * a * b * (R.size : ℚ) := by
    have hn' : scaleBound ≤ (n : ℚ) := by
      refine le_trans (Nat.le_ceil scaleBound) ?_
      exact_mod_cast hnS
    have habpos : (0 : ℚ) < gamma * a * b := by positivity
    rw [hscaledef, div_le_iff₀ habpos] at hn'
    have hk4 : (k : ℚ) ^ 4 ≤ (B : ℚ) ^ 4 := pow_le_pow_left₀ (by positivity) hBk 4
    have hBpos : (0 : ℚ) < 2 * (B : ℚ) := by linarith
    have hkey : 2 * (B : ℚ) ^ 4 * (a + b)
        ≤ gamma * a * b * ((n : ℚ) / (2 * (B : ℚ))) := by
      rw [← mul_div_assoc, le_div_iff₀ hBpos]
      have hring : 2 * (B : ℚ) ^ 4 * (a + b) * (2 * (B : ℚ))
          = 4 * (B : ℚ) ^ 5 * (a + b) := by ring
      rw [hring]
      linarith
    have hab0 : (0 : ℚ) ≤ 2 * (a + b) := by linarith
    nlinarith [mul_le_mul_of_nonneg_right hk4 hab0]
  -- the light-profile account
  have hlightterm : 5 * (((mixedPatterns R).card : ℚ)) * θ ≤ light * (n : ℚ) ^ 2 := by
    refine PaperIV.RC01GlobalSchedule.five_mul_mixedPatterns_theta_le R
      (by exact_mod_cast hk1) hθ0 ?_
    rw [← hkdef, hθdef]
    have hB4 : (0 : ℚ) < 10 * (B : ℚ) ^ 4 := by positivity
    have hk4 : (k : ℚ) ^ 4 ≤ (B : ℚ) ^ 4 := pow_le_pow_left₀ (by positivity) hBk 4
    have hln : (0 : ℚ) ≤ light * (n : ℚ) ^ 2 := by positivity
    rw [← mul_div_assoc, div_le_iff₀ hB4]
    nlinarith [mul_le_mul_of_nonneg_right hk4 hln]
  -- the additive nibble constant
  have hsizeD : 12 + 10 * D ≤ ((zq : ℚ) : ℝ) * (n : ℝ) ^ 2 := by
    have h1 : (12 + 10 * D) / ((zq : ℚ) : ℝ) ≤ (n : ℝ) := by
      refine le_trans (Nat.le_ceil ((12 + 10 * D) / ((zq : ℚ) : ℝ))) ?_
      exact_mod_cast hnD
    rw [div_le_iff₀ hzqR0] at h1
    nlinarith [sq_nonneg ((n : ℝ) - 1)]
  -- the triangle threshold
  set C : ℕ := ⌊ε * (n : ℚ) ^ 2 / 30⌋₊ with hCdef
  have hCle : 30 * (C : ℚ) ≤ ε * (n : ℚ) ^ 2 := by
    have h := Nat.floor_le (a := ε * (n : ℚ) ^ 2 / 30) (by positivity)
    rw [hCdef]
    linarith
  have hCge : ε * (n : ℚ) ^ 2 / 30 - 1 ≤ (C : ℚ) := by
    have h := Nat.sub_one_lt_floor (ε * (n : ℚ) ^ 2 / 30)
    rw [hCdef]
    linarith [h.le]
  -- the residual budget of the triangular transfer
  have hΔ : 5 * ((3 * δ + 1 / (k₀ : ℚ) + s) * (n : ℚ) ^ 2)
      + 5 * (((mixedPatterns R).card : ℚ) * θ) ≤ (ε / 75) * (n : ℚ) ^ 2 := by
    have h1 : 5 * (3 * δ + 1 / (k₀ : ℚ) + s) ≤ ε / 100 := by
      have hδterm : 15 * δ ≤ ε / 300 := by nlinarith
      have hsterm : 5 * s ≤ ε / 300 := by linarith
      have : 5 * (3 * δ + 1 / (k₀ : ℚ) + s) = 15 * δ + 5 / (k₀ : ℚ) + 5 * s := by
        field_simp
        ring
      rw [this]
      linarith
    have h2 : (0 : ℚ) ≤ (n : ℚ) ^ 2 := by positivity
    have h3 := mul_le_mul_of_nonneg_right h1 h2
    have h4 : 5 * (((mixedPatterns R).card : ℚ) * θ) ≤ light * (n : ℚ) ^ 2 := by
      linarith [hlightterm]
    rw [hlightdef] at h4
    nlinarith
  have hn1Q : (1 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn1
  have hn2 : (n : ℚ) ≤ (n : ℚ) ^ 2 := by nlinarith
  have hbound : 50 * (1 + 2 * cst) ≤ ε * (n : ℚ) ^ 2 := by
    have hmassn : massBound ≤ (n : ℚ) := by
      refine le_trans (Nat.le_ceil massBound) ?_
      exact_mod_cast hnM
    rw [hmassdef, div_le_iff₀ hε] at hmassn
    nlinarith only [hmassn, hn2, hε, hcst0]
  -- the six deterministic accounts
  have huv0 : (0 : ℚ) ≤ s + s := by linarith
  have hbud1 : 15 * δ ≤ ε / 100 := by linarith
  have hbud2 : 5 * s ≤ ε / 10 := by linarith
  have hbud3 : (5 / 6 : ℚ) * (s + s) ≤ ε / 10 := by linarith
  have hbud4 : 5 / (k₀ : ℚ) ≤ ε / 10 := by linarith
  have hbud5 : light ≤ ε / 20 := by rw [hlightdef]; linarith
  -- the high-triangle branch
  have hgateT : ∀ z : FracPacking G, ((C : ℕ) : ℝ) ≤
      PaperIV.JointTwoQuotaPhysical.triangleMass z →
      ∃ Pk : Packing G, ((z.value : ℚ) : ℝ) - (Pk.gain : ℝ)
        ≤ (((ε / 2 : ℚ) : ℝ)) * (n : ℝ) ^ 2 := by
    intro z hz
    have hzQ : (C : ℚ) ≤ PaperIV.LowTriangleReduction.triMass z := by
      have := PaperIV.Corollary73Assembly.triMass_cast z
      rw [← this] at hz
      exact_mod_cast hz
    -- the triangular transfer
    have htrans := PaperIV.RC01TriangleTransfer.triMass_le_denseActive_triangles_add_budget
      hδ0.le R z s θ hs0.le hθ0 hk₀pos hkl
    rw [hcardfin] at htrans
    have htri : 2 * cst + (ε / 75) * (n : ℚ) ^ 2
        ≤ PaperIV.LowTriangleReduction.triMass z := by
      linarith only [hzQ, hCge, hbound]
    have hpsi3 : cst ≤ (1 - s - s) *
        (∑ H ∈ (denseActiveProfiles R z s θ).filter (fun H => H.card = 3),
          psiT z (partOf R) H) :=
      retained_mass_bound hs0 hs1 hcst0 htrans hΔ htri
    -- the geometric data of the gate
    have hvolpos := denseActiveProfiles_profileVolume_pos (θ := θ) hδ0.le hs0.le hc3 hc4 R z
    have hvolb : ∀ H ∈ denseActiveProfiles R z s θ, ∀ f : Sym2 (Fin n),
        rootwiseReference (G := G) (partOf R) H (partsOf (partOf R) f)
            * densT G (partOf R) f
          ≤ profileVolume (G := G) (partOf R) H :=
      fun H _ f => rootwiseReference_volume_budget (G := G) (partOf R) H f
    have hclean := denseActiveProfiles_clean_retention (θ := θ) hδ0.le hs0.le hs0 hs0.le
      hc3 hc4 (by exact hchoice3) (by exact hchoice4) R z
    have hmassclean := PaperIV.CleanedTriangleMass.cleanedPacking_triMass_ge z (partOf R)
      (denseActiveProfiles R z s θ) (rootwiseReference (G := G) (partOf R))
      (profileVolume (G := G) (partOf R)) s hs0.le hvolpos hvolb s hs0.le hclean
    have hmassR : Cst ≤ PaperIV.JointTwoQuotaPhysical.triangleMass
        (cleanedPacking z (partOf R) (denseActiveProfiles R z s θ)
          (rootwiseReference (G := G) (partOf R))
          (profileVolume (G := G) (partOf R)) s hs0.le hvolpos hvolb) := by
      have hQ : cst ≤ PaperIV.LowTriangleReduction.triMass
          (cleanedPacking z (partOf R) (denseActiveProfiles R z s θ)
            (rootwiseReference (G := G) (partOf R))
            (profileVolume (G := G) (partOf R)) s hs0.le hvolpos hvolb) :=
        le_trans hpsi3 hmassclean
      have hcast := PaperIV.Corollary73Assembly.triMass_cast
        (cleanedPacking z (partOf R) (denseActiveProfiles R z s θ)
          (rootwiseReference (G := G) (partOf R))
          (profileVolume (G := G) (partOf R)) s hs0.le hvolpos hvolb)
      rw [← hcast]
      refine le_trans hcstR ?_
      exact_mod_cast hQ
    -- the codegree hypothesis
    have hthreshold := PaperIV.RC01GlobalSchedule.dense_codegree_threshold_of_scale
      (d := s) (θ := θ) (gamma := gamma) R z (by exact_mod_cast hk1) hc3.le hc4.le
      (by exact hscale)
    obtain ⟨Pk, hPk⟩ := hgate n G R z hδ0.le hs0.le hs0 hs0.le hc3 hc4
      (by exact hchoice3) (by exact hchoice4)
      hthreshold hgammagam hsizeD hmassR
    refine ⟨Pk, ?_⟩
    -- the deterministic ledger
    set S : ℚ := ∑ H ∈ denseActiveProfiles R z s θ,
      patternGain H * psiT z (partOf R) H with hSdef
    have hround : (1 - s - s) * S - (Pk.gain : ℚ) ≤ zq * (n : ℚ) ^ 2 := by
      have h1 : ((((1 - s - s) * S - (Pk.gain : ℚ)) : ℚ) : ℝ)
          ≤ (((zq * (n : ℚ) ^ 2 : ℚ)) : ℝ) := by
        push_cast
        push_cast at hPk
        linarith
      exact_mod_cast h1
    have hfinal := PaperIV.RC01DenseAssembly.packing_loss_le_half_of_dense_profile_round
      R z Pk s θ s s zq light hε hδ0.le hs0.le hθ0 hk₀pos hkl
      huv0 hbud1 hbud2 hzqε hbud3 hbud4 hbud5 hlightterm hround
    have hfinalR : ((z.value - (Pk.gain : ℚ) : ℚ) : ℝ)
        ≤ (((ε / 2 * (n : ℚ) ^ 2 : ℚ)) : ℝ) := by
      exact_mod_cast hfinal
    push_cast at hfinalR ⊢
    linarith
  -- joining the two branches
  obtain ⟨P, hP⟩ := PaperIV.RC01TriangleSchedule.lowTriangle_branch_free_scheduled
    (ε := ((ε : ℚ) : ℝ)) (ζ := (((ε / 2 : ℚ) : ℝ))) x C hgateT
    (by push_cast; linarith)
    (by
      have : ((30 * (C : ℚ) : ℚ) : ℝ) ≤ ((ε * (n : ℚ) ^ 2 : ℚ) : ℝ) := by exact_mod_cast hCle
      push_cast at this ⊢
      linarith)
  refine ⟨P, ?_⟩
  have : ((x.value - (P.gain : ℚ) : ℚ) : ℝ) ≤ ((ε * (n : ℚ) ^ 2 : ℚ) : ℝ) := by
    push_cast
    linarith
  exact_mod_cast this

end PaperIV.RC01Final

