import E18.Gate
import PaperIV.RC01Final

/-!
# E18 — the RC01 rounding target with an explicit threshold `NE ε` (A2)

Adapted copy of `PaperIV.RC01Final.rc01_uniformRoundingTarget` in which every
constant is explicit: the gate constants come from
`PaperIV.RC01UniformDenseGate.exists_packing_mass_loss_le_denseActive_uniform_explicit`,
and the rational lower bound of the gate codegree constant (formerly produced by
`exists_rat_btwn`) is the explicit `1 / ⌈1/gam⌉`.
-/

namespace E18

open Finset
open MixedRounding
open PaperIV.RC01Final
open PaperIV.PatternTransfer
open PaperIV.PartitionBridge
open PaperIV.RegularityFormat
open PaperIV.RC01CleanedGate
open PaperIV.RC01CleanFiber
open PaperIV.RC01RootwiseReference
open PaperIV.RC01ResidualTransferClosure
open PaperIV.RC01DenseRootwiseRetention
open PaperIV.RC01MixedPatterns

/-- The scale `s = min (ε/4500) (1/10)` (`PaperIV.RC01Final.exists_scale`). -/
def sE (ε : ℚ) : ℚ := min (ε / 4500) (1 / 10)
/-- The regularity parameter `δ = s^21/2208` (`PaperIV.RC01Final.deltaOf`). -/
def δE (ε : ℚ) : ℚ := deltaOf (sE ε)
/-- The gate slack `zq = min (ε/10) 1`. -/
def zqE (ε : ℚ) : ℚ := min (ε / 10) 1
/-- The initial number of parts `k₀ = ⌈1500/ε⌉ + 1`. -/
def k0E (ε : ℚ) : ℕ := ⌈(1500 / ε : ℚ)⌉₊ + 1
/-- The regularity bound `B = SzemerediRegularity.bound (δ/8) k₀`. -/
noncomputable def BE (ε : ℚ) : ℕ := SzemerediRegularity.bound (((δE ε / 8 : ℚ) : ℝ)) (k0E ε)
/-- The explicit rational lower bound `1/⌈1/gam⌉` of the gate codegree constant. -/
noncomputable def gammaQE (ε : ℚ) : ℚ :=
  1 / (⌈1 / PaperIV.RC01UniformDenseGate.gamE ((zqE ε : ℚ) : ℝ)⌉₊ : ℚ)
/-- The integer ceiling of the gate triangle-mass constant. -/
noncomputable def cstE (ε : ℚ) : ℚ := (⌈PaperIV.RC01UniformDenseGate.CstE ((zqE ε : ℚ) : ℝ)⌉₊ : ℚ)
/-- The codegree scale bound `4 B^5 (a+b)/(γ a b)`, `a = s³ - 3δ`, `b = s⁶ - 6δ`. -/
noncomputable def scaleBoundE (ε : ℚ) : ℚ :=
  4 * (BE ε : ℚ) ^ 5 * ((sE ε ^ 3 - 3 * δE ε) + (sE ε ^ 6 - 6 * δE ε)) /
    (gammaQE ε * (sE ε ^ 3 - 3 * δE ε) * (sE ε ^ 6 - 6 * δE ε))
/-- The triangle-mass bound `50 (1 + 2 cst)/ε`. -/
noncomputable def massBoundE (ε : ℚ) : ℚ := 50 * (1 + 2 * cstE ε) / ε

/-- **The explicit RC01 threshold**
`NE ε = max(k₀, ⌈B/δ⌉, ⌈(12+10D)/zq⌉, ⌈4B⁵(a+b)/(γab)⌉, ⌈50(1+2C)/ε⌉) + 1`
with `γ = gammaQE ε`, `C = cstE ε`, `D = DE zq`. -/
noncomputable def NE (ε : ℚ) : ℕ :=
  max (max (k0E ε) ⌈(BE ε : ℚ) / δE ε⌉₊)
    (max ⌈(12 + 10 * PaperIV.RC01UniformDenseGate.DE ((zqE ε : ℚ) : ℝ)) / ((zqE ε : ℚ) : ℝ)⌉₊
      (max ⌈scaleBoundE ε⌉₊ ⌈massBoundE ε⌉₊)) + 1

set_option maxHeartbeats 1600000 in
/-- **A2: RC01 with the explicit threshold `NE ε`.** -/
theorem rc01_uniformRoundingTarget_explicit (ε : ℚ) (hε : 0 < ε) :
    ∀ n : ℕ, NE ε ≤ n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (x : FracPacking G), ∃ P : Packing G,
        x.value - (P.gain : ℚ) ≤ ε * (n : ℚ) ^ 2 := by
  classical
  set s : ℚ := sE ε with hsdef
  obtain ⟨hs0, hs1, hsbudget⟩ : 0 < s ∧ s ≤ 1 / 10 ∧ 15 * s ≤ ε / 300 := by
    refine ⟨lt_min (by linarith) (by norm_num), min_le_right _ _, ?_⟩
    have h : s ≤ ε / 4500 := min_le_left _ _
    linarith
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
  obtain ⟨hgam, hCst, hD, hgate⟩ :=
    PaperIV.RC01UniformDenseGate.exists_packing_mass_loss_le_denseActive_uniform_explicit
      ((zq : ℚ) : ℝ) hzqR0 hzqR1
  set gam : ℝ := PaperIV.RC01UniformDenseGate.gamE ((zq : ℚ) : ℝ) with hgamdef
  set Cst : ℝ := PaperIV.RC01UniformDenseGate.CstE ((zq : ℚ) : ℝ) with hCstdef
  set D : ℝ := PaperIV.RC01UniformDenseGate.DE ((zq : ℚ) : ℝ) with hDdef
  set gamma : ℚ := 1 / (⌈1 / gam⌉₊ : ℚ) with hgammadef
  have hceilpos : 0 < ⌈1 / gam⌉₊ := Nat.ceil_pos.2 (by positivity)
  have hgamma0 : 0 < gamma := by
    rw [hgammadef]
    have : (0 : ℚ) < (⌈1 / gam⌉₊ : ℚ) := by exact_mod_cast hceilpos
    positivity
  have hgammagam : (gamma : ℝ) ≤ gam := by
    have h1 : 1 / gam ≤ (⌈1 / gam⌉₊ : ℝ) := Nat.le_ceil _
    have hc : (0 : ℝ) < (⌈1 / gam⌉₊ : ℝ) := by exact_mod_cast hceilpos
    rw [hgammadef]
    push_cast
    rw [div_le_iff₀ hc]
    rw [div_le_iff₀ hgam] at h1
    linarith
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
  have hNE : NE ε = N := by subst hBdef; rfl
  intro n hn' G _ x
  have hn : N ≤ n := by rw [← hNE]; exact hn'
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
    linarith [mul_le_mul_of_nonneg_left hBk hsizeQ.le, mul_le_mul_of_nonneg_right hδhalf hnQ.le]
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
    linarith [mul_le_mul_of_nonneg_right hk4 hab0, mul_le_mul_of_nonneg_left hsizelow habpos.le]
  -- the light-profile account
  have hlightterm : 5 * (((mixedPatterns R).card : ℚ)) * θ ≤ light * (n : ℚ) ^ 2 := by
    refine PaperIV.RC01GlobalSchedule.five_mul_mixedPatterns_theta_le R
      (by exact_mod_cast hk1) hθ0 ?_
    rw [← hkdef, hθdef]
    have hB4 : (0 : ℚ) < 10 * (B : ℚ) ^ 4 := by positivity
    have hk4 : (k : ℚ) ^ 4 ≤ (B : ℚ) ^ 4 := pow_le_pow_left₀ (by positivity) hBk 4
    have hln : (0 : ℚ) ≤ light * (n : ℚ) ^ 2 := by positivity
    rw [← mul_div_assoc, div_le_iff₀ hB4]
    linarith [mul_le_mul_of_nonneg_right hk4 hln]
  -- the additive nibble constant
  have hsizeD : 12 + 10 * D ≤ ((zq : ℚ) : ℝ) * (n : ℝ) ^ 2 := by
    have h1 : (12 + 10 * D) / ((zq : ℚ) : ℝ) ≤ (n : ℝ) := by
      refine le_trans (Nat.le_ceil ((12 + 10 * D) / ((zq : ℚ) : ℝ))) ?_
      exact_mod_cast hnD
    rw [div_le_iff₀ hzqR0] at h1
    linarith [mul_le_mul_of_nonneg_left (le_self_pow₀ (by exact_mod_cast hn1 : (1 : ℝ) ≤ n) two_ne_zero) hzqR0.le]
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
      have hδterm : 15 * δ ≤ ε / 300 := by linarith
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
    linarith
  have hn1Q : (1 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn1
  have hn2 : (n : ℚ) ≤ (n : ℚ) ^ 2 := le_self_pow₀ hn1Q two_ne_zero
  have hbound : 50 * (1 + 2 * cst) ≤ ε * (n : ℚ) ^ 2 := by
    have hmassn : massBound ≤ (n : ℚ) := by
      refine le_trans (Nat.le_ceil massBound) ?_
      exact_mod_cast hnM
    rw [hmassdef, div_le_iff₀ hε] at hmassn
    linarith [mul_le_mul_of_nonneg_left hn2 hε.le]
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

/-- A2, packaged as `MixedRounding.UniformRoundingTarget ε` with witness `NE ε`. -/
theorem rc01_uniformRoundingTarget_of_explicit (ε : ℚ) (hε : 0 < ε) :
    MixedRounding.UniformRoundingTarget ε :=
  ⟨NE ε, rc01_uniformRoundingTarget_explicit ε hε⟩

end E18
