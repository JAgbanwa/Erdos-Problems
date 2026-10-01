import E18.NibbleOracle
import Nibble.WeightedSpreadNibble
import Nibble.FracNibbleLE

/-!
# E18 — the weighted nibble chain with explicit constants

Adapted copies of

* `Nibble.fracNibble_spread_weightedCodegree`, `Nibble.fracNibble_weightedCodegree`,
* `Nibble.SlackR.fracNibbleR_withSlack`,
* `Nibble.fracNibble_leUniform`,

with every existential witness replaced by an explicit definition.  The final result is
`Nibble.fracNibble_leUniform_explicit` with `γ = Nibble.γE r β`, `C = Nibble.CE r β`.
-/

open Finset Hypergraph

namespace E18.Nib

/-! ## 1. The spread / weighted nibble -/

/-- `k = 1 + r²`, the Beck–Fiala discrepancy constant. -/
def kS (r : ℕ) : ℕ := 1 + r * r
/-- The scaling degree `D = max ⌈d₀⌉ ⌈4k/μ⌉ + 1`. -/
noncomputable def DS (r : ℕ) (β : ℝ) : ℕ :=
  max ⌈d0N r β⌉₊ ⌈(4 * (kS r : ℝ)) / muN r β⌉₊ + 1
/-- The weighted-codegree threshold of the near-perfect weighted nibble. -/
noncomputable def gamW (r : ℕ) (β : ℝ) : ℝ := min (1 / (DS r β : ℝ)) (muN r β / 4)

/-- The conclusion of the near-perfect weighted nibble at fixed `γ, η`. -/
def WeightedAt (r : ℕ) (β γ η : ℝ) : Prop :=
  ∀ {W : Type} [Fintype W] [DecidableEq W] (H : Finset (Finset W)) (w : Finset W → ℝ)
    (Exc : Finset W),
    IsUniform H r →
    (∀ T, 0 ≤ w T) →
    (∀ v : W, ∑ T ∈ H.filter (fun T => v ∈ T), w T ≤ 1) →
    (∀ v : W, v ∉ Exc → 1 - γ ≤ ∑ T ∈ H.filter (fun T => v ∈ T), w T) →
    (Exc.card : ℝ) ≤ η * (Fintype.card W : ℝ) →
    (∀ x z : W, x ≠ z → ∑ T ∈ H.filter (fun T => x ∈ T ∧ z ∈ T), w T ≤ γ) →
    ∃ M : Finset (Finset W), IsMatching H M ∧
      (1 - β) * ((Fintype.card W : ℝ) / r) ≤ (M.card : ℝ) ∧
      (1 - β) * (∑ T ∈ H, w T) ≤ (M.card : ℝ)

/-- Adapted copy of `Nibble.fracNibble_spread_weightedCodegree` with explicit witnesses. -/
theorem spread_explicit (r : ℕ) (hr : 2 ≤ r) (β : ℝ) (hβ : 0 < β) :
    ∀ {W : Type} [Fintype W] [DecidableEq W] (H : Finset (Finset W)) (w : Finset W → ℝ)
      (Exc : Finset W),
      IsUniform H r →
      (∀ T, 0 ≤ w T) →
      (∀ T ∈ H, w T ≤ 1 / (DS r β : ℝ)) →
      (∀ v : W, ∑ T ∈ H.filter (fun T => v ∈ T), w T ≤ 1) →
      (∀ v : W, v ∉ Exc → 1 - muN r β / 4 ≤ ∑ T ∈ H.filter (fun T => v ∈ T), w T) →
      (Exc.card : ℝ) ≤ etaN r β * (Fintype.card W : ℝ) →
      (∀ x z : W, x ≠ z → ∑ T ∈ H.filter (fun T => x ∈ T ∧ z ∈ T), w T ≤ muN r β / 4) →
      ∃ M : Finset (Finset W), IsMatching H M ∧
        (1 - β) * ((Fintype.card W : ℝ) / r) ≤ (M.card : ℝ) ∧
        (1 - β) * (∑ T ∈ H, w T) ≤ (M.card : ℝ) := by
  classical
  obtain ⟨hμ, hη, hd₀, hmain⟩ := mostCeil_explicit r hr β hβ
  set μ := muN r β with hμdef
  set η := etaN r β with hηdef
  set d₀ := d0N r β with hd₀def
  set k : ℕ := kS r with hkdef
  have hkpos : (0 : ℝ) < (k : ℝ) := by
    have : 0 < k := by rw [hkdef, kS]; omega
    exact_mod_cast this
  set D : ℕ := DS r β with hDdef
  have hDeq : D = max ⌈d₀⌉₊ ⌈(4 * (k : ℝ)) / μ⌉₊ + 1 := rfl
  have hDpos : 0 < D := by rw [hDeq]; exact Nat.succ_pos _
  have hDR : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hDpos
  have hd₀D : d₀ ≤ (D : ℝ) := by
    have h1 : (⌈d₀⌉₊ : ℝ) ≤ (D : ℝ) := by
      exact_mod_cast (by rw [hDeq]; omega : ⌈d₀⌉₊ ≤ D)
    exact le_trans (Nat.le_ceil _) h1
  have hkD : 4 * (k : ℝ) ≤ μ * (D : ℝ) := by
    have h1 : ((4 * (k : ℝ)) / μ) ≤ (⌈(4 * (k : ℝ)) / μ⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈(4 * (k : ℝ)) / μ⌉₊ : ℝ) ≤ (D : ℝ) := by
      exact_mod_cast (by rw [hDeq]; omega : ⌈(4 * (k : ℝ)) / μ⌉₊ ≤ D)
    have h3 : ((4 * (k : ℝ)) / μ) ≤ (D : ℝ) := le_trans h1 h2
    rw [div_le_iff₀ hμ] at h3
    linarith
  intro W _ _ H w Exc hunif hwnn hspread hvle hvge hExc hcod
  set y : Finset W → ℝ := fun T => (D : ℝ) * w T with hydef
  have hy0 : ∀ T ∈ H, 0 ≤ y T := fun T _ => mul_nonneg hDR.le (hwnn T)
  have hy1 : ∀ T ∈ H, y T ≤ 1 := by
    intro T hT
    have h := hspread T hT
    rw [hydef]
    calc (D : ℝ) * w T ≤ (D : ℝ) * (1 / (D : ℝ)) := mul_le_mul_of_nonneg_left h hDR.le
      _ = 1 := by field_simp
  obtain ⟨S, hSH, hdeg, hcodeg⟩ :=
    Nibble.BeckFiala.exists_rounding_pairs r H (fun T hT => hunif T hT) y hy0 hy1
  have hkr : (1 : ℝ) + (r : ℝ) * r = (k : ℝ) := by rw [hkdef, kS]; push_cast; ring
  have hfrac : ∀ v : W, ∑ T ∈ H.filter (fun T => v ∈ T), y T
      = (D : ℝ) * ∑ T ∈ H.filter (fun T => v ∈ T), w T := by
    intro v; rw [hydef, ← Finset.mul_sum]
  have hfrac2 : ∀ x z : W, ∑ T ∈ H.filter (fun T => x ∈ T ∧ z ∈ T), y T
      = (D : ℝ) * ∑ T ∈ H.filter (fun T => x ∈ T ∧ z ∈ T), w T := by
    intro x z; rw [hydef, ← Finset.mul_sum]
  have hSunif : IsUniform S r := fun T hT => hunif T (hSH hT)
  have hdegeq : ∀ v : W, ((S.filter (fun T => v ∈ T)).card : ℝ) = (degree S v : ℝ) := by
    intro v; simp [degree]
  have hcodeq : ∀ x z : W, ((S.filter (fun T => x ∈ T ∧ z ∈ T)).card : ℝ)
      = (codegree S x z : ℝ) := by
    intro x z; simp [codegree]
  have hceil : ∀ v : W, (degree S v : ℝ) ≤ (1 + μ) * (D : ℝ) := by
    intro v
    have h := (abs_le.mp (hdeg v)).2
    rw [hfrac v, hdegeq v, hkr] at h
    have h2 : (D : ℝ) * ∑ T ∈ H.filter (fun T => v ∈ T), w T ≤ (D : ℝ) * 1 :=
      mul_le_mul_of_nonneg_left (hvle v) hDR.le
    linarith
  have hlow : ∀ v : W, v ∉ Exc → (1 - μ) * (D : ℝ) ≤ (degree S v : ℝ) := by
    intro v hv
    have h := (abs_le.mp (hdeg v)).1
    rw [hfrac v, hdegeq v, hkr] at h
    have h2 : (D : ℝ) * (1 - μ / 4) ≤ (D : ℝ) * ∑ T ∈ H.filter (fun T => v ∈ T), w T :=
      mul_le_mul_of_nonneg_left (hvge v hv) hDR.le
    linarith
  have hScod : CodegreeBounded S (μ * (D : ℝ)) := by
    intro x z hxz
    have h := (abs_le.mp (hcodeg x z)).2
    rw [hfrac2 x z, hcodeq x z, hkr] at h
    have h2 : (D : ℝ) * ∑ T ∈ H.filter (fun T => x ∈ T ∧ z ∈ T), w T ≤ (D : ℝ) * (μ / 4) :=
      mul_le_mul_of_nonneg_left (hcod x z hxz) hDR.le
    linarith
  have hreg : NearlyRegularMost S (D : ℝ) μ η :=
    ⟨Exc, hExc, fun v hv => ⟨hlow v hv, hceil v⟩⟩
  obtain ⟨M, hM, hMcard⟩ := hmain S (D : ℝ) hDR hd₀D hSunif hreg hScod hceil
  refine ⟨M, ⟨Finset.Subset.trans hM.subset hSH, hM.disjoint⟩, hMcard, ?_⟩
  have hrpos : (0 : ℝ) < r := by
    have : 0 < r := lt_of_lt_of_le (by norm_num) hr
    exact_mod_cast this
  have hsum : (∑ T ∈ H, w T) ≤ (Fintype.card W : ℝ) / r := by
    rw [le_div_iff₀ hrpos, mul_comm]
    exact Nibble.fracMatching_sum_le hunif hvle
  rcases le_or_gt β 1 with h1 | h1
  · exact le_trans (mul_le_mul_of_nonneg_left hsum (by linarith)) hMcard
  · have hnn' : 0 ≤ ∑ T ∈ H, w T := Finset.sum_nonneg (fun T _ => hwnn T)
    have hle0 : (1 - β) * (∑ T ∈ H, w T) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) hnn'
    exact le_trans hle0 (Nat.cast_nonneg _)

/-- Adapted copy of `Nibble.fracNibble_weightedCodegree` with explicit witnesses
`γ = gamW r β`, `η = etaN r β`. -/
theorem weighted_explicit (r : ℕ) (hr : 2 ≤ r) (β : ℝ) (hβ : 0 < β) :
    0 < gamW r β ∧ 0 < etaN r β ∧ WeightedAt r β (gamW r β) (etaN r β) := by
  classical
  obtain ⟨hμ, hη, -, -⟩ := mostCeil_explicit r hr β hβ
  have hDpos : (0 : ℝ) < (DS r β : ℝ) := by
    have : 0 < DS r β := by rw [DS]; exact Nat.succ_pos _
    exact_mod_cast this
  have hδ : 0 < 1 / (DS r β : ℝ) := by positivity
  have hγ : 0 < muN r β / 4 := by positivity
  refine ⟨lt_min hδ hγ, hη, ?_⟩
  intro W _ _ H w Exc hunif hwnn hvle hvge hExc hcod
  have hcod' : ∀ x z : W, x ≠ z → ∑ T ∈ H.filter (fun T => x ∈ T ∧ z ∈ T), w T ≤ muN r β / 4 :=
    fun x z hxz => le_trans (hcod x z hxz) (min_le_right _ _)
  have hcodδ : ∀ x z : W, x ≠ z →
      ∑ T ∈ H.filter (fun T => x ∈ T ∧ z ∈ T), w T ≤ 1 / (DS r β : ℝ) :=
    fun x z hxz => le_trans (hcod x z hxz) (min_le_left _ _)
  refine spread_explicit r hr β hβ H w Exc hunif hwnn
    (fun T hT => Nibble.weight_le_weightedCodegree hr hunif hwnn hcodδ hT) hvle
    (fun v hv => le_trans (by have := min_le_right (1 / (DS r β : ℝ)) (muN r β / 4); unfold gamW at *; linarith) (hvge v hv))
    hExc hcod'

/-! ## 2. The weighted nibble with slack, uniformity `k + 1` -/

/-- The slack threshold of `fracNibbleR_withSlack`. -/
noncomputable def gamR (k : ℕ) (β : ℝ) : ℝ := min (gamW (k + 1) β) 1

section SlackRSection

open Nibble.SlackR

/-- Adapted copy of `Nibble.SlackR.fracNibbleR_withSlack` with `γ = gamR k β`. -/
theorem fracNibbleR_withSlack_explicit (k : ℕ) (hk : 0 < k) (β : ℝ) (hβ : 0 < β) :
    0 < gamR k β ∧
      ∀ {X : Type} [Fintype X] [DecidableEq X] (K : Finset (Finset X)) (w : Finset X → ℝ),
        IsUniform K (k + 1) →
        (∀ T, 0 ≤ w T) →
        (∀ v : X, Nibble.Slack.wLoad K w v ≤ 1) →
        (∀ x z : X, x ≠ z → ∑ T ∈ K.filter (fun T => x ∈ T ∧ z ∈ T), w T ≤ gamR k β) →
        1 / gamR k β ≤ Nibble.Slack.slackTotal K w →
        ∃ M : Finset (Finset X), IsMatching K M ∧
          (1 - β) * (∑ T ∈ K, w T) - β * Nibble.Slack.slackTotal K w - 1 ≤ (M.card : ℝ) := by
  classical
  obtain ⟨hγ₀, hη, hmain⟩ := weighted_explicit (k + 1) (by omega) β hβ
  set γ₀ := gamW (k + 1) β with hγ₀def
  set η := etaN (k + 1) β with hηdef
  have hγpos : 0 < min γ₀ 1 := lt_min hγ₀ one_pos
  refine ⟨hγpos, ?_⟩
  intro X _ _ K w hK hw hload hcod hslack
  have hγle : min γ₀ 1 ≤ γ₀ := min_le_left _ _
  have hγ1 : min γ₀ 1 ≤ 1 := min_le_right _ _
  set γ := min γ₀ 1 with hγdef
  set S := Nibble.Slack.slackTotal K w with hSdef
  have hS : 1 / γ ≤ S := hslack
  have hγS : 1 ≤ S * γ := (div_le_iff₀ hγpos).mp hS
  have hS1 : 1 ≤ S := by nlinarith
  set m := ⌈S⌉₊ with hmdef
  have hmS : S ≤ (m : ℝ) := Nat.le_ceil S
  have hmpos : (0 : ℝ) < (m : ℝ) := lt_of_lt_of_le (by linarith) hmS
  have hm : 0 < m := by exact_mod_cast hmpos
  have hmlt : (m : ℝ) < S + 1 := Nat.ceil_lt_add_one (by linarith)
  have hinvm : 1 / (m : ℝ) ≤ γ := by
    rw [div_le_iff₀ hmpos]; nlinarith
  have hunif := padFamR_uniform K k m hK
  have hnn := padWtR_nonneg K w k m hw hload
  have hle : ∀ v : PadR X k m,
      ∑ U ∈ (padFamR K k m).filter (fun U => v ∈ U), padWtR K w k m U ≤ 1 := by
    intro v
    cases v with
    | inl a => rw [padLoad_inl K w k m hk hm a]
    | inr d =>
        obtain ⟨j, e⟩ := d
        rw [padLoad_inr K w k m hk hm j e, div_le_one hmpos]
        exact hmS
  have hge : ∀ v : PadR X k m, v ∉ (∅ : Finset (PadR X k m)) →
      1 - γ₀ ≤ ∑ U ∈ (padFamR K k m).filter (fun U => v ∈ U), padWtR K w k m U := by
    rintro v -
    cases v with
    | inl a => rw [padLoad_inl K w k m hk hm a]; linarith
    | inr d =>
        obtain ⟨j, e⟩ := d
        rw [padLoad_inr K w k m hk hm j e, le_div_iff₀ hmpos]
        nlinarith
  have hexc : ((∅ : Finset (PadR X k m)).card : ℝ)
      ≤ η * (Fintype.card (PadR X k m) : ℝ) := by
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  have hcodeg : ∀ x z : PadR X k m, x ≠ z →
      ∑ U ∈ (padFamR K k m).filter (fun U => x ∈ U ∧ z ∈ U), padWtR K w k m U ≤ γ₀ := by
    intro x z hxz
    have hmixbound : ∀ a : X, (1 - Nibble.Slack.wLoad K w a) / (m : ℝ) ≤ γ₀ := by
      intro a
      have h0 : 0 ≤ Nibble.Slack.wLoad K w a := Finset.sum_nonneg fun T _ => hw T
      have : (1 - Nibble.Slack.wLoad K w a) / (m : ℝ) ≤ 1 / (m : ℝ) := by
        gcongr
        linarith
      linarith [hinvm]
    cases x with
    | inl a =>
        cases z with
        | inl b =>
            have hab : a ≠ b := fun h => hxz (by rw [h])
            rw [padCodeg_inl_inl K w k m hk hab]
            exact le_trans (hcod a b hab) hγle
        | inr d =>
            obtain ⟨j, e⟩ := d
            rw [padCodeg_inl_inr K w k m hk hm a j e]
            exact hmixbound a
    | inr d =>
        obtain ⟨j, e⟩ := d
        cases z with
        | inl b =>
            rw [padCodegR_comm K w k m _ _, padCodeg_inl_inr K w k m hk hm b j e]
            exact hmixbound b
        | inr d' =>
            have hdd : (j, e) ≠ d' := fun h => hxz (by rw [h])
            refine le_trans (padCodeg_inr_inr K w k m hk hm hload hdd) ?_
            have hSnn : 0 ≤ S := by linarith
            have : S / (m : ℝ) ^ 2 ≤ 1 / (m : ℝ) := by
              rw [div_le_div_iff₀ (by positivity) hmpos]
              nlinarith
            rw [← hSdef]
            linarith [hinvm]
  obtain ⟨M, hM, -, hMcard⟩ :=
    hmain (padFamR K k m) (padWtR K w k m) ∅ hunif hnn hle hge hexc hcodeg
  rw [sum_padWtR K w k m hk hm, ← hSdef] at hMcard
  have hsplit : ((M.filter (fun U => U.toRight = ∅)).card : ℝ)
      + ((M.filter (fun U => ¬ (U.toRight = ∅))).card : ℝ) = (M.card : ℝ) := by
    rw [← Nat.cast_add, Finset.card_filter_add_card_filter_not]
  have hmix := card_mixedPartR_le K k m hk hm hM
  obtain ⟨M', hM', hM'card⟩ := exists_matching_of_padMatchingR K k m hk hM
  refine ⟨M', hM', ?_⟩
  rw [hM'card]
  nlinarith only [hMcard, hmix, hsplit, hmlt, hβ.le]

end SlackRSection

end E18.Nib

/-! ## 3. The bounded-rank weighted nibble with explicit constants -/

namespace Nibble

/-- Inner accuracy `b = β / (1 + r)`. -/
noncomputable def bLE (r : ℕ) (β : ℝ) : ℝ := β / (1 + (r : ℝ))

/-- **Explicit codegree threshold** `γE r β` of the bounded-rank weighted nibble. -/
noncomputable def γE (r : ℕ) (β : ℝ) : ℝ := min (E18.Nib.gamR (r - 1) (bLE r β)) 1

/-- **Explicit additive constant** `CE r β` of the bounded-rank weighted nibble. -/
noncomputable def CE (r : ℕ) (β : ℝ) : ℝ :=
  bLE r β * (r : ℝ) * (1 / E18.Nib.gamR (r - 1) (bLE r β) + 3) + 1

theorem γE_pos (r : ℕ) (hr : 2 ≤ r) (β : ℝ) (hβ : 0 < β) : 0 < γE r β := by
  have hb : 0 < bLE r β := by unfold bLE; positivity
  exact lt_min (E18.Nib.fracNibbleR_withSlack_explicit (r - 1) (by omega) _ hb).1 one_pos

theorem CE_pos (r : ℕ) (hr : 2 ≤ r) (β : ℝ) (hβ : 0 < β) : 0 < CE r β := by
  have hb : 0 < bLE r β := by unfold bLE; positivity
  have := (E18.Nib.fracNibbleR_withSlack_explicit (r - 1) (by omega) _ hb).1
  unfold CE; positivity

/-- **`Nibble.fracNibble_leUniform` with explicit constants** `γ = γE r β`, `C = CE r β`.
Adapted copy of the original proof. -/
theorem fracNibble_leUniform_explicit (r : ℕ) (hr : 2 ≤ r) (β : ℝ) (hβ : 0 < β) :
    ∀ {X : Type} [Fintype X] [DecidableEq X] (K : Finset (Finset X)) (w : Finset X → ℝ),
      (∀ T ∈ K, T.Nonempty ∧ #T ≤ r) →
      (∀ T, 0 ≤ w T) →
      (∀ v : X, Slack.wLoad K w v ≤ 1) →
      (∀ x z : X, x ≠ z → ∑ T ∈ K.filter (fun T => x ∈ T ∧ z ∈ T), w T ≤ γE r β) →
      ∃ M : Finset (Finset X), IsMatching K M ∧
        (1 - β) * (∑ T ∈ K, w T) - β * (Fintype.card X : ℝ) - CE r β ≤ (M.card : ℝ) := by
  classical
  have hrpos : (0 : ℝ) < 1 + (r : ℝ) := by positivity
  set b : ℝ := bLE r β with hbdef
  have hb : 0 < b := by rw [hbdef, bLE]; positivity
  have hbβ : b ≤ β := by
    rw [hbdef, bLE, div_le_iff₀ hrpos]
    nlinarith
  obtain ⟨hγ₂, hmain⟩ := E18.Nib.fracNibbleR_withSlack_explicit (r - 1) (by omega) b hb
  set γ₂ := E18.Nib.gamR (r - 1) b with hγ₂def
  have hγEdef : γE r β = min γ₂ 1 := rfl
  have hCEdef : CE r β = b * (r : ℝ) * (1 / γ₂ + 3) + 1 := rfl
  rw [hγEdef, hCEdef]
  intro X _ _ K w hsize hw hload hcod
  set W : ℝ := ∑ T ∈ K, w T with hWdef
  have hW0 : 0 ≤ W := Finset.sum_nonneg fun T _ => hw T
  set m : ℕ := ⌈W⌉₊ + ⌈1 / γ₂⌉₊ + 1 with hmdef
  have hm : 0 < m := by omega
  have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hmW : W + 1 / γ₂ ≤ (m : ℝ) := by
    have h1 : W ≤ (⌈W⌉₊ : ℝ) := Nat.le_ceil W
    have h2 : 1 / γ₂ ≤ (⌈1 / γ₂⌉₊ : ℝ) := Nat.le_ceil _
    rw [hmdef]
    push_cast
    linarith
  have hmub : (m : ℝ) ≤ W + 1 / γ₂ + 3 := by
    have h1 : (⌈W⌉₊ : ℝ) < W + 1 := Nat.ceil_lt_add_one hW0
    have h2 : (⌈1 / γ₂⌉₊ : ℝ) < 1 / γ₂ + 1 := Nat.ceil_lt_add_one (by positivity)
    rw [hmdef]
    push_cast
    linarith
  have hWm : W ≤ (m : ℝ) := by
    have : (0 : ℝ) < 1 / γ₂ := by positivity
    linarith
  have hinvm : 1 / (m : ℝ) ≤ γ₂ := by
    rw [div_le_iff₀ hm']
    have : 1 / γ₂ ≤ (m : ℝ) := by linarith
    rw [div_le_iff₀ hγ₂] at this
    linarith
  set K' := LEUnif.padFamLE r m K with hK'
  set w' := LEUnif.padWtLE r m w with hw'
  have hunif : IsUniform K' (r - 1 + 1) := by
    have hrr : r - 1 + 1 = r := by omega
    rw [hrr]
    exact LEUnif.padFamLE_uniform (fun T hT => (hsize T hT).2)
  have hnn : ∀ U, 0 ≤ w' U := fun U => LEUnif.padWtLE_nonneg w hw U
  have hfilW : ∀ p : Finset X → Prop, ∀ _ : DecidablePred p,
      ∑ T ∈ K.filter p, w T ≤ W := by
    intro p _
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun T _ _ => hw T)
  have hloadPad : ∀ v : LEUnif.PadV X r m, Slack.wLoad K' w' v ≤ 1 := by
    intro v
    cases v with
    | inl a => rw [hK', hw', LEUnif.padLoad_inl hm K w a]; exact hload a
    | inr d =>
        obtain ⟨j, e⟩ := d
        rw [hK', hw', LEUnif.padLoad_inr hm K w j e, div_le_one hm']
        exact le_trans (hfilW _ _) hWm
  have hloadX : ∀ v : X, 0 ≤ Slack.wLoad K w v :=
    fun v => Finset.sum_nonneg fun T _ => hw T
  have hcodPad : ∀ x z : LEUnif.PadV X r m, x ≠ z →
      ∑ U ∈ K'.filter (fun U => x ∈ U ∧ z ∈ U), w' U ≤ γ₂ := by
    intro x z hxz
    have hmix : ∀ a : X, Slack.wLoad K w a / (m : ℝ) ≤ γ₂ := by
      intro a
      have h1 : Slack.wLoad K w a / (m : ℝ) ≤ 1 / (m : ℝ) := by
        gcongr
        exact hload a
      linarith [hinvm]
    cases x with
    | inl a =>
        cases z with
        | inl c =>
            have hac : a ≠ c := fun h => hxz (by rw [h])
            rw [hK', hw', LEUnif.padCodeg_inl_inl K w hm]
            exact le_trans (hcod a c hac) (le_trans (min_le_left _ _) (le_refl _))
        | inr d =>
            obtain ⟨j, e⟩ := d
            exact le_trans (LEUnif.padCodeg_inl_inr hm K w hw a j e) (hmix a)
    | inr d =>
        obtain ⟨j, e⟩ := d
        cases z with
        | inl c =>
            rw [hK', hw', LEUnif.padCodegLE_comm]
            exact le_trans (LEUnif.padCodeg_inl_inr hm K w hw c j e) (hmix c)
        | inr d' =>
            obtain ⟨j', e'⟩ := d'
            have hne : (j, e) ≠ (j', e') := fun h => hxz (by rw [h])
            refine le_trans (LEUnif.padCodeg_inr_inr hm K w hw hne) ?_
            have h1 : W / (m : ℝ) ^ 2 ≤ 1 / (m : ℝ) := by
              rw [div_le_div_iff₀ (by positivity) hm']
              nlinarith
            linarith [hinvm]
  have hslackEq : Slack.slackTotal K' w'
      = (∑ v : X, (1 - Slack.wLoad K' w' (Sum.inl v)))
        + ∑ d : Fin r × Fin m, (1 - Slack.wLoad K' w' (Sum.inr d)) := by
    rw [Slack.slackTotal]
    exact Fintype.sum_sum_type _
  have hdummy : ∀ d : Fin r × Fin m, Slack.wLoad K' w' (Sum.inr d) ≤ W / (m : ℝ) := by
    rintro ⟨j, e⟩
    rw [hK', hw', LEUnif.padLoad_inr hm K w j e]
    gcongr
    exact hfilW _ _
  have hslackLB : 1 / γ₂ ≤ Slack.slackTotal K' w' := by
    have hreal : 0 ≤ ∑ v : X, (1 - Slack.wLoad K' w' (Sum.inl v)) := by
      refine Finset.sum_nonneg fun v _ => ?_
      have := hloadPad (Sum.inl v)
      linarith
    have hdum : (Fintype.card (Fin r × Fin m) : ℝ) * (1 - W / (m : ℝ))
        ≤ ∑ d : Fin r × Fin m, (1 - Slack.wLoad K' w' (Sum.inr d)) := by
      have hconst : (Fintype.card (Fin r × Fin m) : ℝ) * (1 - W / (m : ℝ))
          = ∑ _d : Fin r × Fin m, (1 - W / (m : ℝ)) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [hconst]
      refine Finset.sum_le_sum fun d _ => ?_
      have := hdummy d
      linarith
    have hcardrm : (Fintype.card (Fin r × Fin m) : ℝ) = (r : ℝ) * (m : ℝ) := by
      simp
    have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast (by omega : 1 ≤ r)
    have hmWpos : 1 / γ₂ ≤ (m : ℝ) - W := by linarith
    have hkey : (r : ℝ) * (m : ℝ) * (1 - W / (m : ℝ)) = (r : ℝ) * ((m : ℝ) - W) := by
      field_simp
    rw [hslackEq]
    rw [hcardrm, hkey] at hdum
    nlinarith [hmWpos]
  obtain ⟨M, hM, hMcard⟩ :=
    hmain K' w' hunif hnn hloadPad hcodPad hslackLB
  have hsumw' : ∑ U ∈ K', w' U = W := LEUnif.sum_padWtLE hm K w
  have hslackUB : Slack.slackTotal K' w'
      ≤ (Fintype.card X : ℝ) + (r : ℝ) * (m : ℝ) := by
    have hbound : ∀ v : LEUnif.PadV X r m, 1 - Slack.wLoad K' w' v ≤ 1 := by
      intro v
      have : 0 ≤ Slack.wLoad K' w' v := Finset.sum_nonneg fun U _ => hnn U
      linarith
    have := Finset.sum_le_sum (fun v (_ : v ∈ (univ : Finset (LEUnif.PadV X r m))) => hbound v)
    rw [Slack.slackTotal]
    refine le_trans this ?_
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    have : (Fintype.card (LEUnif.PadV X r m) : ℝ)
        = (Fintype.card X : ℝ) + (r : ℝ) * (m : ℝ) := by simp
    rw [this]
  have hWX : W ≤ (Fintype.card X : ℝ) := by
    have h1 : W ≤ ∑ T ∈ K, (#T : ℝ) * w T := by
      refine Finset.sum_le_sum fun T hT => ?_
      have h2 : (1 : ℝ) ≤ (#T : ℝ) := by
        have := (hsize T hT).1
        have : 1 ≤ #T := Finset.card_pos.mpr this
        exact_mod_cast this
      nlinarith [hw T]
    have h3 : ∑ v : X, Slack.wLoad K w v ≤ (Fintype.card X : ℝ) := by
      have := Finset.sum_le_sum (fun v (_ : v ∈ (univ : Finset X)) => hload v)
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at this
      exact this
    rw [LEUnif.sum_wLoad_eq K w] at h3
    linarith
  obtain ⟨M', hM', hM'card⟩ :=
    LEUnif.exists_matching_of_padMatchingLE (fun T hT => (hsize T hT).1) hM
  refine ⟨M', hM', ?_⟩
  rw [hM'card]
  rw [hsumw'] at hMcard
  have hslackbound : b * Slack.slackTotal K' w'
      ≤ β * (Fintype.card X : ℝ) + b * (r : ℝ) * (1 / γ₂ + 3) := by
    have h1 : b * Slack.slackTotal K' w'
        ≤ b * ((Fintype.card X : ℝ) + (r : ℝ) * (m : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hslackUB hb.le
    have h2 : (r : ℝ) * (m : ℝ) ≤ (r : ℝ) * (W + 1 / γ₂ + 3) := by
      have hr0 : (0 : ℝ) ≤ (r : ℝ) := by positivity
      exact mul_le_mul_of_nonneg_left hmub hr0
    have hbr : b * (1 + (r : ℝ)) = β := by
      rw [hbdef, bLE]
      field_simp
    nlinarith [hb.le, hWX, hW0]
  have hbw : b * W ≤ β * W := mul_le_mul_of_nonneg_right hbβ hW0
  linarith only [hMcard, hslackbound, hbw]

end Nibble
