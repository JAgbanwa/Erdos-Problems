import E18.NibbleChain
import PaperIV.RC01UniformDenseGate

/-!
# E18 — the marked-quota gate and the dense physical gate with explicit constants

Adapted copies of `PaperIV.MarkedQuotaSlackGate.slackMarkedQuotaNibbleAt_proved`,
`PaperIV.MarkedQuotaTypedGain.typed_gain_slack`,
`PaperIV.MarkedQuotaPairing.paired_typed_gain_slack`,
`PaperIV.JointTwoQuotaPhysical.mixed_physical_packing_of_slackMarkedQuota`,
`PaperIV.RC01MarkedRounding.exists_packing_loss_le_of_slackMarkedQuota` and
`PaperIV.RC01UniformDenseGate.exists_packing_mass_loss_le_denseActive_uniform`,
each with its existential witnesses replaced by explicit definitions.  The new
declarations live in the namespaces of the originals, with the suffix `_explicit`.
-/

namespace PaperIV.MarkedQuotaSlackGate

open Finset
open PaperIV.MarkedQuotaTokens

/-- Inner slack accuracy `b = min (β/2) (ε/2)`. -/
noncomputable def bQ (β ε : ℝ) : ℝ := min (β / 2) (ε / 2)
/-- Explicit codegree threshold of the slack marked-quota gate. -/
noncomputable def gamQ (r : ℕ) (β ε : ℝ) : ℝ := Nibble.γE (r + 1) (bQ β ε)
/-- Token-pool floor `k₀ = ⌈1/γ₀⌉`. -/
noncomputable def kQ (r : ℕ) (β ε : ℝ) : ℕ := ⌈(1 : ℝ) / gamQ r β ε⌉₊
/-- Explicit additive constant of the slack marked-quota gate. -/
noncomputable def CQ (r : ℕ) (β ε : ℝ) : ℝ :=
  Nibble.CE (r + 1) (bQ β ε) + 1 + (kQ r β ε : ℝ) + bQ β ε * (2 + 2 * (kQ r β ε : ℝ))

set_option maxHeartbeats 4000000 in
/-- `slackMarkedQuotaNibbleAt_proved` with explicit `γ = gamQ r β ε`, `C = CQ r β ε`. -/
theorem slackMarkedQuotaNibbleAt_explicit (r : ℕ) (hr : 2 ≤ r) (β ε : ℝ)
    (hβ : 0 < β) (hε : 0 < ε) :
    0 < gamQ r β ε ∧ 0 < CQ r β ε ∧
      ∀ {W : Type} [Fintype W] [DecidableEq W]
        (H A : Finset (Finset W)) (w : Finset W → ℝ),
        A ⊆ H →
        NibblePort.Hypergraph.IsUniform H r →
        (∀ T, 0 ≤ w T) →
        (∀ v : W, ∑ T ∈ H.filter (fun T => v ∈ T), w T ≤ 1) →
        (∀ x z : W, x ≠ z →
          ∑ T ∈ H.filter (fun T => x ∈ T ∧ z ∈ T), w T ≤ gamQ r β ε) →
        ∃ M : Finset (Finset W), SlackMarkedQuotaConclusion H A M w β ε (CQ r β ε) := by
  classical
  unfold CQ kQ gamQ bQ
  have hrR : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  set b : ℝ := min (β / 2) (ε / 2) with hbdef
  have hb : 0 < b := lt_min (by positivity) (by positivity)
  have hbβ : b ≤ β / 2 := min_le_left _ _
  have hbε : b ≤ ε / 2 := min_le_right _ _
  have hγ₀ : 0 < Nibble.γE (r + 1) b := Nibble.γE_pos (r + 1) (by omega) b hb
  have hC₀ : 0 < Nibble.CE (r + 1) b := Nibble.CE_pos (r + 1) (by omega) b hb
  have hmain : ∀ {W : Type} [Fintype W] [DecidableEq W]
      (H : Finset (Finset W)) (w : Finset W → ℝ),
      (∀ T ∈ H, T.Nonempty ∧ T.card ≤ r + 1) →
      (∀ T, 0 ≤ w T) →
      (∀ v : W, ∑ T ∈ H.filter (fun T => v ∈ T), w T ≤ 1) →
      (∀ x z : W, x ≠ z →
        ∑ T ∈ H.filter (fun T => x ∈ T ∧ z ∈ T), w T ≤ Nibble.γE (r + 1) b) →
      ∃ M : Finset (Finset W),
        PaperIV.NibblePort.Hypergraph.IsMatching H M ∧
        (1 - b) * (∑ T ∈ H, w T) - b * (Fintype.card W : ℝ) - Nibble.CE (r + 1) b
          ≤ (M.card : ℝ) := by
    intro W _ _ H w hsize hnonneg hload hcodeg
    have hload' : ∀ v : W, Nibble.Slack.wLoad H w v ≤ 1 := by
      simpa [Nibble.Slack.wLoad] using hload
    obtain ⟨M, hM, hcard⟩ :=
      Nibble.fracNibble_leUniform_explicit (r + 1) (by omega) b hb H w hsize hnonneg hload' hcodeg
    exact ⟨M, ⟨hM.subset, hM.disjoint⟩, hcard⟩
  set γ₀ := Nibble.γE (r + 1) b with hγ₀def
  set C₀ := Nibble.CE (r + 1) b with hC₀def
  set k₀ : ℕ := ⌈(1 : ℝ) / γ₀⌉₊ with hk₀def
  have hk₀ge : (1 : ℝ) / γ₀ ≤ (k₀ : ℝ) := Nat.le_ceil _
  have hk₀pos : 0 < k₀ := by
    by_contra hcon
    push_neg at hcon
    interval_cases k₀
    · have : (0 : ℝ) < 1 / γ₀ := by positivity
      simp at hk₀ge
      linarith
  have hk₀R : (0 : ℝ) < (k₀ : ℝ) := by exact_mod_cast hk₀pos
  have hinvk : (1 : ℝ) / (k₀ : ℝ) ≤ γ₀ := by
    rw [div_le_iff₀ hk₀R]
    rw [div_le_iff₀ hγ₀] at hk₀ge
    linarith
  refine ⟨hγ₀, by positivity, ?_⟩
  intro W _ _ H A w hAH huni hw hload hcod
  set u : ℝ := ∑ T ∈ H \ A, w T with hudef
  set a : ℝ := ∑ T ∈ A, w T with hadef
  have hu0 : 0 ≤ u := Finset.sum_nonneg (fun T _ => hw T)
  have ha0 : 0 ≤ a := Finset.sum_nonneg (fun T _ => hw T)
  have hsum : ∑ T ∈ H, w T = u + a := (Finset.sum_sdiff hAH).symm
  have hn0 : (0 : ℝ) ≤ (Fintype.card W : ℝ) := by positivity
  have hεn : (0 : ℝ) ≤ ε * (Fintype.card W : ℝ) := by positivity
  have hmassW : (r : ℝ) * (u + a) ≤ (Fintype.card W : ℝ) := by
    rw [← hsum]; exact MarkedQuotaGate.mass_le_card huni hload
  have h2ua : 2 * (u + a) ≤ (Fintype.card W : ℝ) := by nlinarith
  -- the token pools
  set p : ℕ := max ⌈u⌉₊ k₀ with hpdef
  set q : ℕ := max ⌈a⌉₊ k₀ with hqdef
  have hp0 : 0 < p := lt_of_lt_of_le hk₀pos (le_max_right _ _)
  have hq0 : 0 < q := lt_of_lt_of_le hk₀pos (le_max_right _ _)
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp0
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq0
  have hup : u ≤ (p : ℝ) :=
    le_trans (Nat.le_ceil u) (by exact_mod_cast le_max_left ⌈u⌉₊ k₀)
  have haq : a ≤ (q : ℝ) :=
    le_trans (Nat.le_ceil a) (by exact_mod_cast le_max_left ⌈a⌉₊ k₀)
  have hpk : (k₀ : ℝ) ≤ (p : ℝ) := by exact_mod_cast le_max_right ⌈u⌉₊ k₀
  have hqk : (k₀ : ℝ) ≤ (q : ℝ) := by exact_mod_cast le_max_right ⌈a⌉₊ k₀
  have hinvp : (1 : ℝ) / (p : ℝ) ≤ γ₀ :=
    le_trans (by apply one_div_le_one_div_of_le hk₀R hpk) hinvk
  have hinvq : (1 : ℝ) / (q : ℝ) ≤ γ₀ :=
    le_trans (by apply one_div_le_one_div_of_le hk₀R hqk) hinvk
  have hple : (p : ℝ) ≤ u + 1 + (k₀ : ℝ) := by
    have h1 : p ≤ ⌈u⌉₊ + k₀ := max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)
    have h2 : (p : ℝ) ≤ (⌈u⌉₊ : ℝ) + (k₀ : ℝ) := by exact_mod_cast h1
    have h3 : (⌈u⌉₊ : ℝ) < u + 1 := Nat.ceil_lt_add_one hu0
    linarith
  have hqle : (q : ℝ) ≤ a + 1 + (k₀ : ℝ) := by
    have h1 : q ≤ ⌈a⌉₊ + k₀ := max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)
    have h2 : (q : ℝ) ≤ (⌈a⌉₊ : ℝ) + (k₀ : ℝ) := by exact_mod_cast h1
    have h3 : (⌈a⌉₊ : ℝ) < a + 1 := Nat.ceil_lt_add_one ha0
    linarith
  -- the extended instance
  have hsize' : ∀ S ∈ bigH H A p q, S.Nonempty ∧ S.card ≤ r + 1 := by
    intro S hS
    have hcard : S.card = r + 1 := card_of_mem_bigH huni hAH hS
    refine ⟨Finset.card_pos.1 ?_, le_of_eq hcard⟩
    rw [hcard]; omega
  have hnonneg' : ∀ S, 0 ≤ bigW w p q S := bigW_nonneg hw p q
  have hload' : ∀ v : Vtx W p q,
      ∑ S ∈ (bigH H A p q).filter (fun S => v ∈ S), bigW w p q S ≤ 1 := by
    rintro (v | (i | j))
    · rw [bigH_load_inl H A w p q hAH hp0.ne' hq0.ne' v]; exact hload v
    · rw [bigH_load_tokP H A w p q i, ← hudef]
      exact (div_le_one hpR).2 hup
    · rw [bigH_load_tokQ H A w p q j, ← hadef]
      exact (div_le_one hqR).2 haq
  have hswap : ∀ x z : Vtx W p q,
      ∑ S ∈ (bigH H A p q).filter (fun S => x ∈ S ∧ z ∈ S), bigW w p q S
        = ∑ S ∈ (bigH H A p q).filter (fun S => z ∈ S ∧ x ∈ S), bigW w p q S := by
    intro x z
    congr 1
    exact Finset.filter_congr (fun S _ => and_comm)
  have hcodP : ∀ (x : W) (i : Fin p),
      ∑ S ∈ (bigH H A p q).filter
        (fun S => (Sum.inl x : Vtx W p q) ∈ S ∧ (Sum.inr (Sum.inl i) : Vtx W p q) ∈ S),
        bigW w p q S ≤ γ₀ := by
    intro x i
    rw [bigH_codeg_inl_tokP H A w p q i x]
    have hnum : (∑ T ∈ (H \ A).filter (fun T => x ∈ T), w T) ≤ 1 := by
      refine le_trans ?_ (hload x)
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun T _ _ => hw T)
      intro T hT
      rw [Finset.mem_filter] at hT ⊢
      exact ⟨(Finset.mem_sdiff.1 hT.1).1, hT.2⟩
    refine le_trans ?_ hinvp
    rw [div_le_div_iff_of_pos_right hpR]
    exact hnum
  have hcodQ : ∀ (x : W) (j : Fin q),
      ∑ S ∈ (bigH H A p q).filter
        (fun S => (Sum.inl x : Vtx W p q) ∈ S ∧ (Sum.inr (Sum.inr j) : Vtx W p q) ∈ S),
        bigW w p q S ≤ γ₀ := by
    intro x j
    rw [bigH_codeg_inl_tokQ H A w p q j x]
    have hnum : (∑ T ∈ A.filter (fun T => x ∈ T), w T) ≤ 1 := by
      refine le_trans ?_ (hload x)
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun T _ _ => hw T)
      intro T hT
      rw [Finset.mem_filter] at hT ⊢
      exact ⟨hAH hT.1, hT.2⟩
    refine le_trans ?_ hinvq
    rw [div_le_div_iff_of_pos_right hqR]
    exact hnum
  have hcod' : ∀ x z : Vtx W p q, x ≠ z →
      ∑ S ∈ (bigH H A p q).filter (fun S => x ∈ S ∧ z ∈ S), bigW w p q S ≤ γ₀ := by
    rintro (x | (i | j)) (z | (i' | j')) hxz
    · rw [bigH_codeg_inl_inl H A w p q hAH hp0.ne' hq0.ne' x z]
      exact hcod x z (fun hc => hxz (by rw [hc]))
    · exact hcodP x i'
    · exact hcodQ x j'
    · rw [hswap]; exact hcodP z i
    · rw [bigH_codeg_tok_tok H A w p q (Sum.inl i) (Sum.inl i')
        (fun hc => hxz (by rw [hc]))]
      exact le_of_lt hγ₀
    · rw [bigH_codeg_tok_tok H A w p q (Sum.inl i) (Sum.inr j') (by simp)]
      exact le_of_lt hγ₀
    · rw [hswap]; exact hcodQ z j
    · rw [bigH_codeg_tok_tok H A w p q (Sum.inr j) (Sum.inl i') (by simp)]
      exact le_of_lt hγ₀
    · rw [bigH_codeg_tok_tok H A w p q (Sum.inr j) (Sum.inr j')
        (fun hc => hxz (by rw [hc]))]
      exact le_of_lt hγ₀
  obtain ⟨Mstar, hMstar, hMmass⟩ :=
    hmain (W := Vtx W p q) (bigH H A p q) (bigW w p q) hsize' hnonneg' hload' hcod'
  rw [bigH_mass H A w p q hp0.ne' hq0.ne', ← hudef, ← hadef] at hMmass
  have hcardV : (Fintype.card (Vtx W p q) : ℝ)
      = (Fintype.card W : ℝ) + ((p : ℝ) + (q : ℝ)) := by
    have hc : Fintype.card (Vtx W p q) = Fintype.card W + (p + q) := by simp [Vtx]
    rw [hc]; push_cast; ring
  rw [hcardV] at hMmass
  -- projecting back
  have hprojInj : ∀ S₁ ∈ Mstar, ∀ S₂ ∈ Mstar, proj S₁ = proj S₂ → S₁ = S₂ := by
    intro S₁ h₁ S₂ h₂ heq
    by_contra hne
    have hdisj := hMstar.disjoint S₁ h₁ S₂ h₂ hne
    have hcard1 : (proj S₁).card = r := by
      rcases mem_bigH.1 (hMstar.subset h₁) with ⟨T, hT, _, i, rfl⟩ | ⟨T, hT, j, rfl⟩
      · rw [proj_ext]; exact huni T hT
      · rw [proj_ext]; exact huni T (hAH hT)
    obtain ⟨v, hv⟩ : (proj S₁).Nonempty := by
      rw [← Finset.card_pos, hcard1]; omega
    have hv1 : (Sum.inl v : Vtx W p q) ∈ S₁ := mem_proj.1 hv
    have hv2 : (Sum.inl v : Vtx W p q) ∈ S₂ := mem_proj.1 (heq ▸ hv)
    exact (Finset.disjoint_left.1 hdisj hv1) hv2
  set M : Finset (Finset W) := Mstar.image proj with hMdef
  have hMcard : M.card = Mstar.card := Finset.card_image_of_injOn hprojInj
  have hMmatch : NibblePort.Hypergraph.IsMatching H M := by
    constructor
    · intro T hT
      obtain ⟨S, hS, rfl⟩ := Finset.mem_image.1 hT
      exact proj_mem_of_mem_bigH hAH (hMstar.subset hS)
    · intro T₁ h₁ T₂ h₂ hne
      obtain ⟨S₁, hS₁, rfl⟩ := Finset.mem_image.1 h₁
      obtain ⟨S₂, hS₂, rfl⟩ := Finset.mem_image.1 h₂
      have hSne : S₁ ≠ S₂ := fun hc => hne (by rw [hc])
      have hdisj := hMstar.disjoint S₁ hS₁ S₂ hS₂ hSne
      rw [Finset.disjoint_left]
      intro v hv1 hv2
      exact (Finset.disjoint_left.1 hdisj (mem_proj.1 hv1)) (mem_proj.1 hv2)
  -- at most `p` unmarked edges are selected
  have hbadcard : (M.filter (fun T => T ∉ A)).card ≤ p := by
    set Mbad : Finset (Finset (Vtx W p q)) := Mstar.filter (fun S => proj S ∉ A) with hMbad
    have hsub : M.filter (fun T => T ∉ A) ⊆ Mbad.image proj := by
      intro T hT
      rw [Finset.mem_filter] at hT
      obtain ⟨S, hS, rfl⟩ := Finset.mem_image.1 hT.1
      exact Finset.mem_image.2 ⟨S, Finset.mem_filter.2 ⟨hS, hT.2⟩, rfl⟩
    refine le_trans (le_trans (Finset.card_le_card hsub) Finset.card_image_le) ?_
    set Pt : Finset (Vtx W p q) → Finset (Fin p) :=
      fun S => (Finset.univ : Finset (Fin p)).filter
        (fun i => (Sum.inr (Sum.inl i) : Vtx W p q) ∈ S) with hPt
    have hne : ∀ S ∈ Mbad, 1 ≤ (Pt S).card := by
      intro S hS
      rw [Finset.mem_filter] at hS
      rcases mem_bigH.1 (hMstar.subset hS.1) with ⟨T, hT, hTA, i, rfl⟩ | ⟨T, hT, j, rfl⟩
      · refine Finset.card_pos.2 ⟨i, ?_⟩
        rw [hPt]
        exact Finset.mem_filter.2 ⟨Finset.mem_univ _, by simp⟩
      · exact absurd (by simpa using hT) hS.2
    have hdisjPt : ∀ S₁ ∈ Mbad, ∀ S₂ ∈ Mbad, S₁ ≠ S₂ → Disjoint (Pt S₁) (Pt S₂) := by
      intro S₁ h₁ S₂ h₂ hne12
      have hd := hMstar.disjoint S₁ (Finset.mem_filter.1 h₁).1 S₂
        (Finset.mem_filter.1 h₂).1 hne12
      rw [Finset.disjoint_left]
      intro i hi1 hi2
      rw [hPt, Finset.mem_filter] at hi1 hi2
      exact (Finset.disjoint_left.1 hd hi1.2) hi2.2
    have hbiUnion : (Mbad.biUnion Pt).card = ∑ S ∈ Mbad, (Pt S).card :=
      Finset.card_biUnion hdisjPt
    have hle1 : Mbad.card ≤ ∑ S ∈ Mbad, (Pt S).card := by
      calc Mbad.card = ∑ _S ∈ Mbad, 1 := by simp
        _ ≤ ∑ S ∈ Mbad, (Pt S).card := Finset.sum_le_sum hne
    have hle2 : (Mbad.biUnion Pt).card ≤ p := by
      refine le_trans (Finset.card_le_univ _) ?_
      simp
    omega
  -- the two quotas
  have hsplit : (M.filter (fun T => T ∈ A)).card + (M.filter (fun T => T ∉ A)).card
      = M.card := Finset.card_filter_add_card_filter_not _
  have hMcardR : (M.card : ℝ) = (Mstar.card : ℝ) := by exact_mod_cast hMcard
  have hmarkedR : (Mstar.card : ℝ) - (p : ℝ) ≤ ((M.filter (fun T => T ∈ A)).card : ℝ) := by
    have h1 : ((M.filter (fun T => T ∉ A)).card : ℝ) ≤ (p : ℝ) := by exact_mod_cast hbadcard
    have h2 : ((M.filter (fun T => T ∈ A)).card : ℝ)
        + ((M.filter (fun T => T ∉ A)).card : ℝ) = (M.card : ℝ) := by exact_mod_cast hsplit
    linarith [hMcardR]
  -- the arithmetic of the slack budget
  have hexp : (1 - b) * (u + a) = (u + a) - b * (u + a) := by ring
  have hdist : b * ((Fintype.card W : ℝ) + ((p : ℝ) + (q : ℝ)))
      = b * (Fintype.card W : ℝ) + b * ((p : ℝ) + (q : ℝ)) := by ring
  have hpq : (p : ℝ) + (q : ℝ) ≤ (u + a) + (2 + 2 * (k₀ : ℝ)) := by linarith
  have hpqb : b * ((p : ℝ) + (q : ℝ)) ≤ b * (u + a) + b * (2 + 2 * (k₀ : ℝ)) := by
    have h := mul_le_mul_of_nonneg_left hpq hb.le
    have heq : b * ((u + a) + (2 + 2 * (k₀ : ℝ)))
        = b * (u + a) + b * (2 + 2 * (k₀ : ℝ)) := by ring
    linarith
  have hbua : 2 * (b * (u + a)) ≤ b * (Fintype.card W : ℝ) := by
    have h := mul_le_mul_of_nonneg_left h2ua hb.le
    have heq : b * (2 * (u + a)) = 2 * (b * (u + a)) := by ring
    linarith
  have hbn : b * (Fintype.card W : ℝ) ≤ (ε / 2) * (Fintype.card W : ℝ) :=
    mul_le_mul_of_nonneg_right hbε hn0
  have htotal : (1 - β) * (∑ T ∈ H, w T) - ε * (Fintype.card W : ℝ)
        - (C₀ + 1 + (k₀ : ℝ) + b * (2 + 2 * (k₀ : ℝ))) ≤ (M.card : ℝ) := by
    rw [hsum, hMcardR]
    have hstep : (1 - β) * (u + a) ≤ (1 - 2 * b) * (u + a) :=
      mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    have hstep' : (1 - 2 * b) * (u + a) = (u + a) - 2 * (b * (u + a)) := by ring
    linarith
  have hmarked : (1 - β) * a - ε * (Fintype.card W : ℝ)
        - (C₀ + 1 + (k₀ : ℝ) + b * (2 + 2 * (k₀ : ℝ)))
      ≤ ((M.filter (fun T => T ∈ A)).card : ℝ) := by
    have hβa : (1 - β) * a ≤ a := by
      have := mul_le_mul_of_nonneg_right (show (1 : ℝ) - β ≤ 1 by linarith) ha0
      linarith
    linarith
  exact ⟨M, hMmatch, htotal, hmarked⟩

end PaperIV.MarkedQuotaSlackGate

namespace PaperIV.MarkedQuotaTypedGain

open Finset

/-- `typed_gain_slack` with explicit `γ = gamQ 6 β ε`, `C = CQ 6 β ε`. -/
theorem typed_gain_slack_explicit (β ε : ℝ) (hβ : 0 < β) (hβ1 : β ≤ 1) (hε : 0 < ε) :
    0 < MarkedQuotaSlackGate.gamQ 6 β ε ∧ 0 < MarkedQuotaSlackGate.CQ 6 β ε ∧
      ∀ {W : Type} [Fintype W] [DecidableEq W]
        (H A : Finset (Finset W)) (w : Finset W → ℝ) (triangleMass : ℝ),
        A ⊆ H →
        NibblePort.Hypergraph.IsUniform H 6 →
        (∀ T, 0 ≤ w T) →
        (∀ v : W, ∑ T ∈ H.filter (fun T => v ∈ T), w T ≤ 1) →
        (∀ x z : W, x ≠ z →
          ∑ T ∈ H.filter (fun T => x ∈ T ∧ z ∈ T), w T ≤ MarkedQuotaSlackGate.gamQ 6 β ε) →
        (triangleMass - 3) / 2 ≤ ∑ T ∈ H \ A, w T →
        ∃ M : Finset (Finset W), NibblePort.Hypergraph.IsMatching H M ∧
          (1 - β) * (2 * triangleMass + 5 * (∑ T ∈ A, w T) - 6)
              - 5 * (ε * (Fintype.card W : ℝ)) - 5 * MarkedQuotaSlackGate.CQ 6 β ε
            ≤ 4 * ((M.filter (fun T => T ∉ A)).card : ℝ)
              + 5 * ((M.filter (fun T => T ∈ A)).card : ℝ) := by
  classical
  obtain ⟨hγ, hC, hgate⟩ :=
    MarkedQuotaSlackGate.slackMarkedQuotaNibbleAt_explicit 6 (by norm_num) β ε hβ hε
  set C := MarkedQuotaSlackGate.CQ 6 β ε with hCdef
  refine ⟨hγ, hC, ?_⟩
  intro W _ _ H A w triangleMass hAH huni hw hload hcod hpair
  obtain ⟨M, hM, htotal, hmarked⟩ := hgate H A w hAH huni hw hload hcod
  refine ⟨M, hM, ?_⟩
  have hsplit : (M.filter (fun T => T ∈ A)).card + (M.filter (fun T => T ∉ A)).card
      = M.card := Finset.card_filter_add_card_filter_not _
  have hsplitR : ((M.filter (fun T => T ∈ A)).card : ℝ)
      + ((M.filter (fun T => T ∉ A)).card : ℝ) = (M.card : ℝ) := by exact_mod_cast hsplit
  have hmass : ∑ T ∈ H, w T = (∑ T ∈ H \ A, w T) + ∑ T ∈ A, w T :=
    (Finset.sum_sdiff hAH).symm
  rw [hmass] at htotal
  have htotal' : (1 - β) * ((∑ T ∈ H \ A, w T) + ∑ T ∈ A, w T)
        - (ε * (Fintype.card W : ℝ) + C)
      ≤ ((M.filter (fun T => T ∉ A)).card : ℝ) + ((M.filter (fun T => T ∈ A)).card : ℝ) := by
    linarith
  have hmarked' : (1 - β) * (∑ T ∈ A, w T) - (ε * (Fintype.card W : ℝ) + C)
      ≤ ((M.filter (fun T => T ∈ A)).card : ℝ) := by linarith
  have key := PaperIV.JointTypedQuota.typed_gain_of_paired_total_and_four_quota_additive
    (β := β) (triangleMass := triangleMass) (pairMass := ∑ T ∈ H \ A, w T)
    (fourMass := ∑ T ∈ A, w T)
    (outPairs := ((M.filter (fun T => T ∉ A)).card : ℝ))
    (outFour := ((M.filter (fun T => T ∈ A)).card : ℝ))
    (errTotal := ε * (Fintype.card W : ℝ) + C)
    (errFour := ε * (Fintype.card W : ℝ) + C)
    hβ1 hpair htotal' hmarked'
  linarith

end PaperIV.MarkedQuotaTypedGain

namespace PaperIV.MarkedQuotaPairing

open Finset
open PaperIV.TrianglePairingDefs
open PaperIV.TrianglePairingSums

/-- `paired_typed_gain_slack` with explicit `γ = gamQ 6 β ε / 2`, `C = 6 / gamQ 6 β ε`,
`D = CQ 6 β ε`. -/
theorem paired_typed_gain_slack_explicit (β ε : ℝ) (hβ : 0 < β) (hβ1 : β ≤ 1) (hε : 0 < ε) :
    0 < MarkedQuotaSlackGate.gamQ 6 β ε / 2 ∧ 0 < 6 / MarkedQuotaSlackGate.gamQ 6 β ε ∧
      0 < MarkedQuotaSlackGate.CQ 6 β ε ∧
      ∀ {W : Type} [Fintype W] [DecidableEq W]
        (H₃ H₄ : Finset (Finset W)) (w : Finset W → ℝ),
        NibblePort.Hypergraph.IsUniform H₃ 3 →
        NibblePort.Hypergraph.IsUniform H₄ 6 →
        Disjoint H₄ (pairFam H₃) →
        (∀ T, 0 ≤ w T) →
        (∀ v : W, (∑ T ∈ H₃.filter (fun T => v ∈ T), w T)
            + (∑ T ∈ H₄.filter (fun T => v ∈ T), w T) ≤ 1) →
        (∀ x z : W, x ≠ z → (∑ T ∈ H₃.filter (fun T => x ∈ T ∧ z ∈ T), w T)
            + (∑ T ∈ H₄.filter (fun T => x ∈ T ∧ z ∈ T), w T)
              ≤ MarkedQuotaSlackGate.gamQ 6 β ε / 2) →
        6 / MarkedQuotaSlackGate.gamQ 6 β ε ≤ ∑ T ∈ H₃, w T →
        ∃ M : Finset (Finset W),
          NibblePort.Hypergraph.IsMatching (bigFam H₃ H₄) M ∧
          (1 - β) * (2 * (∑ T ∈ H₃, w T) + 5 * (∑ T ∈ H₄, w T) - 6)
              - 5 * (ε * (Fintype.card W : ℝ)) - 5 * MarkedQuotaSlackGate.CQ 6 β ε
            ≤ 4 * ((M.filter (fun T => T ∉ H₄)).card : ℝ)
              + 5 * ((M.filter (fun T => T ∈ H₄)).card : ℝ) := by
  classical
  obtain ⟨hγ₀, hD, hmain⟩ :=
    MarkedQuotaTypedGain.typed_gain_slack_explicit β ε hβ hβ1 hε
  set γ₀ := MarkedQuotaSlackGate.gamQ 6 β ε with hγ₀def
  set D := MarkedQuotaSlackGate.CQ 6 β ε with hDdef
  refine ⟨by linarith, by positivity, hD, ?_⟩
  intro W _ _ H₃ H₄ w h3 h4 hdisj hw hload hcod hmass
  set t : ℝ := ∑ T ∈ H₃, w T with ht_def
  have htpos : 0 < t := lt_of_lt_of_le (by positivity) hmass
  have hthr : 3 / t ≤ γ₀ / 2 := by
    rw [div_le_div_iff₀ htpos (by norm_num : (0 : ℝ) < 2)]
    rw [div_le_iff₀ hγ₀] at hmass
    linarith
  have honet : 1 / t ≤ γ₀ / 2 := by
    have h1 : 1 / t ≤ 3 / t := by
      apply div_le_div_of_nonneg_right _ htpos.le
      norm_num
    linarith
  have hload3 : ∀ v : W, ∑ T ∈ H₃.filter (fun T => v ∈ T), w T ≤ 1 := by
    intro v
    have h4nn : (0 : ℝ) ≤ ∑ T ∈ H₄.filter (fun T => v ∈ T), w T :=
      Finset.sum_nonneg fun T _ => hw T
    linarith [hload v]
  have hbigload : ∀ v : W,
      ∑ T ∈ (bigFam H₃ H₄).filter (fun T => v ∈ T), bigWeight H₃ H₄ w t T ≤ 1 := by
    intro v
    rw [sum_bigWeight_filter w t hdisj (fun T => v ∈ T)]
    have hp := pairs_load_le (H₃ := H₃) (w := w) (t := t) hw htpos
      (le_of_eq ht_def.symm) v
    linarith [hload v]
  have hbigcod : ∀ x z : W, x ≠ z →
      ∑ T ∈ (bigFam H₃ H₄).filter (fun T => x ∈ T ∧ z ∈ T),
          bigWeight H₃ H₄ w t T ≤ γ₀ := by
    intro x z hxz
    rw [sum_bigWeight_filter w t hdisj (fun T => x ∈ T ∧ z ∈ T)]
    have hp := pairs_codeg_le (H₃ := H₃) (w := w) (t := t) hw htpos ht_def hload3 x z
    linarith [hcod x z hxz]
  have hpair : (t - 3) / 2 ≤
      ∑ T ∈ bigFam H₃ H₄ \ H₄, bigWeight H₃ H₄ w t T := by
    rw [sum_bigWeight_sdiff w t hdisj]
    exact pairs_mass_ge h3 hw htpos ht_def hload3
  obtain ⟨M, hM, hgain⟩ :=
    hmain (bigFam H₃ H₄) H₄ (bigWeight H₃ H₄ w t) t
      Finset.subset_union_left (bigFam_uniform h3 h4)
      (bigWeight_nonneg hw htpos.le) hbigload hbigcod hpair
  refine ⟨M, hM, ?_⟩
  rw [sum_bigWeight_four w t] at hgain
  simpa [ht_def] using hgain

end PaperIV.MarkedQuotaPairing

namespace PaperIV.JointTwoQuotaPhysical

open Finset
open PaperIV.FarRounding
open PaperIV.NibblePort
open PaperIV.JointTypedNibbleGate
open PaperIV.TrianglePairingDefs

/-- `mixed_physical_packing_of_slackMarkedQuota` with the explicit constants of
`paired_typed_gain_slack_explicit`. -/
theorem mixed_physical_packing_of_slackMarkedQuota_explicit (β ε : ℝ)
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hε : 0 < ε) :
    0 < MarkedQuotaSlackGate.gamQ 6 β ε / 2 ∧ 0 < 6 / MarkedQuotaSlackGate.gamQ 6 β ε ∧
      0 < MarkedQuotaSlackGate.CQ 6 β ε ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
        (x : MixedRounding.FracPacking G),
        (∀ e f : Sym2 V, e ≠ f →
          ∑ S ∈ (jointSupports G).filter (fun S => e ∈ S ∧ f ∈ S),
            MixedRounding.inducedWeight x S ≤ MarkedQuotaSlackGate.gamQ 6 β ε / 2) →
        6 / MarkedQuotaSlackGate.gamQ 6 β ε ≤ triangleMass x →
        ∃ P : MixedRounding.Packing G,
          (1 - β) * (2 * triangleMass x + 5 * fourCliqueMass x - 6)
              - 5 * (ε * (Fintype.card (Sym2 V) : ℝ)) - 5 * MarkedQuotaSlackGate.CQ 6 β ε
            ≤ (P.gain : ℝ) := by
  classical
  obtain ⟨hγ, hC, hD, hmain⟩ :=
    MarkedQuotaPairing.paired_typed_gain_slack_explicit β ε hβ hβ1 hε
  set γ := MarkedQuotaSlackGate.gamQ 6 β ε / 2 with hγdef
  set C := 6 / MarkedQuotaSlackGate.gamQ 6 β ε with hCdef
  set D := MarkedQuotaSlackGate.CQ 6 β ε with hDdef
  refine ⟨hγ, hC, hD, ?_⟩
  intro V _ _ G _ x hcod hmass
  set w : Finset (Sym2 V) → ℝ := MixedRounding.inducedWeight x with hw_def
  have hwnn : ∀ T, 0 ≤ w T := fun T => MixedRounding.inducedWeight_nonneg x T
  have hload : ∀ e : Sym2 V,
      (∑ S ∈ (k3Supports G).filter (fun S => e ∈ S), w S)
        + (∑ S ∈ (k4Supports G).filter (fun S => e ∈ S), w S) ≤ 1 := by
    intro e
    rw [← joint_sum_split x (fun S => e ∈ S), jointSupports_eq_supports]
    exact joint_load_le_one x e
  have hcod' : ∀ e f : Sym2 V, e ≠ f →
      (∑ S ∈ (k3Supports G).filter (fun S => e ∈ S ∧ f ∈ S), w S)
        + (∑ S ∈ (k4Supports G).filter (fun S => e ∈ S ∧ f ∈ S), w S) ≤ γ := by
    intro e f hef
    rw [← joint_sum_split x (fun S => e ∈ S ∧ f ∈ S)]
    exact hcod e f hef
  have hmass' : C ≤ ∑ S ∈ k3Supports G, w S := by
    rw [sum_k3Supports_eq]
    exact hmass
  obtain ⟨Mstar, hMstar, hgain⟩ :=
    hmain (k3Supports G) (k4Supports G) w
      k3Supports_uniform k4Supports_uniform k4Supports_disjoint_pairFam
      hwnn hload hcod' hmass'
  set M := TrianglePairingSplit.unfoldMatching (k3Supports G) (k4Supports G) Mstar with hMdef
  have hMmatch : NibblePort.Hypergraph.IsMatching (k3Supports G ∪ k4Supports G) M := by
    rw [hMdef]
    exact TrianglePairingSplit.unfold_isMatching k3Supports_uniform hMstar
  have hMjoint : NibblePort.Hypergraph.IsMatching (jointSupports G) M := by
    rw [jointSupports]
    exact hMmatch
  obtain ⟨P, hP⟩ := packing_of_joint_matching_counted M hMjoint
  have hsix : M.filter (fun S => S.card = 6) = M.filter (fun S => S ∈ k4Supports G) := by
    apply Finset.filter_congr
    intro S hS
    constructor
    · intro h6
      rcases Finset.mem_union.1 (hMjoint.subset hS) with h | h
      · have h3 := k3Supports_uniform S h
        omega
      · exact h
    · intro h
      exact k4Supports_uniform S h
  have hfour : M.filter (fun S => S ∈ k4Supports G)
      = Mstar.filter (fun S => S ∈ k4Supports G) := by
    rw [hMdef]
    exact TrianglePairingSplit.unfold_filter_four
      k3Supports_uniform k4Supports_uniform hMstar
  have hcardsplit : (M.filter (fun S => S.card = 3)).card
      + (M.filter (fun S => S.card = 6)).card = M.card := by
    have hcompl : M.filter (fun S => ¬ S.card = 3) = M.filter (fun S => S.card = 6) := by
      apply Finset.filter_congr
      intro S hS
      rcases jointSupports_card (hMjoint.subset hS) with h | h <;> simp [h]
    rw [← hcompl]
    exact Finset.card_filter_add_card_filter_not (s := M) (p := fun S => S.card = 3)
  have hMcard : M.card
      = (Mstar.filter (fun S => S ∈ k4Supports G)).card
        + 2 * (Mstar.filter (fun S => S ∉ k4Supports G)).card := by
    rw [hMdef]
    exact TrianglePairingSplit.unfold_card
      k3Supports_uniform k4Supports_uniform hMstar
  have hthree : (M.filter (fun S => S.card = 3)).card
      = 2 * (Mstar.filter (fun S => S ∉ k4Supports G)).card := by
    rw [hsix, hfour] at hcardsplit
    omega
  refine ⟨MixedRoundingAdapter.ofFarPacking P, ?_⟩
  rw [MixedRoundingAdapter.gain_ofFarPacking, hP]
  rw [hthree, hsix, hfour]
  rw [sum_k3Supports_eq, sum_k4Supports_eq] at hgain
  norm_num at hgain ⊢
  convert hgain using 1 <;> ring

end PaperIV.JointTwoQuotaPhysical

namespace PaperIV.RC01MarkedRounding

open Finset
open MixedRounding
open PaperIV.JointTwoQuotaPhysical

/-- Explicit codegree constant of the slack marked rounding at target `ζ`. -/
noncomputable def gamZ (ζ : ℝ) : ℝ := MarkedQuotaSlackGate.gamQ 6 (ζ / 4) (ζ / 20) / 2
/-- Explicit triangle-mass constant of the slack marked rounding at target `ζ`. -/
noncomputable def CZ (ζ : ℝ) : ℝ := 6 / MarkedQuotaSlackGate.gamQ 6 (ζ / 4) (ζ / 20)
/-- Explicit additive slack constant of the slack marked rounding at target `ζ`. -/
noncomputable def DZ (ζ : ℝ) : ℝ := MarkedQuotaSlackGate.CQ 6 (ζ / 4) (ζ / 20)

/-- `exists_packing_loss_le_of_slackMarkedQuota` with explicit `γ = gamZ ζ`, `C = CZ ζ`,
`D = DZ ζ`. -/
theorem exists_packing_loss_le_of_slackMarkedQuota_explicit
    (ζ : ℝ) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) :
    0 < gamZ ζ ∧ 0 < CZ ζ ∧ 0 < DZ ζ ∧
      ∀ (n : ℕ), 1 ≤ n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
        (x : FracPacking G),
        12 + 10 * DZ ζ ≤ ζ * (n : ℝ) ^ 2 →
        (∀ e f : Sym2 (Fin n), e ≠ f →
          ∑ S ∈ (PaperIV.JointTypedNibbleGate.jointSupports G).filter
              (fun S => e ∈ S ∧ f ∈ S),
            MixedRounding.inducedWeight x S ≤ gamZ ζ) →
        CZ ζ ≤ triangleMass x →
        ∃ P : Packing G,
          (((x.value : ℚ) : ℝ) - (P.gain : ℝ)) ≤ ζ * (n : ℝ) ^ 2 := by
  have hβ : (0 : ℝ) < ζ / 4 := by positivity
  have hβ1 : ζ / 4 ≤ (1 : ℝ) := by linarith
  have hε : (0 : ℝ) < ζ / 20 := by positivity
  obtain ⟨hγ, hC, hD, hselect⟩ :=
    mixed_physical_packing_of_slackMarkedQuota_explicit (ζ / 4) (ζ / 20) hβ hβ1 hε
  unfold gamZ CZ DZ
  refine ⟨hγ, hC, hD, ?_⟩
  intro n hn G _ x hsize hcodeg hmass
  have hcard := card_sym2_fin_le_sq hn
  obtain ⟨P, hP⟩ := hselect (Fin n) G x hcodeg hmass
  refine ⟨P, ?_⟩
  have hvalueQ := PaperIV.UniformDual.value_le_of_card
    (PaperIV.MixedRoundingAdapter.toFarFrac x)
  rw [PaperIV.MixedRoundingAdapter.value_toFarFrac] at hvalueQ
  have hvalue : ((x.value : ℚ) : ℝ) ≤ (5 / 12 : ℝ) * (n : ℝ) ^ 2 := by
    have h := (Rat.cast_le (K := ℝ)).2 hvalueQ
    norm_num at h ⊢
    exact h
  have hβvalue : (ζ / 4) * ((x.value : ℚ) : ℝ)
      ≤ (ζ / 4) * ((5 / 12 : ℝ) * (n : ℝ) ^ 2) :=
    mul_le_mul_of_nonneg_left hvalue hβ.le
  have hcard' : (ζ / 4) * (Fintype.card (Sym2 (Fin n)) : ℝ)
      ≤ (ζ / 4) * (n : ℝ) ^ 2 :=
    mul_le_mul_of_nonneg_left hcard (by positivity)
  have hsplit := value_cast_eq_masses x
  nlinarith

end PaperIV.RC01MarkedRounding

namespace PaperIV.RC01UniformDenseGate

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

/-- **Explicit codegree constant** `gam` of the uniform dense physical gate. -/
noncomputable def gamE (zeta : ℝ) : ℝ := PaperIV.RC01MarkedRounding.gamZ zeta
/-- **Explicit triangle-mass constant** `Cst` of the uniform dense physical gate. -/
noncomputable def CstE (zeta : ℝ) : ℝ := PaperIV.RC01MarkedRounding.CZ zeta
/-- **Explicit additive constant** `D` of the uniform dense physical gate. -/
noncomputable def DE (zeta : ℝ) : ℝ := PaperIV.RC01MarkedRounding.DZ zeta

/-- **`exists_packing_mass_loss_le_denseActive_uniform` with explicit constants**
`gam = gamE zeta`, `Cst = CstE zeta`, `D = DE zeta`. -/
theorem exists_packing_mass_loss_le_denseActive_uniform_explicit
    (zeta : ℝ) (hzeta : 0 < zeta) (hzeta1 : zeta ≤ 1) :
    0 < gamE zeta ∧ 0 < CstE zeta ∧ 0 < DE zeta ∧
      ∀ (n : ℕ) [NeZero n] (Gn : SimpleGraph (Fin n)) [DecidableRel Gn.Adj]
        {δ d θ u v gamma : ℚ} (R : EqualRegularity Gn δ) (x : FracPacking Gn),
        ∀ (hδ : 0 ≤ δ) (hd : 0 ≤ d) (hu : 0 < u) (hv : 0 ≤ v)
        (hc3 : 0 < d ^ 3 - 3 * δ) (hc4 : 0 < d ^ 6 - 6 * δ)
        (hchoice3 : 33 * δ ≤ v * u ^ 2 * (d ^ 3 - 3 * δ) ^ 3)
        (hchoice4 : 138 * δ ≤ v * u ^ 2 * (d ^ 6 - 6 * δ) ^ 3),
        ((denseActiveProfiles R x d θ).card : ℚ) * (d ^ 6 - 6 * δ) +
            ((denseActiveProfiles R x d θ).card : ℚ) * (d ^ 3 - 3 * δ)
          ≤ gamma * (d ^ 3 - 3 * δ) * (d ^ 6 - 6 * δ) * (R.size : ℚ) →
        (gamma : ℝ) ≤ gamE zeta →
        12 + 10 * DE zeta ≤ zeta * (n : ℝ) ^ 2 →
        CstE zeta ≤ PaperIV.JointTwoQuotaPhysical.triangleMass
          (cleanedPacking x (partOf R) (denseActiveProfiles R x d θ)
            (rootwiseReference (G := Gn) (partOf R))
            (profileVolume (G := Gn) (partOf R)) u hu.le
            (denseActiveProfiles_profileVolume_pos hδ hd hc3 hc4 R x)
            (fun H _ f => rootwiseReference_volume_budget (G := Gn) (partOf R) H f)) →
        ∃ Pk : Packing Gn,
          (((1 - u - v) *
              (∑ H ∈ denseActiveProfiles R x d θ,
                patternGain H * PaperIV.PatternTransfer.psiT x (partOf R) H) : ℚ) : ℝ)
            - (Pk.gain : ℝ) ≤ zeta * (n : ℝ) ^ 2 := by
  obtain ⟨hgam, hCst, hD, hslack⟩ :=
    PaperIV.RC01MarkedRounding.exists_packing_loss_le_of_slackMarkedQuota_explicit zeta
      hzeta hzeta1
  refine ⟨hgam, hCst, hD, ?_⟩
  intro n _ Gn _ δ d θ u v gamma R x hδ hd hu hv hc3 hc4 hchoice3 hchoice4
    hthreshold hgamma hsize hmass
  classical
  set Pats := denseActiveProfiles R x d θ with hPats
  set A := rootwiseReference (G := Gn) (partOf R) with hA
  set vol := profileVolume (G := Gn) (partOf R) with hvolDef
  have hvolpos : ∀ H ∈ Pats, 0 < vol H :=
    denseActiveProfiles_profileVolume_pos hδ hd hc3 hc4 R x
  have hvol : ∀ H ∈ Pats, ∀ f : Sym2 (Fin n),
      A H (partsOf (partOf R) f) * densT Gn (partOf R) f ≤ vol H :=
    fun H _ f => rootwiseReference_volume_budget (G := Gn) (partOf R) H f
  -- the geometric data of the dense family, exactly as in `RC01DensePhysicalGate`
  have hcard : ∀ H ∈ Pats, H.card = 3 ∨ H.card = 4 := fun H hH =>
    denseActiveProfiles_card R x d θ hH
  have hpart : ∀ H ∈ Pats, ∀ p ∈ H,
      (univ.filter (fun w => partOf R w = p)).card ≤ R.size :=
    denseActiveProfiles_class_card_le R x d θ
  have hlower := denseActiveProfiles_profileVolume_lower (θ := θ) hδ hd R x
  have hb3 : ∀ H ∈ Pats, H.card = 3 →
      (d ^ 3 - 3 * δ) * (R.size : ℚ) ^ 2 * (R.size : ℚ) ≤ (1 + u) * vol H := by
    intro H hH hH3
    rcases hlower H hH with h3 | h4
    · have hbase : (d ^ 3 - 3 * δ) * (R.size : ℚ) ^ 2 * (R.size : ℚ) ≤ vol H := by
        nlinarith [h3.2]
      have hnonneg : 0 ≤ vol H := le_of_lt (hvolpos H hH)
      nlinarith
    · omega
  have hb4 : ∀ H ∈ Pats, H.card = 4 →
      (d ^ 6 - 6 * δ) * (R.size : ℚ) ^ 2 * (R.size : ℚ) ^ 2 ≤ (1 + u) * vol H := by
    intro H hH hH4
    rcases hlower H hH with h3 | h4
    · omega
    · have hbase : (d ^ 6 - 6 * δ) * (R.size : ℚ) ^ 2 * (R.size : ℚ) ^ 2 ≤ vol H := by
        nlinarith [h4.2]
      have hnonneg : 0 ≤ vol H := le_of_lt (hvolpos H hH)
      nlinarith
  have hclean : ∀ H ∈ Pats,
      (1 - v) * vol H ≤ ((cleanFiber Gn (partOf R) A u H).card : ℚ) :=
    denseActiveProfiles_clean_retention hδ hd hu hv hc3 hc4 hchoice3 hchoice4 R x
  have hk3 : (((Pats.filter (fun H => H.card = 3)).card : ℕ) : ℚ) ≤ (Pats.card : ℚ) := by
    exact_mod_cast Finset.card_filter_le (s := Pats) (p := fun H => H.card = 3)
  have hk4 : (((Pats.filter (fun H => ¬ H.card = 3)).card : ℕ) : ℚ) ≤ (Pats.card : ℚ) := by
    exact_mod_cast Finset.card_filter_le (s := Pats) (p := fun H => ¬ H.card = 3)
  have href : ∀ H ∈ Pats, vol H ≤ ((profileFiber Gn (partOf R) H).card : ℚ) :=
    fun H _ => le_of_eq rfl
  -- every retained pattern serves at least one real pair
  have hserved : ∀ H ∈ Pats, ∃ e : Sym2 (Fin n), H ∈ servingT (partOf R) e := by
    intro H hH
    have hposQ : (0 : ℚ) < ((profileFiber Gn (partOf R) H).card : ℚ) :=
      lt_of_lt_of_le (hvolpos H hH) (href H hH)
    have hpos : 0 < (profileFiber Gn (partOf R) H).card := by exact_mod_cast hposQ
    obtain ⟨K, hK⟩ := Finset.card_pos.1 hpos
    have hitem : IsItem Gn K := mem_items.1 (mem_profileFiber.1 hK).1
    have hpairs : (pairs K).Nonempty := by
      rw [← Finset.card_pos, card_pairs]
      rcases hitem.2 with h3 | h4
      · simp [h3]
      · rw [h4]
        decide +kernel
    obtain ⟨e, he⟩ := hpairs
    exact ⟨e, serving_of_mem_profileFiber hK he⟩
  have ht : 1 ≤ R.size := R.size_pos
  have hthreshold' :
      (Pats.card : ℚ) * (d ^ 6 - 6 * δ) + (Pats.card : ℚ) * (d ^ 3 - 3 * δ)
        ≤ gamma * (d ^ 3 - 3 * δ) * (d ^ 6 - 6 * δ) * (R.size : ℚ) := hthreshold
  -- (C.1) the joint codegree of the cleaned packing
  have hcodeg := cleanedPacking_joint_codegree_le_of_served_patterns x (partOf R)
    Pats A vol u hu.le hvolpos hvol R.size (Pats.card : ℚ) (Pats.card : ℚ)
    (d ^ 3 - 3 * δ) (d ^ 6 - 6 * δ) gamma ht hc3 hc4 hserved hcard hpart hk3 hk4
    hb3 hb4 (by linarith [hthreshold'])
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.2 (NeZero.ne n)
  obtain ⟨Pk, hPk⟩ := hslack n hn1 Gn
    (cleanedPacking x (partOf R) Pats A vol u hu.le hvolpos hvol) hsize
    (fun e f hef => le_trans (hcodeg e f hef) hgamma) hmass
  refine ⟨Pk, ?_⟩
  -- (C.2) the cleaned packing retains the transferred objective
  have hvalue := cleanedPacking_value_ge x (partOf R) Pats A vol u hu.le hvolpos
    hvol v hv hcard hclean
  have hcast :
      (((1 - u - v) * (∑ H ∈ Pats, patternGain H * psiT x (partOf R) H) : ℚ) : ℝ)
        ≤ (((cleanedPacking x (partOf R) Pats A vol u hu.le hvolpos hvol).value : ℚ) : ℝ) := by
    exact_mod_cast hvalue
  linarith

end PaperIV.RC01UniformDenseGate
