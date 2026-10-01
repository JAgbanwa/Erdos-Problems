import PaperIV.MarkedQuotaGate
import PaperIV.PaperIIISlackNibbleAdapter

/-!
# RC01: the additive marked-quota gate over the *slack* nibble

`PaperIV.MarkedQuotaGate.additiveMarkedQuotaNibbleAt_proved` runs the token
extension over Paper III's **near-perfect** nibble, and therefore inherits its
two unphysical hypotheses: a lower bound `1 - γ` for the load of every vertex
outside a small exceptional set, and a bound on the size of that exceptional
set.  The RC01 physical schedule does not produce such lower loads, and the
attempted implication from simultaneous layer survival to near-perfect lower
loads is false.

This module replaces that adapter.  It runs the same token extension over the
frozen **bounded-rank nibble with slack**
`PaperIV.PaperIIISlackNibbleAdapter.boundedRankNibbleAt`
(`Nibble.fracNibble_leUniform`), whose hypotheses are only:

* bounded edge size (nonempty edges of at most `r` vertices);
* nonnegative weights;
* upper loads at most `1`;
* small weighted codegrees,

and whose conclusion carries the additive loss `b·|W| + C`.  No lower load and
no exceptional set occur anywhere.

The output is one matching keeping, simultaneously,

* the total mass, and
* the mass of one arbitrary marked subfamily `A ⊆ H`,

each up to a multiplicative `1 - β` and an **additive** `ε·|W| + C`.

The arithmetic is exactly the rank-`r` form of the budget certified in
`checks/rc01_slack_marked_quota_budget.py`: with `u + a ≤ |W| / r` and `r ≥ 2`,
an inner slack parameter `b ≤ ε / 2` charges both the slack loss `b·|W|` and
the mass loss `2b(u + a) ≤ b·|W|` against `ε·|W|`; the token pool overshoot is
the constant part.  (As in the certificate, the extra assumption `b ≤ β` is not
needed for the marked inequality; here `b ≤ β/2` is used only for the total
one.)
-/

namespace PaperIV.MarkedQuotaSlackGate

open Finset
open PaperIV.MarkedQuotaTokens

/-- The conclusion of the slack marked-quota nibble: one matching keeping the
total mass and the marked mass, each up to `(1-β)` multiplicatively and up to
an additive `ε |W| + C`. -/
def SlackMarkedQuotaConclusion {W : Type*} [Fintype W] [DecidableEq W]
    (H A M : Finset (Finset W)) (w : Finset W → ℝ) (β ε C : ℝ) : Prop :=
  NibblePort.Hypergraph.IsMatching H M ∧
    (1 - β) * (∑ T ∈ H, w T) - ε * (Fintype.card W : ℝ) - C ≤ (M.card : ℝ) ∧
    (1 - β) * (∑ T ∈ A, w T) - ε * (Fintype.card W : ℝ) - C
      ≤ ((M.filter (fun T => T ∈ A)).card : ℝ)

set_option maxHeartbeats 4000000 in
/-- **The additive marked-quota nibble gate over the slack nibble.**

For every rank `r ≥ 2` and all `β, ε > 0` there are `γ, C > 0` such that every
`r`-uniform system with nonnegative weights, upper loads at most `1` and
weighted codegrees at most `γ` admits **one** matching which keeps `(1-β)` of
the total mass and `(1-β)` of the mass of any declared marked subfamily, each
up to the additive loss `ε |W| + C`.

There is **no lower-load hypothesis and no exceptional set**. -/
theorem slackMarkedQuotaNibbleAt_proved (r : ℕ) (hr : 2 ≤ r) (β ε : ℝ)
    (hβ : 0 < β) (hε : 0 < ε) :
    ∃ γ : ℝ, 0 < γ ∧ ∃ C : ℝ, 0 < C ∧
      ∀ {W : Type} [Fintype W] [DecidableEq W]
        (H A : Finset (Finset W)) (w : Finset W → ℝ),
        A ⊆ H →
        NibblePort.Hypergraph.IsUniform H r →
        (∀ T, 0 ≤ w T) →
        (∀ v : W, ∑ T ∈ H.filter (fun T => v ∈ T), w T ≤ 1) →
        (∀ x z : W, x ≠ z →
          ∑ T ∈ H.filter (fun T => x ∈ T ∧ z ∈ T), w T ≤ γ) →
        ∃ M : Finset (Finset W), SlackMarkedQuotaConclusion H A M w β ε C := by
  classical
  have hrR : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  set b : ℝ := min (β / 2) (ε / 2) with hbdef
  have hb : 0 < b := lt_min (by positivity) (by positivity)
  have hbβ : b ≤ β / 2 := min_le_left _ _
  have hbε : b ≤ ε / 2 := min_le_right _ _
  obtain ⟨γ₀, hγ₀, C₀, hC₀, hmain⟩ :=
    PaperIIISlackNibbleAdapter.boundedRankNibbleAt (r + 1) (by omega) b hb
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
  refine ⟨γ₀, hγ₀, C₀ + 1 + (k₀ : ℝ) + b * (2 + 2 * (k₀ : ℝ)),
    by positivity, ?_⟩
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
