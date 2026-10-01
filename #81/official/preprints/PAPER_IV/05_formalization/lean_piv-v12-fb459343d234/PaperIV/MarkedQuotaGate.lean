import PaperIV.MarkedQuotaNibble
import PaperIV.MarkedQuotaTokens

/-!
# RC01: the additive marked-quota nibble gate, proved

`PaperIV.MarkedQuotaNibble.AdditiveMarkedQuotaNibbleAt r β ε` is the minimal
probabilistic obligation left by the triangle-pairing reduction: **one** matching
of an `r`-uniform near-perfect fractional matching which keeps, at once, the
total mass and the mass of a declared marked subfamily `A ⊆ H`, the marked
inequality being allowed an additive loss `ε |W|`.

This module proves it, for every rank `r ≥ 2` and all `β, ε > 0`, from the
frozen Paper III near-perfect nibble alone.  The device is the token extension
of `PaperIV.MarkedQuotaTokens`:

* each edge of `H \ A` is extended by a token from a pool of size
  `p = max ⌈unmarked mass⌉ k₀`, each edge of `A` by a token from a disjoint pool
  of size `q = max ⌈marked mass⌉ k₀`, the weight being spread uniformly over the
  pool.  The extended system is `(r+1)`-uniform, has the same total mass and the
  same loads on the old vertices, and the pool vertices carry load
  `mass/pool size ≈ 1`, so it is again near-perfect with small codegrees;
* Paper III's nibble returns a matching of the extended system whose
  **cardinality** is at least `(1-β')` times the total mass;
* a matching uses every token at most once, hence contains at most `p` unmarked
  edges; so it must contain at least `(1-β')(u+a) - p ≥ a - β'(u+a) - 1 - k₀`
  marked edges, which is the marked quota up to the allowed additive loss once
  `β'` is chosen small and `|W|` is large.

That the hypotheses force `|W|` to be large is itself a consequence of the
codegree bound (`card_ge_of_codegree`): a vertex of load close to `1` needs at
least `(1-γ)/γ` edges through it.

No new hypothesis is used: the only non-Mathlib input is the audited Paper III
theorem `Nibble.fracNibbleWeighted_nearPerfect`, through
`PaperIV.PaperIIINibbleAdapter.nearPerfectNibbleAt`.
-/

namespace PaperIV.MarkedQuotaGate

open Finset
open PaperIV.MarkedQuotaTokens

/-! ## Generic counting lemmas -/

section Generic

variable {W : Type} [Fintype W] [DecidableEq W]

/-- Summing the loads of all vertices counts every edge `r` times. -/
lemma sum_loads_eq_mul (H : Finset (Finset W)) (w : Finset W → ℝ) (r : ℕ)
    (huni : ∀ T ∈ H, T.card = r) :
    ∑ v : W, ∑ T ∈ H.filter (fun T => v ∈ T), w T = (r : ℝ) * ∑ T ∈ H, w T := by
  classical
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  have h2 : ∀ T ∈ H, (∑ _v : W, if _v ∈ T then w T else 0) = (r : ℝ) * w T := by
    intro T hT
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, huni T hT, nsmul_eq_mul]
  rw [Finset.sum_congr rfl h2, ← Finset.mul_sum]

/-- A fractional matching of an `r`-uniform system has mass at most `|W|/r`. -/
lemma mass_le_card {H : Finset (Finset W)} {w : Finset W → ℝ} {r : ℕ}
    (huni : ∀ T ∈ H, T.card = r)
    (hload : ∀ v : W, ∑ T ∈ H.filter (fun T => v ∈ T), w T ≤ 1) :
    (r : ℝ) * (∑ T ∈ H, w T) ≤ (Fintype.card W : ℝ) := by
  classical
  rw [← sum_loads_eq_mul H w r huni]
  calc ∑ v : W, ∑ T ∈ H.filter (fun T => v ∈ T), w T ≤ ∑ _v : W, (1 : ℝ) :=
        Finset.sum_le_sum (fun v _ => hload v)
    _ = (Fintype.card W : ℝ) := by simp [Finset.card_univ]

omit [Fintype W] in
/-- Under a weighted codegree bound, every single edge weight is small. -/
lemma weight_le_of_codegree {H : Finset (Finset W)} {w : Finset W → ℝ} {r : ℕ} {γ : ℝ}
    (hr : 2 ≤ r) (huni : ∀ T ∈ H, T.card = r) (hw : ∀ T, 0 ≤ w T)
    (hcod : ∀ x z : W, x ≠ z → ∑ T ∈ H.filter (fun T => x ∈ T ∧ z ∈ T), w T ≤ γ)
    {T : Finset W} (hT : T ∈ H) {v : W} (hv : v ∈ T) : w T ≤ γ := by
  classical
  have h2 : 1 < T.card := by rw [huni T hT]; omega
  obtain ⟨z, hz, hzv⟩ := Finset.exists_mem_ne h2 v
  refine le_trans ?_ (hcod v z (Ne.symm hzv))
  exact Finset.single_le_sum (f := w) (fun T' _ => hw T')
    (Finset.mem_filter.2 ⟨hT, hv, hz⟩)

/-- A near-perfect fractional matching with tiny weighted codegrees forces the
ground set to be large: some vertex carries load `≥ 1-γ` from edges of weight at
most `γ` each, and there are at most `2^{|W|}` edges through it. -/
lemma card_ge_of_codegree {H : Finset (Finset W)} {w : Finset W → ℝ} {r : ℕ} {γ : ℝ}
    {Exc : Finset W} (hr : 2 ≤ r) (huni : ∀ T ∈ H, T.card = r) (hw : ∀ T, 0 ≤ w T)
    (hγ : 0 ≤ γ)
    (hcod : ∀ x z : W, x ≠ z → ∑ T ∈ H.filter (fun T => x ∈ T ∧ z ∈ T), w T ≤ γ)
    (hlow : ∀ v : W, v ∉ Exc → 1 - γ ≤ ∑ T ∈ H.filter (fun T => v ∈ T), w T)
    {v : W} (hv : v ∉ Exc) :
    1 - γ ≤ (2 : ℝ) ^ (Fintype.card W) * γ := by
  classical
  have h1 : ∑ T ∈ H.filter (fun T => v ∈ T), w T
      ≤ ((H.filter (fun T => v ∈ T)).card : ℝ) * γ := by
    calc ∑ T ∈ H.filter (fun T => v ∈ T), w T
        ≤ ∑ _T ∈ H.filter (fun T => v ∈ T), γ :=
          Finset.sum_le_sum (fun T hT => weight_le_of_codegree hr huni hw hcod
            (Finset.mem_filter.1 hT).1 (Finset.mem_filter.1 hT).2)
      _ = ((H.filter (fun T => v ∈ T)).card : ℝ) * γ := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have h2 : ((H.filter (fun T => v ∈ T)).card : ℝ) ≤ (2 : ℝ) ^ (Fintype.card W) := by
    have hle : (H.filter (fun T => v ∈ T)).card ≤ 2 ^ (Fintype.card W) := by
      simpa [Fintype.card_finset] using Finset.card_le_univ (H.filter (fun T => v ∈ T))
    exact_mod_cast hle
  have h3 : ((H.filter (fun T => v ∈ T)).card : ℝ) * γ ≤ (2 : ℝ) ^ (Fintype.card W) * γ :=
    mul_le_mul_of_nonneg_right h2 hγ
  exact le_trans (hlow v hv) (le_trans h1 h3)

end Generic

/-! ## The gate -/

set_option maxHeartbeats 4000000 in
/-- **The additive marked-quota nibble gate.**  For every rank `r ≥ 2` and all
`β, ε > 0` there are `γ, η > 0` such that every `r`-uniform near-perfect
fractional matching with weighted codegrees at most `γ` admits **one** matching
which keeps `(1-β)` of the total mass and, up to an additive `ε |W|`, also
`(1-β)` of the mass of any declared marked subfamily. -/
theorem additiveMarkedQuotaNibbleAt_proved (r : ℕ) (hr : 2 ≤ r) (β ε : ℝ)
    (hβ : 0 < β) (hε : 0 < ε) :
    MarkedQuotaNibble.AdditiveMarkedQuotaNibbleAt r β ε := by
  classical
  have hrpos : (0 : ℝ) < r := by
    have : (0 : ℕ) < r := by omega
    exact_mod_cast this
  set β' : ℝ := min β (ε * r / 2) with hβ'def
  have hβ' : 0 < β' := lt_min hβ (by positivity)
  have hβ'β : β' ≤ β := min_le_left _ _
  have hβ'ε : β' ≤ ε * r / 2 := min_le_right _ _
  obtain ⟨γ₀, hγ₀, η₀, hη₀, hmain⟩ :=
    PaperIIINibbleAdapter.nearPerfectNibbleAt (r + 1) (by omega) β' hβ'
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
  set N₀ : ℕ := ⌈4 * (k₀ : ℝ) / η₀⌉₊ + ⌈2 * (1 + (k₀ : ℝ)) / ε⌉₊ + 1 with hN₀def
  have hN₀η : 4 * (k₀ : ℝ) / η₀ ≤ (N₀ : ℝ) := by
    refine le_trans (Nat.le_ceil _) ?_
    have : (⌈4 * (k₀ : ℝ) / η₀⌉₊ : ℝ) ≤ (N₀ : ℝ) := by
      have : ⌈4 * (k₀ : ℝ) / η₀⌉₊ ≤ N₀ := by rw [hN₀def]; omega
      exact_mod_cast this
    exact this
  have hN₀ε : 2 * (1 + (k₀ : ℝ)) / ε ≤ (N₀ : ℝ) := by
    refine le_trans (Nat.le_ceil _) ?_
    have : ⌈2 * (1 + (k₀ : ℝ)) / ε⌉₊ ≤ N₀ := by rw [hN₀def]; omega
    exact_mod_cast this
  refine ⟨min γ₀ (1 / 2 ^ (N₀ + 1)), lt_min hγ₀ (by positivity),
    min (η₀ / 2) (1 / 4), lt_min (by positivity) (by norm_num), ?_⟩
  intro W _ _ H A w Exc hAH huni hw hload hlow hExc hcod
  set γ : ℝ := min γ₀ (1 / 2 ^ (N₀ + 1)) with hγdef
  set η : ℝ := min (η₀ / 2) (1 / 4) with hηdef
  have hγγ₀ : γ ≤ γ₀ := min_le_left _ _
  have hγpow : γ ≤ 1 / 2 ^ (N₀ + 1) := min_le_right _ _
  have hγpos : 0 < γ := lt_min hγ₀ (by positivity)
  have hηη₀ : η ≤ η₀ / 2 := min_le_left _ _
  have hη4 : η ≤ 1 / 4 := min_le_right _ _
  set u : ℝ := ∑ T ∈ H \ A, w T with hudef
  set a : ℝ := ∑ T ∈ A, w T with hadef
  have hu0 : 0 ≤ u := Finset.sum_nonneg (fun T _ => hw T)
  have ha0 : 0 ≤ a := Finset.sum_nonneg (fun T _ => hw T)
  have hsum : ∑ T ∈ H, w T = u + a := (Finset.sum_sdiff hAH).symm
  -- the degenerate case of an empty ground set
  rcases Nat.eq_zero_or_pos (Fintype.card W) with hW0 | hWpos
  · have hempty : IsEmpty W := Fintype.card_eq_zero_iff.1 hW0
    have hH : H = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun T hT => ?_
      have hT0 : T = ∅ := Finset.eq_empty_of_forall_notMem (fun x _ => hempty.false x)
      have := huni T hT
      rw [hT0] at this
      simp at this
      omega
    have hA0 : A = ∅ := Finset.subset_empty.1 (hH ▸ hAH)
    refine ⟨∅, ⟨by simp, by simp⟩, ?_, ?_⟩ <;>
      simp [hH, hA0, hW0]
  -- the main case
  · -- the ground set is large
    obtain ⟨v₀, hv₀⟩ : ∃ v : W, v ∉ Exc := by
      by_contra hcon
      push_neg at hcon
      have hsub : (Finset.univ : Finset W) ⊆ Exc := fun v _ => hcon v
      have h1 : ((Fintype.card W : ℕ) : ℝ) ≤ (Exc.card : ℝ) := by
        have := Finset.card_le_card hsub
        rw [Finset.card_univ] at this
        exact_mod_cast this
      have h2 : (0 : ℝ) < (Fintype.card W : ℝ) := by exact_mod_cast hWpos
      nlinarith only [hExc, hη4, h1, h2]
    have hbig : 1 - γ ≤ (2 : ℝ) ^ (Fintype.card W) * γ :=
      card_ge_of_codegree hr huni hw (le_of_lt hγpos) hcod hlow hv₀
    have hN₀W : N₀ ≤ Fintype.card W := by
      by_contra hcon
      push_neg at hcon
      have hpow2 : (2 : ℝ) ^ (Fintype.card W) * 2 ≤ 2 ^ N₀ := by
        have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
          (by omega : Fintype.card W + 1 ≤ N₀)
        rwa [pow_succ] at h
      have hposW : (0 : ℝ) < 2 ^ (Fintype.card W) := by positivity
      have hstep : (2 : ℝ) ^ (Fintype.card W) * γ ≤ 1 / 4 := by
        have h1 : (2 : ℝ) ^ (Fintype.card W) * γ
            ≤ 2 ^ (Fintype.card W) * (1 / 2 ^ (N₀ + 1)) :=
          mul_le_mul_of_nonneg_left hγpow (le_of_lt hposW)
        refine le_trans h1 ?_
        rw [pow_succ, mul_one_div, div_le_iff₀ (by positivity)]
        linarith
      have hhalf : γ ≤ 1 / 2 := by
        refine le_trans hγpow ?_
        have h2 : (2 : ℝ) ^ 1 ≤ 2 ^ (N₀ + 1) :=
          pow_le_pow_right₀ (by norm_num) (by omega)
        rw [pow_one] at h2
        exact one_div_le_one_div_of_le (by norm_num) h2
      linarith
    have hWR : (N₀ : ℝ) ≤ (Fintype.card W : ℝ) := by exact_mod_cast hN₀W
    have hmassW : (r : ℝ) * (u + a) ≤ (Fintype.card W : ℝ) := by
      rw [← hsum]; exact mass_le_card huni hload
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
    -- the pool loads are near-perfect unless the pool is of constant size
    have hpoolP : k₀ ≤ ⌈u⌉₊ → 1 - γ₀ ≤ u / (p : ℝ) := by
      intro hle
      have hpe : p = ⌈u⌉₊ := max_eq_left hle
      have hn : (1 : ℝ) / γ₀ ≤ (p : ℝ) := by
        refine le_trans hk₀ge ?_
        exact_mod_cast le_max_right ⌈u⌉₊ k₀
      have hnγ : 1 ≤ (p : ℝ) * γ₀ := by
        rw [div_le_iff₀ hγ₀] at hn; linarith
      have hun : (p : ℝ) - 1 ≤ u := by
        have h3 : (⌈u⌉₊ : ℝ) < u + 1 := Nat.ceil_lt_add_one hu0
        rw [hpe]; linarith
      rw [le_div_iff₀ hpR]
      nlinarith only [hnγ, hun]
    have hpoolQ : k₀ ≤ ⌈a⌉₊ → 1 - γ₀ ≤ a / (q : ℝ) := by
      intro hle
      have hqe : q = ⌈a⌉₊ := max_eq_left hle
      have hn : (1 : ℝ) / γ₀ ≤ (q : ℝ) := by
        refine le_trans hk₀ge ?_
        exact_mod_cast le_max_right ⌈a⌉₊ k₀
      have hnγ : 1 ≤ (q : ℝ) * γ₀ := by
        rw [div_le_iff₀ hγ₀] at hn; linarith
      have hun : (q : ℝ) - 1 ≤ a := by
        have h3 : (⌈a⌉₊ : ℝ) < a + 1 := Nat.ceil_lt_add_one ha0
        rw [hqe]; linarith
      rw [le_div_iff₀ hqR]
      nlinarith only [hnγ, hun]
    -- the extended instance
    set EP : Finset (Vtx W p q) :=
      if (1 : ℝ) - γ₀ ≤ u / (p : ℝ) then ∅
      else (Finset.univ : Finset (Fin p)).image (fun i => Sum.inr (Sum.inl i)) with hEPdef
    set EQ : Finset (Vtx W p q) :=
      if (1 : ℝ) - γ₀ ≤ a / (q : ℝ) then ∅
      else (Finset.univ : Finset (Fin q)).image (fun j => Sum.inr (Sum.inr j)) with hEQdef
    set Exc' : Finset (Vtx W p q) := (Exc.image Sum.inl ∪ EP) ∪ EQ with hExc'def
    have huni' : NibblePort.Hypergraph.IsUniform (bigH H A p q) (r + 1) := by
      intro S hS
      exact card_of_mem_bigH huni hAH hS
    have hnonneg' : ∀ S, 0 ≤ bigW w p q S := bigW_nonneg hw p q
    have hload' : ∀ v : Vtx W p q,
        ∑ S ∈ (bigH H A p q).filter (fun S => v ∈ S), bigW w p q S ≤ 1 := by
      rintro (v | (i | j))
      · rw [bigH_load_inl H A w p q hAH hp0.ne' hq0.ne' v]; exact hload v
      · rw [bigH_load_tokP H A w p q i, ← hudef]
        exact (div_le_one hpR).2 hup
      · rw [bigH_load_tokQ H A w p q j, ← hadef]
        exact (div_le_one hqR).2 haq
    have hlow' : ∀ v : Vtx W p q, v ∉ Exc' →
        1 - γ₀ ≤ ∑ S ∈ (bigH H A p q).filter (fun S => v ∈ S), bigW w p q S := by
      rintro (v | (i | j)) hv
      · rw [bigH_load_inl H A w p q hAH hp0.ne' hq0.ne' v]
        have hvE : v ∉ Exc := by
          intro hc
          exact hv (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_image.2 ⟨v, hc, rfl⟩)))
        have := hlow v hvE
        linarith
      · rw [bigH_load_tokP H A w p q i, ← hudef]
        by_contra hcon
        refine hv (Finset.mem_union_left _ (Finset.mem_union_right _ ?_))
        rw [hEPdef, if_neg hcon]
        exact Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩
      · rw [bigH_load_tokQ H A w p q j, ← hadef]
        by_contra hcon
        refine hv (Finset.mem_union_right _ ?_)
        rw [hEQdef, if_neg hcon]
        exact Finset.mem_image.2 ⟨j, Finset.mem_univ _, rfl⟩
    have hEPcard : (EP.card : ℝ) ≤ (k₀ : ℝ) := by
      rw [hEPdef]
      split_ifs with hif
      · simp
      · have hlt : ⌈u⌉₊ < k₀ := by
          by_contra hcon
          push_neg at hcon
          exact hif (hpoolP hcon)
        have hpe : p = k₀ := max_eq_right (le_of_lt hlt)
        have hcard : ((Finset.univ : Finset (Fin p)).image
            (fun i => (Sum.inr (Sum.inl i) : Vtx W p q))).card ≤ k₀ := by
          refine le_trans Finset.card_image_le ?_
          simp [hpe]
        exact_mod_cast hcard
    have hEQcard : (EQ.card : ℝ) ≤ (k₀ : ℝ) := by
      rw [hEQdef]
      split_ifs with hif
      · simp
      · have hlt : ⌈a⌉₊ < k₀ := by
          by_contra hcon
          push_neg at hcon
          exact hif (hpoolQ hcon)
        have hqe : q = k₀ := max_eq_right (le_of_lt hlt)
        have hcard : ((Finset.univ : Finset (Fin q)).image
            (fun j => (Sum.inr (Sum.inr j) : Vtx W p q))).card ≤ k₀ := by
          refine le_trans Finset.card_image_le ?_
          simp [hqe]
        exact_mod_cast hcard
    have hcardV : (Fintype.card W : ℝ) ≤ (Fintype.card (Vtx W p q) : ℝ) := by
      have : Fintype.card (Vtx W p q) = Fintype.card W + (p + q) := by
        simp [Vtx]
      rw [this]
      push_cast
      linarith
    have hExc' : (Exc'.card : ℝ) ≤ η₀ * (Fintype.card (Vtx W p q) : ℝ) := by
      have hcard1 : Exc'.card ≤ (Exc.image (Sum.inl : W → Vtx W p q)).card + EP.card + EQ.card := by
        refine le_trans (Finset.card_union_le _ _) ?_
        have := Finset.card_union_le (Exc.image (Sum.inl : W → Vtx W p q)) EP
        omega
      have hcard2 : ((Exc.image (Sum.inl : W → Vtx W p q)).card : ℝ) ≤ (Exc.card : ℝ) := by
        exact_mod_cast Finset.card_image_le
      have hcard3 : (Exc'.card : ℝ)
          ≤ (Exc.card : ℝ) + (k₀ : ℝ) + (k₀ : ℝ) := by
        have : (Exc'.card : ℝ)
            ≤ ((Exc.image (Sum.inl : W → Vtx W p q)).card : ℝ) + (EP.card : ℝ)
              + (EQ.card : ℝ) := by exact_mod_cast hcard1
        linarith
      have hk2 : 2 * (k₀ : ℝ) ≤ η₀ / 2 * (Fintype.card W : ℝ) := by
        have h1 : 4 * (k₀ : ℝ) / η₀ ≤ (Fintype.card W : ℝ) := le_trans hN₀η hWR
        rw [div_le_iff₀ hη₀] at h1
        linarith
      have hE : (Exc.card : ℝ) ≤ η₀ / 2 * (Fintype.card W : ℝ) := by
        refine le_trans hExc ?_
        have hWnn : (0 : ℝ) ≤ (Fintype.card W : ℝ) := by positivity
        exact mul_le_mul_of_nonneg_right hηη₀ hWnn
      have : (Exc'.card : ℝ) ≤ η₀ * (Fintype.card W : ℝ) := by linarith
      refine le_trans this ?_
      exact mul_le_mul_of_nonneg_left hcardV (le_of_lt hη₀)
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
      have hnum0 : 0 ≤ (∑ T ∈ (H \ A).filter (fun T => x ∈ T), w T) :=
        Finset.sum_nonneg (fun T _ => hw T)
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
        have hne : x ≠ z := fun hc => hxz (by rw [hc])
        exact le_trans (hcod x z hne) hγγ₀
      · exact hcodP x i'
      · exact hcodQ x j'
      · rw [hswap]; exact hcodP z i
      · rw [bigH_codeg_tok_tok H A w p q (Sum.inl i) (Sum.inl i')
          (fun hc => hxz (by rw [hc]))]
        exact le_of_lt hγ₀
      · rw [bigH_codeg_tok_tok H A w p q (Sum.inl i) (Sum.inr j')
          (by simp)]
        exact le_of_lt hγ₀
      · rw [hswap]; exact hcodQ z j
      · rw [bigH_codeg_tok_tok H A w p q (Sum.inr j) (Sum.inl i')
          (by simp)]
        exact le_of_lt hγ₀
      · rw [bigH_codeg_tok_tok H A w p q (Sum.inr j) (Sum.inr j')
          (fun hc => hxz (by rw [hc]))]
        exact le_of_lt hγ₀
    obtain ⟨Mstar, hMstar, -, hMmass⟩ :=
      hmain (W := Vtx W p q) (bigH H A p q) (bigW w p q) Exc'
        huni' hnonneg' hload' hlow' hExc' hcod'
    rw [bigH_mass H A w p q hp0.ne' hq0.ne', ← hudef, ← hadef] at hMmass
    -- projecting back
    have hprojInj : ∀ S₁ ∈ Mstar, ∀ S₂ ∈ Mstar, proj S₁ = proj S₂ → S₁ = S₂ := by
      intro S₁ h₁ S₂ h₂ heq
      by_contra hne
      have hdisj := hMstar.disjoint S₁ h₁ S₂ h₂ hne
      have hcard1 : (proj S₁).card = r := by
        have := card_of_mem_bigH huni hAH (hMstar.subset h₁)
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
      -- the unmarked tokens of the members of `Mbad` are disjoint and nonempty
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
    have htotalR : (1 - β) * (∑ T ∈ H, w T) - ε * (Fintype.card W : ℝ) ≤ (M.card : ℝ) := by
      rw [hsum, hMcardR]
      have h1 : (1 - β) * (u + a) ≤ (1 - β') * (u + a) :=
        mul_le_mul_of_nonneg_right (by linarith) (by linarith)
      have h2 : 0 ≤ ε * (Fintype.card W : ℝ) := by positivity
      linarith
    have hmarked : (1 - β) * a - ε * (Fintype.card W : ℝ)
        ≤ ((M.filter (fun T => T ∈ A)).card : ℝ) := by
      have hexp : (1 - β') * (u + a) = u + a - β' * (u + a) := by ring
      have hA4 : β' * (u + a) ≤ ε * (Fintype.card W : ℝ) / 2 := by
        have h1 : β' * (u + a) ≤ (ε * r / 2) * (u + a) :=
          mul_le_mul_of_nonneg_right hβ'ε (by linarith)
        have h2 : (ε * r / 2) * (u + a) = (ε / 2) * ((r : ℝ) * (u + a)) := by ring
        have h3 : (ε / 2) * ((r : ℝ) * (u + a)) ≤ (ε / 2) * (Fintype.card W : ℝ) :=
          mul_le_mul_of_nonneg_left hmassW (by positivity)
        linarith
      have hA5 : 1 + (k₀ : ℝ) ≤ ε * (Fintype.card W : ℝ) / 2 := by
        have h1 : 2 * (1 + (k₀ : ℝ)) / ε ≤ (Fintype.card W : ℝ) := le_trans hN₀ε hWR
        rw [div_le_iff₀ hε] at h1
        linarith
      have hβa : (1 - β) * a ≤ a := by nlinarith only [hβ, ha0]
      linarith [hmarkedR, hMmass, hple]
    exact ⟨M, hMmatch, htotalR, hmarked⟩

end PaperIV.MarkedQuotaGate

