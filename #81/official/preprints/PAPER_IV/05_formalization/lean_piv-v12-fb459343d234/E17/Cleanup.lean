import PaperIV.FarRounding
import Mathlib.Tactic.IntervalCases

/-!
# E17 Part B: far-branch cleanup of a fractional mixed packing

We work with the tree's fractional mixed packings `PaperIV.FarRounding.FracPacking G ℚ`
(weights on the items of `G` — real triangles and `K₄`'s — with edge loads at most one) and their
value `w(x) = 2 Σ x_T + 5 Σ x_Q` (`FracPacking.value`, gain `C(|K|,2) - 1`).

Every cleanup step is a **transfer**: a nonnegative matrix `a K T` supported on `T ⊆ K`, with
`Σ_{T ∋ e} a K T ≤ 1` for every edge `e` of `K`; the new packing is `y_T = Σ_K x_K a K T`.

* B3 `resources` — for every nonempty edge set `F`, `Σ_{T ⊇ F} y_T ≤ Σ_{K ⊇ F} x_K`; in
  particular `y` is again a fractional packing (`Transfer.apply`).
* B1 `r3_loss` — the R3 cleanup against forbidden edges `B`:
  `V - w(y) ≤ Σ_{e ∈ B} (2 l3_e + 3 l4_e) ≤ 3|B|`, and `r3_tight` (tightness on `K₄`).
* B2 `f1_faces`, `f1_value`, `f1_optimal` — the `F1` conversion of a `K₄` into its faces.
* B4 `profile_loss` — profile accounting.
* B5 `restrict_loss` — restricting to `K \ U`: loss `≤ |B_U|`.
* B6 `cleanup_loss`, `selector_closure`, `c4_le_of_closure`.
-/

namespace E17.Cleanup

open Finset PaperIV.FarRounding

section Transfer

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

variable (G) in
/-- A transfer matrix from items to items: `a K T ≥ 0`, supported on `T ⊆ K`, with total
weight at most one on every edge of `K`. -/
structure Transfer where
  a : Finset V → Finset V → ℚ
  nonneg : ∀ K T, 0 ≤ a K T
  sub : ∀ K ∈ items G, ∀ T ∈ items G, a K T ≠ 0 → T ⊆ K
  row : ∀ K ∈ items G, ∀ e ∈ pairs K,
    ∑ T ∈ items G, (if e ∈ pairs T then a K T else 0) ≤ 1

omit [Fintype V] in
theorem pairs_mono {K T : Finset V} (h : T ⊆ K) : pairs T ⊆ pairs K := by
  intro e he
  rw [mem_pairs] at he ⊢
  exact ⟨fun a ha => h (he.1 a ha), he.2⟩

/-- **B3 (resources), row form.** -/
theorem Transfer.row_le (τ : Transfer G) {K : Finset V} (hK : K ∈ items G)
    (F : Finset (Sym2 V)) (hF : F.Nonempty) :
    ∑ T ∈ items G, (if F ⊆ pairs T then τ.a K T else 0) ≤ if F ⊆ pairs K then 1 else 0 := by
  split_ifs with hFK
  · obtain ⟨e, he⟩ := hF
    refine le_trans (sum_le_sum fun T _ => ?_) (τ.row K hK e (hFK he))
    split_ifs with h1 h2
    · exact le_rfl
    · exact absurd (h1 he) h2
    · exact τ.nonneg K T
    · exact le_rfl
  · refine le_of_eq (sum_eq_zero fun T hT => ?_)
    split_ifs with h1
    · by_contra hne
      exact hFK (h1.trans (pairs_mono (τ.sub K hK T hT hne)))
    · rfl

/-- The transferred packing `y_T = Σ_K x_K a K T`. -/
def Transfer.weight (τ : Transfer G) (x : FracPacking G ℚ) (T : Finset V) : ℚ :=
  ∑ K ∈ items G, x.weight K * τ.a K T

/-- **B3 (resources).** Loads and codegrees do not increase: for every nonempty edge set `F`,
`Σ_{T ⊇ F} y_T ≤ Σ_{K ⊇ F} x_K`. -/
theorem resources (τ : Transfer G) (x : FracPacking G ℚ) (F : Finset (Sym2 V))
    (hF : F.Nonempty) :
    ∑ T ∈ items G, (if F ⊆ pairs T then τ.weight x T else 0) ≤
      ∑ K ∈ items G, (if F ⊆ pairs K then x.weight K else 0) := by
  unfold Transfer.weight
  calc ∑ T ∈ items G, (if F ⊆ pairs T then ∑ K ∈ items G, x.weight K * τ.a K T else 0)
      = ∑ T ∈ items G, ∑ K ∈ items G, x.weight K * (if F ⊆ pairs T then τ.a K T else 0) := by
        refine sum_congr rfl fun T _ => ?_
        split_ifs <;> simp
    _ = ∑ K ∈ items G, x.weight K * ∑ T ∈ items G, (if F ⊆ pairs T then τ.a K T else 0) := by
        rw [sum_comm]; simp only [mul_sum]
    _ ≤ ∑ K ∈ items G, x.weight K * (if F ⊆ pairs K then 1 else 0) :=
        sum_le_sum fun K hK => mul_le_mul_of_nonneg_left (τ.row_le hK F hF) (x.weight_nonneg K)
    _ = ∑ K ∈ items G, (if F ⊆ pairs K then x.weight K else 0) := by
        simp only [mul_ite, mul_one, mul_zero]


/-- The transferred fractional packing (B3 gives its capacity constraints). -/
def Transfer.apply (τ : Transfer G) (x : FracPacking G ℚ) : FracPacking G ℚ where
  weight := τ.weight x
  weight_nonneg T := sum_nonneg fun K _ => mul_nonneg (x.weight_nonneg K) (τ.nonneg K T)
  capacity e he := by
    have h := resources τ x {e} (singleton_nonempty e)
    simp only [singleton_subset_iff] at h
    exact h.trans (x.capacity e he)

/-- Total load through any unordered pair is at most one (zero off the edges of `G`). -/
theorem load_le_one (x : FracPacking G ℚ) (e : Sym2 V) :
    ∑ K ∈ items G, (if e ∈ pairs K then x.weight K else 0) ≤ 1 := by
  by_cases he : e ∈ G.edgeFinset
  · exact x.capacity e he
  · rw [sum_eq_zero fun K hK => if_neg fun h => he (pairs_subset_edgeFinset (mem_items.1 hK) h)]
    norm_num

theorem Transfer.value_apply (τ : Transfer G) (x : FracPacking G ℚ) :
    (τ.apply x).value =
      ∑ K ∈ items G, x.weight K * ∑ T ∈ items G, gainF ℚ T * τ.a K T := by
  unfold FracPacking.value Transfer.apply Transfer.weight
  simp only [mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring

/-- The value lost by a transfer, copy by copy. -/
theorem Transfer.loss_eq (τ : Transfer G) (x : FracPacking G ℚ) :
    x.value - (τ.apply x).value =
      ∑ K ∈ items G, x.weight K * (gainF ℚ K - ∑ T ∈ items G, gainF ℚ T * τ.a K T) := by
  rw [τ.value_apply, FracPacking.value, ← sum_sub_distrib]
  exact sum_congr rfl fun _ _ => by ring

/-- Double counting of damaged edges against loads. -/
theorem sum_mul_card_inter (x : FracPacking G ℚ) (c : Finset V → ℚ) (B : Finset (Sym2 V)) :
    ∑ K ∈ items G, x.weight K * (c K * ((pairs K ∩ B).card : ℚ)) =
      ∑ e ∈ B, ∑ K ∈ items G, (if e ∈ pairs K then c K * x.weight K else 0) := by
  have hc : ∀ K : Finset V, ((pairs K ∩ B).card : ℚ) = ∑ e ∈ B, if e ∈ pairs K then 1 else 0 := by
    intro K
    rw [sum_boole, inter_comm, ← filter_mem_eq_inter]
  simp only [hc, mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by split_ifs <;> ring

/-- A deterministic transfer: each copy `K` is replaced by the single set `t K ⊆ K`
(dropped when `t K` is not an item). -/
def ofTarget (t : Finset V → Finset V) (ht : ∀ K, t K ⊆ K) : Transfer G where
  a K T := if T = t K then 1 else 0
  nonneg K T := by split_ifs <;> norm_num
  sub K _ T _ h := by
    split_ifs at h with hT
    · rw [hT]; exact ht K
    · exact absurd rfl h
  row K _ e _ := by
    refine le_trans (sum_le_sum fun T _ => (?_ : (if e ∈ pairs T then
      (if T = t K then (1 : ℚ) else 0) else 0) ≤ if T = t K then 1 else 0)) ?_
    · split_ifs <;> norm_num
    · rw [sum_ite_eq']; split_ifs <;> norm_num

theorem ofTarget_rowGain (t : Finset V → Finset V) (ht : ∀ K, t K ⊆ K) (K : Finset V) :
    ∑ T ∈ items G, gainF ℚ T * (ofTarget (G := G) t ht).a K T =
      if t K ∈ items G then gainF ℚ (t K) else 0 := by
  simp only [ofTarget, mul_ite, mul_one, mul_zero]
  rw [sum_ite_eq']

theorem gainF_of_item {K : Finset V} (hK : K ∈ items G) :
    gainF ℚ K = if K.card = 4 then 5 else 2 := by
  rcases (mem_items.1 hK).2 with h | h <;> simp [gainF, h, Nat.choose] <;> norm_num

theorem gainF_nonneg_of_item {K : Finset V} (hK : K ∈ items G) : 0 ≤ gainF ℚ K := by
  rw [gainF_of_item hK]; split_ifs <;> norm_num

theorem mem_items_of_subset {K T : Finset V} (hK : K ∈ items G) (hT : T ⊆ K)
    (h3 : T.card = 3) : T ∈ items G := by
  have := mem_items.1 hK
  exact mem_items.2 ⟨fun a ha b hb hab => this.1 a (hT ha) b (hT hb) hab, Or.inl h3⟩

theorem ofTarget_support {t : Finset V → Finset V} {ht : ∀ K, t K ⊆ K} {x : FracPacking G ℚ}
    {T : Finset V} (h : ((ofTarget (G := G) t ht).apply x).weight T ≠ 0) :
    ∃ K ∈ items G, T = t K := by
  obtain ⟨K, hK, hne⟩ := exists_ne_zero_of_sum_ne_zero h
  refine ⟨K, hK, ?_⟩
  by_contra hT
  simp [ofTarget, hT] at hne

/-! ### B1: the R3 cleanup against a set `B` of forbidden edges -/

open Classical in
/-- R3: keep intact copies; replace a damaged `K₄` by a triangle of `K₄ - B` when one exists;
drop everything else (target `∅`). -/
noncomputable def r3Target (B : Finset (Sym2 V)) (K : Finset V) : Finset V :=
  if Disjoint (pairs K) B then K
  else if h : K.card = 4 ∧ ∃ T, T ⊆ K ∧ T.card = 3 ∧ Disjoint (pairs T) B then
    Classical.choose h.2
  else ∅

omit [Fintype V] in
theorem r3Target_spec (B : Finset (Sym2 V)) (K : Finset V) :
    r3Target B K ⊆ K ∧ Disjoint (pairs (r3Target B K)) B := by
  unfold r3Target
  split_ifs with h1 h2
  · exact ⟨subset_rfl, h1⟩
  · have := Classical.choose_spec h2.2
    exact ⟨this.1, this.2.2⟩
  · refine ⟨empty_subset _, ?_⟩
    have : pairs (∅ : Finset V) = ∅ := by simp [pairs]
    rw [this]; exact disjoint_empty_left _

/-- The R3 transfer. -/
noncomputable def r3 (B : Finset (Sym2 V)) : Transfer G :=
  ofTarget (r3Target B) fun K => (r3Target_spec B K).1

/-- The loss coefficient of a copy: `2` for a triangle, `3` for a `K₄`. -/
def coef (K : Finset V) : ℚ := if K.card = 4 then 3 else 2

omit [Fintype V] in
/-- The key finite fact behind R3: if at most one edge of a `K₄` is forbidden, some triangle
of the `K₄` avoids all forbidden edges. -/
theorem exists_triangle_of_card_le_one {K : Finset V} {B : Finset (Sym2 V)} (hK : K.card = 4)
    (hB : (pairs K ∩ B).card ≤ 1) : ∃ T, T ⊆ K ∧ T.card = 3 ∧ Disjoint (pairs T) B := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hB with h0 | h1
  · obtain ⟨a, ha⟩ : K.Nonempty := card_pos.1 (by omega)
    refine ⟨K.erase a, erase_subset _ _, by rw [card_erase_of_mem ha, hK], ?_⟩
    rw [card_eq_zero, ← disjoint_iff_inter_eq_empty] at h0
    exact h0.mono_left (pairs_mono (erase_subset _ _))
  · obtain ⟨e, he⟩ := card_eq_one.1 h1
    have heK : e ∈ pairs K := (mem_inter.1 (he ▸ mem_singleton_self e)).1
    induction e using Sym2.ind with
    | _ a b =>
    have ha : a ∈ K := (mk_mem_pairs.1 heK).1
    refine ⟨K.erase a, erase_subset _ _, by rw [card_erase_of_mem ha, hK], ?_⟩
    rw [disjoint_left]
    intro f hfT hfB
    have hfK : f ∈ pairs K ∩ B := mem_inter.2 ⟨pairs_mono (erase_subset _ _) hfT, hfB⟩
    rw [he, mem_singleton] at hfK
    subst hfK
    have := (mk_mem_pairs.1 hfT).1
    simp at this

/-- Per-copy R3 loss: `gain(K) - gain(r3(K)) ≤ coef(K) · |E(K) ∩ B|`. -/
theorem r3_copy_loss (B : Finset (Sym2 V)) {K : Finset V} (hK : K ∈ items G) :
    gainF ℚ K - (if r3Target B K ∈ items G then gainF ℚ (r3Target B K) else 0) ≤
      coef K * ((pairs K ∩ B).card : ℚ) := by
  have hcoef : 0 ≤ coef K := by unfold coef; split_ifs <;> norm_num
  have hcard := (mem_items.1 hK).2
  by_cases hd : Disjoint (pairs K) B
  · have : r3Target B K = K := by simp [r3Target, hd]
    rw [this, if_pos hK, sub_self]
    positivity
  have h1 : (1 : ℚ) ≤ (pairs K ∩ B).card := by
    have : (pairs K ∩ B).Nonempty := not_disjoint_iff_nonempty_inter.1 hd
    exact_mod_cast card_pos.2 this
  by_cases h : K.card = 4 ∧ ∃ T, T ⊆ K ∧ T.card = 3 ∧ Disjoint (pairs T) B
  · have hT : r3Target B K = Classical.choose h.2 := by
      unfold r3Target; rw [if_neg hd, dif_pos h]
    have hspec := Classical.choose_spec h.2
    have hTi : r3Target B K ∈ items G := by
      rw [hT]; exact mem_items_of_subset hK hspec.1 hspec.2.1
    rw [if_pos hTi, gainF_of_item hTi, gainF_of_item hK, hT, hspec.2.1, if_pos h.1, coef,
      if_pos h.1, if_neg (by norm_num : (3 : ℕ) ≠ 4)]
    linarith
  · have hT : r3Target B K = ∅ := by
      unfold r3Target; rw [if_neg hd, dif_neg h]
    have hnot : (∅ : Finset V) ∉ items G := fun h' => by
      rcases (mem_items.1 h').2 with h' | h' <;> simp at h'
    rw [hT, if_neg hnot, sub_zero, gainF_of_item hK, coef]
    by_cases h4 : K.card = 4
    · rw [if_pos h4, if_pos h4]
      have h2n : 2 ≤ (pairs K ∩ B).card := by
        by_contra hlt
        exact h ⟨h4, exists_triangle_of_card_le_one h4 (by omega)⟩
      have h2 : (2 : ℚ) ≤ (pairs K ∩ B).card := by exact_mod_cast h2n
      linarith
    · rw [if_neg h4, if_neg h4]; linarith


/-- The load of `x` on `e` coming from copies of order `r` (`l3_e`, `l4_e`). -/
def loadCard (x : FracPacking G ℚ) (r : ℕ) (e : Sym2 V) : ℚ :=
  ∑ K ∈ items G, if e ∈ pairs K ∧ K.card = r then x.weight K else 0

theorem coef_load_eq (x : FracPacking G ℚ) (e : Sym2 V) :
    ∑ K ∈ items G, (if e ∈ pairs K then coef K * x.weight K else 0) =
      2 * loadCard x 3 e + 3 * loadCard x 4 e := by
  unfold loadCard
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun K hK => ?_
  rcases (mem_items.1 hK).2 with h | h <;> by_cases he : e ∈ pairs K <;> simp [coef, h, he]

theorem two_load_add_three_load_le (x : FracPacking G ℚ) (e : Sym2 V) :
    2 * loadCard x 3 e + 3 * loadCard x 4 e ≤ 3 := by
  have h := load_le_one x e
  unfold loadCard
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  refine le_trans (sum_le_sum fun K hK => (?_ : _ ≤ 3 * if e ∈ pairs K then x.weight K else 0)) ?_
  · have := x.weight_nonneg K
    by_cases he : e ∈ pairs K <;> by_cases h3 : K.card = 3 <;> by_cases h4 : K.card = 4 <;>
      simp [he, h3, h4] <;> first | omega | linarith
  · rw [← mul_sum]; linarith

/-- **B1 (R3).** After the R3 cleanup against the forbidden edges `B`,
`V - w(y) ≤ Σ_{e ∈ B} (2 l3_e + 3 l4_e) ≤ 3|B|`. -/
theorem r3_loss (x : FracPacking G ℚ) (B : Finset (Sym2 V)) :
    x.value - ((r3 (G := G) B).apply x).value ≤
        ∑ e ∈ B, (2 * loadCard x 3 e + 3 * loadCard x 4 e) ∧
      ∑ e ∈ B, (2 * loadCard x 3 e + 3 * loadCard x 4 e) ≤ 3 * B.card := by
  refine ⟨?_, ?_⟩
  · rw [Transfer.loss_eq]
    calc ∑ K ∈ items G, x.weight K *
          (gainF ℚ K - ∑ T ∈ items G, gainF ℚ T * (r3 (G := G) B).a K T)
        ≤ ∑ K ∈ items G, x.weight K * (coef K * ((pairs K ∩ B).card : ℚ)) := by
          refine sum_le_sum fun K hK => mul_le_mul_of_nonneg_left ?_ (x.weight_nonneg K)
          have := ofTarget_rowGain (G := G) (r3Target B) (fun K => (r3Target_spec B K).1) K
          rw [show (r3 (G := G) B) = ofTarget (r3Target B) (fun K => (r3Target_spec B K).1)
            from rfl, this]
          exact r3_copy_loss B hK
      _ = ∑ e ∈ B, (2 * loadCard x 3 e + 3 * loadCard x 4 e) := by
          rw [sum_mul_card_inter]
          exact sum_congr rfl fun e _ => coef_load_eq x e
  · calc ∑ e ∈ B, (2 * loadCard x 3 e + 3 * loadCard x 4 e) ≤ ∑ _e ∈ B, (3 : ℚ) :=
          sum_le_sum fun e _ => two_load_add_three_load_le x e
      _ = 3 * B.card := by rw [sum_const, nsmul_eq_mul]; ring

/-- The R3 packing avoids the forbidden edges: every copy carrying positive weight has no edge
in `B`. -/
theorem r3_avoids (x : FracPacking G ℚ) (B : Finset (Sym2 V)) {T : Finset V}
    (hT : ((r3 (G := G) B).apply x).weight T ≠ 0) : Disjoint (pairs T) B := by
  obtain ⟨K, _, rfl⟩ := ofTarget_support hT
  exact (r3Target_spec B K).2


/-! ### B5: exceptional vertices -/

/-- The edges of `G` incident to the exceptional set `U`. -/
def edgesMeeting (U : Finset V) : Finset (Sym2 V) :=
  G.edgeFinset.filter fun e => ∃ u ∈ U, u ∈ e

/-- Restriction of every copy to `K \ U`. -/
def restrictU (U : Finset V) : Transfer G := ofTarget (fun K => K \ U) fun _ => sdiff_subset

theorem restrict_copy_loss (U : Finset V) {K : Finset V} (hK : K ∈ items G) :
    gainF ℚ K - (if K \ U ∈ items G then gainF ℚ (K \ U) else 0) ≤
      ((pairs K ∩ edgesMeeting (G := G) U).card : ℚ) := by
  have hsub : pairs (K \ U) ⊆ pairs K := pairs_mono sdiff_subset
  have hsd : pairs K \ pairs (K \ U) ⊆ pairs K ∩ edgesMeeting (G := G) U := by
    intro f hf
    rw [mem_sdiff] at hf
    refine mem_inter.2 ⟨hf.1, mem_filter.2 ⟨pairs_subset_edgeFinset (mem_items.1 hK) hf.1, ?_⟩⟩
    have h1 := mem_pairs.1 hf.1
    by_contra hno
    push_neg at hno
    exact hf.2 (mem_pairs.2 ⟨fun a ha => mem_sdiff.2 ⟨h1.1 a ha, fun hU => hno a hU ha⟩, h1.2⟩)
  have hc := card_le_card hsd
  rw [card_sdiff_of_subset hsub, card_pairs, card_pairs] at hc
  have hk := (mem_items.1 hK).2
  have hk' : (K \ U).card ≤ K.card := card_le_card sdiff_subset
  have hmono : (K \ U).card.choose 2 ≤ K.card.choose 2 := Nat.choose_le_choose 2 hk'
  have hc' : ((K.card.choose 2 : ℕ) : ℚ) - ((K \ U).card.choose 2 : ℕ) ≤
      ((pairs K ∩ edgesMeeting (G := G) U).card : ℚ) := by
    rw [← Nat.cast_sub hmono]; exact_mod_cast hc
  have hg : ((K \ U).card.choose 2 : ℚ) - 1 ≤
      (if K \ U ∈ items G then gainF ℚ (K \ U) else 0) := by
    split_ifs with hi
    · rw [gainF]
    · have : (K \ U).card ≤ 2 := by
        by_contra hlt
        apply hi
        refine mem_items.2 ⟨fun a ha b hb hab =>
          (mem_items.1 hK).1 a (sdiff_subset ha) b (sdiff_subset hb) hab, ?_⟩
        omega
      interval_cases h : (K \ U).card <;> simp [Nat.choose]
  rw [gainF]
  linarith

/-- **B5.** Restricting every copy to `K \ U` loses at most `|B_U|`, the number of edges incident
to `U`. -/
theorem restrict_loss (x : FracPacking G ℚ) (U : Finset V) :
    x.value - ((restrictU (G := G) U).apply x).value ≤ (edgesMeeting (G := G) U).card := by
  rw [Transfer.loss_eq]
  calc ∑ K ∈ items G, x.weight K *
        (gainF ℚ K - ∑ T ∈ items G, gainF ℚ T * (restrictU (G := G) U).a K T)
      ≤ ∑ K ∈ items G, x.weight K *
          ((fun _ => (1 : ℚ)) K * ((pairs K ∩ edgesMeeting (G := G) U).card : ℚ)) := by
        refine sum_le_sum fun K hK => mul_le_mul_of_nonneg_left ?_ (x.weight_nonneg K)
        rw [show (restrictU (G := G) U) = ofTarget (fun K => K \ U) (fun K => sdiff_subset)
          from rfl, ofTarget_rowGain, one_mul]
        exact restrict_copy_loss U hK
    _ = ∑ e ∈ edgesMeeting (G := G) U,
          ∑ K ∈ items G, (if e ∈ pairs K then 1 * x.weight K else 0) := sum_mul_card_inter _ _ _
    _ ≤ ∑ _e ∈ edgesMeeting (G := G) U, (1 : ℚ) :=
        sum_le_sum fun e _ => by simp only [one_mul]; exact load_le_one x e
    _ = (edgesMeeting (G := G) U).card := by rw [sum_const, nsmul_eq_mul, mul_one]

theorem restrict_avoids (x : FracPacking G ℚ) (U : Finset V) {T : Finset V}
    (hT : ((restrictU (G := G) U).apply x).weight T ≠ 0) : Disjoint T U := by
  obtain ⟨K, _, rfl⟩ := ofTarget_support hT
  exact sdiff_disjoint

/-! ### B6: total cleanup -/

/-- The combined cleanup: first restrict to `V \ U`, then R3 against `B`. -/
noncomputable def cleanup (U : Finset V) (B : Finset (Sym2 V)) (x : FracPacking G ℚ) : FracPacking G ℚ :=
  (r3 B).apply ((restrictU U).apply x)

/-- **B6 (copy part).** `V - w(y) ≤ |B_U| + 3|B|` for the combined cleanup. -/
theorem cleanup_loss (x : FracPacking G ℚ) (U : Finset V) (B : Finset (Sym2 V)) :
    x.value - (cleanup U B x).value ≤ (edgesMeeting (G := G) U).card + 3 * B.card := by
  have h1 := restrict_loss x U
  have h2 := r3_loss ((restrictU (G := G) U).apply x) B
  unfold cleanup
  linarith [h2.1, h2.2]

/-- The cleaned packing avoids `U` and `B`. -/
theorem cleanup_avoids (x : FracPacking G ℚ) (U : Finset V) (B : Finset (Sym2 V))
    {T : Finset V} (hT : (cleanup U B x).weight T ≠ 0) : Disjoint T U ∧ Disjoint (pairs T) B := by
  refine ⟨?_, r3_avoids _ B hT⟩
  obtain ⟨K', hK', hne⟩ := exists_ne_zero_of_sum_ne_zero hT
  have hx : ((restrictU (G := G) U).apply x).weight K' ≠ 0 := by
    intro h0; apply hne
    show ((restrictU (G := G) U).apply x).weight K' * _ = 0
    rw [h0, zero_mul]
  have hsub : T ⊆ K' := by
    by_contra hT'
    apply hne
    show _ * (if T = r3Target B K' then (1 : ℚ) else 0) = 0
    rw [if_neg fun h => hT' (by rw [h]; exact (r3Target_spec B K').1), mul_zero]
  exact (restrict_avoids x U hx).mono_left hsub


/-- **B6 (total cleanup).** If the profile stage (B4) costs at most `N4 θ4 + 2 N3 θ3` from the
cleaned packing, the whole cleanup costs at most `|B_U| + 3|B| + N4 θ4 + 2 N3 θ3`. -/
theorem total_cleanup (x : FracPacking G ℚ) (U : Finset V) (B : Finset (Sym2 V)) (wy : ℚ)
    (N4 N3 : ℕ) (θ4 θ3 : ℚ) (hprof : (cleanup U B x).value - wy ≤ N4 * θ4 + 2 * N3 * θ3) :
    x.value - wy ≤ (edgesMeeting (G := G) U).card + 3 * B.card + N4 * θ4 + 2 * N3 * θ3 := by
  have := cleanup_loss x U B
  linarith

/-- **B6 (selector closure).** A selector contract `g(P) ≥ (1-α) w(y) - E_sel` gives
`V - g(P) ≤ α V + (1-α)(V - w(y)) + E_sel`. -/
theorem selector_closure (Vx wy g α Esel : ℚ) (hsel : (1 - α) * wy - Esel ≤ g) :
    Vx - g ≤ α * Vx + (1 - α) * (Vx - wy) + Esel := by
  have : α * Vx + (1 - α) * (Vx - wy) = Vx - (1 - α) * wy := by ring
  linarith

/-- **B6 (closure to `c₄`).** If a physical packing `P` satisfies the selector contract and
`α V + (1-α)(V - w(y)) + E_sel < M(n) - e(G) + V + 1`, then `c₄(G) ≤ M(n)`. -/
theorem c4_le_of_closure (P : Packing G) (Vx wy α Esel : ℚ)
    (hsel : (1 - α) * wy - Esel ≤ P.gain)
    (hclose : α * Vx + (1 - α) * (Vx - wy) + Esel <
      (targetSize (Fintype.card V) : ℚ) - G.edgeFinset.card + Vx + 1) :
    ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size ≤ targetSize (Fintype.card V) := by
  obtain ⟨Q, hQ4, hQ⟩ := exists_cliquePartition_of_packing P
  refine ⟨Q, hQ4, ?_⟩
  have h1 := selector_closure Vx wy P.gain α Esel hsel
  have hQ' : (Q.size : ℚ) + P.gain = G.edgeFinset.card := by exact_mod_cast hQ
  have : (Q.size : ℚ) < targetSize (Fintype.card V) + 1 := by linarith
  have : Q.size < targetSize (Fintype.card V) + 1 := by exact_mod_cast this
  omega

/-! ### B1 tightness and B2 (F1) on a single `K₄` -/

/-- **B1 tightness.** In the unit `K₄` on `Fin 4` with the edge `01` excluded, every fractional
triangle packing (only the load of the edge `23` matters) has gain at most `2`; so the R3 loss
`5 - 2 = 3 = 3|B|` cannot be improved by any triangle-only replacement. -/
theorem r3_tight (y : Finset (Fin 4) → ℚ)
    (hload : ∑ T ∈ (univ.powersetCard 3).filter (fun T => s(0, 1) ∉ pairs T),
      (if s(2, 3) ∈ pairs T then y T else 0) ≤ 1) :
    ∑ T ∈ (univ.powersetCard 3).filter (fun T => s(0, 1) ∉ pairs T), 2 * y T ≤ 2 := by
  have hall : ∀ T ∈ (univ.powersetCard 3 : Finset (Finset (Fin 4))).filter
      (fun T => s(0, 1) ∉ pairs T), s(2, 3) ∈ pairs T := by decide +kernel
  rw [sum_congr rfl fun T hT => if_pos (hall T hT)] at hload
  rw [← mul_sum]; linarith

omit [Fintype V] in
/-- **B2 (F1), loads.** Replacing a `K₄` of mass `λ` by its four faces `K \ {c}` with mass `λ/2`
leaves every edge load unchanged. -/
theorem f1_loads {K : Finset V} (hK : K.card = 4) (lam : ℚ) {e : Sym2 V} (he : e ∈ pairs K) :
    ∑ c ∈ K, (if e ∈ pairs (K.erase c) then lam / 2 else 0) = lam := by
  induction e using Sym2.ind with
  | _ a b =>
  obtain ⟨ha, hb, hab⟩ := mk_mem_pairs.1 he
  have hiff : ∀ c ∈ K, s(a, b) ∈ pairs (K.erase c) ↔ c ∈ (K.erase a).erase b := by
    intro c hc
    rw [mk_mem_pairs]
    simp only [mem_erase]
    constructor
    · rintro ⟨⟨h1, _⟩, ⟨h2, _⟩, _⟩; exact ⟨fun h => h2 h.symm, fun h => h1 h.symm, hc⟩
    · rintro ⟨h1, h2, _⟩; exact ⟨⟨fun h => h2 h.symm, ha⟩, ⟨fun h => h1 h.symm, hb⟩, hab⟩
  rw [sum_congr rfl fun c hc => by rw [if_congr (hiff c hc) rfl rfl], sum_ite_mem,
    inter_eq_right.2 ((erase_subset _ _).trans (erase_subset _ _)), sum_const,
    card_erase_of_mem (mem_erase.2 ⟨Ne.symm hab, hb⟩), card_erase_of_mem ha, hK, nsmul_eq_mul]
  norm_num; ring

omit [Fintype V] in
/-- **B2 (F1), gain.** The four faces with mass `λ/2` have gain `4λ` (versus `5λ`). -/
theorem f1_value {K : Finset V} (hK : K.card = 4) (lam : ℚ) :
    ∑ c ∈ K, gainF ℚ (K.erase c) * (lam / 2) = 4 * lam := by
  rw [sum_congr rfl fun c hc => by
    rw [gainF, card_erase_of_mem hc, hK]]
  rw [sum_const, hK]; simp [Nat.choose]; ring

omit [Fintype V] in
/-- **B2 (F1), optimality.** Any triangle-only replacement inside a `K₄` with all loads `≤ λ`
has gain at most `4λ`. -/
theorem f1_optimal {K : Finset V} (hK : K.card = 4) (lam : ℚ) (y : Finset V → ℚ)
    (hload : ∀ e ∈ pairs K, ∑ T ∈ K.powersetCard 3, (if e ∈ pairs T then y T else 0) ≤ lam) :
    ∑ T ∈ K.powersetCard 3, 2 * y T ≤ 4 * lam := by
  have hsum : ∑ e ∈ pairs K, ∑ T ∈ K.powersetCard 3, (if e ∈ pairs T then y T else 0) =
      3 * ∑ T ∈ K.powersetCard 3, y T := by
    rw [sum_comm, mul_sum]
    refine sum_congr rfl fun T hT => ?_
    obtain ⟨hTK, hT3⟩ := mem_powersetCard.1 hT
    rw [← sum_filter, sum_const, nsmul_eq_mul, filter_mem_eq_inter,
      inter_eq_right.2 (pairs_mono hTK), card_pairs, hT3]
    norm_num
  have hle : ∑ e ∈ pairs K, ∑ T ∈ K.powersetCard 3, (if e ∈ pairs T then y T else 0) ≤
      ∑ _e ∈ pairs K, lam := sum_le_sum hload
  rw [sum_const, card_pairs, hK, nsmul_eq_mul] at hle
  rw [← mul_sum]
  norm_num [Nat.choose] at hle
  linarith


/-! ### B4: profile accounting -/

/-- **B4 (profiles).** `K₄` profiles `P4` with masses `q`, triangle profiles `P3` with masses `r`,
and for each `K₄` profile its four face profiles `face a i ∈ P3`.  Small `K₄` profiles
(`q < θ4`) are converted by F1 (mass `q/2` to each face, aggregated into `r'`), then triangle
profiles with aggregated mass `r' < θ3` are dropped.  The value lost is exactly
`μ4 + 2 μ3`, and `μ4 + 2 μ3 ≤ N4 θ4 + 2 N3 θ3`. -/
theorem profile_loss {α β : Type*} [DecidableEq β] (P4 : Finset α) (P3 : Finset β)
    (q : α → ℚ) (r : β → ℚ) (face : α → Fin 4 → β) (hface : ∀ a ∈ P4, ∀ i, face a i ∈ P3)
    (θ4 θ3 : ℚ) (hθ4 : 0 ≤ θ4) (hθ3 : 0 ≤ θ3) :
    let S4 := P4.filter fun a => q a < θ4
    let r' : β → ℚ := fun b => r b + ∑ a ∈ S4, ∑ i, (if face a i = b then q a / 2 else 0)
    let S3 := P3.filter fun b => r' b < θ3
    let μ4 := ∑ a ∈ S4, q a
    let μ3 := ∑ b ∈ S3, r' b
    (5 * ∑ a ∈ P4, q a + 2 * ∑ b ∈ P3, r b) -
        (5 * ∑ a ∈ P4.filter (fun a => ¬ q a < θ4), q a +
          2 * ∑ b ∈ P3.filter (fun b => ¬ r' b < θ3), r' b) = μ4 + 2 * μ3 ∧
      μ4 + 2 * μ3 ≤ P4.card * θ4 + 2 * (P3.card * θ3) := by
  intro S4 r' S3 μ4 μ3
  have hagg : ∑ b ∈ P3, r' b = ∑ b ∈ P3, r b + 2 * μ4 := by
    simp only [r', sum_add_distrib]
    congr 1
    rw [sum_comm, mul_sum]
    refine sum_congr rfl fun a ha => ?_
    rw [sum_comm]
    have ha' : a ∈ P4 := (mem_filter.1 ha).1
    rw [sum_congr rfl fun i _ => (by rw [sum_ite_eq, if_pos (hface a ha' i)] :
      ∑ b ∈ P3, (if face a i = b then q a / 2 else 0) = q a / 2)]
    rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  have h4 := sum_filter_add_sum_filter_not P4 (fun a => q a < θ4) q
  have h3 := sum_filter_add_sum_filter_not P3 (fun b => r' b < θ3) r'
  refine ⟨?_, ?_⟩
  · simp only [μ4, μ3, S4, S3] at hagg ⊢
    linarith
  · have hμ4 : μ4 ≤ P4.card * θ4 := by
      calc μ4 ≤ ∑ _a ∈ S4, θ4 := sum_le_sum fun a ha => (mem_filter.1 ha).2.le
        _ = S4.card * θ4 := by rw [sum_const, nsmul_eq_mul]
        _ ≤ P4.card * θ4 := mul_le_mul_of_nonneg_right
            (by exact_mod_cast card_le_card (filter_subset _ _)) hθ4
    have hμ3 : μ3 ≤ P3.card * θ3 := by
      calc μ3 ≤ ∑ _b ∈ S3, θ3 := sum_le_sum fun b hb => (mem_filter.1 hb).2.le
        _ = S3.card * θ3 := by rw [sum_const, nsmul_eq_mul]
        _ ≤ P3.card * θ3 := mul_le_mul_of_nonneg_right
            (by exact_mod_cast card_le_card (filter_subset _ _)) hθ3
    linarith

end Transfer
end E17.Cleanup
