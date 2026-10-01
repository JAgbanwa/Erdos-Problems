import PaperIV.LiftedPieceBudget

/-!
# E4, part A — choosing the lifted pieces greedily

Let `E` be a set of outside edges of the clique `A`.  A *lift choice* assigns to every
`e = xy ∈ E` a core pair `pick e ⊆ A`, adjacent to both `x` and `y`, such that

* distinct edges get distinct core pairs,
* edges sharing an exterior vertex get **disjoint** core pairs (so their links differ),
* every core vertex is used by at most `cap` lifts.

`GoodLifts` records these conditions; `liftOf pick e = pick e ∪ {x, y}` is the lifted
piece.  `liftOf_isItem` and `card_inter_liftOf_le_one` show that a lift choice is a
physical packing of `K₄`'s.

`exists_goodLifts` is the greedy construction.  Its hypothesis is explicit: for every
`xy ∈ E`, the common core neighbourhood of `x, y`, minus the `2(deg_E x + deg_E y)` core
vertices already linked to `x` or `y` and the at most `s` saturated core vertices, still
contains at least `|E|` core pairs, where `2|E| ≤ cap·(s+1)`.
-/

namespace PaperIV.LiftedPieces

open Finset PaperIV.FarRounding PaperIV.RootVocab

variable {V : Type*} [DecidableEq V] [Fintype V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {A : Finset V}

/-- The lifted piece attached to the outside edge `e` by the choice `pick`. -/
def liftOf (pick : Sym2 V → Finset V) (e : Sym2 V) : Finset V := pick e ∪ e.toFinset

/-- How many lifts of `E` use the core vertex `u`. -/
def usage (E : Finset (Sym2 V)) (pick : Sym2 V → Finset V) (u : V) : ℕ :=
  (E.filter fun e => u ∈ pick e).card

/-- The common core neighbourhood of `x` and `y`. -/
def commonCore (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) (x y : V) :
    Finset V :=
  A.filter fun u => G.Adj u x ∧ G.Adj u y

/-- The degree of `x` in the edge set `E`. -/
def edgeDeg (E : Finset (Sym2 V)) (x : V) : ℕ := (E.filter fun e => x ∈ e).card

/-- A lift choice for the outside edges `E` with usage cap `cap`. -/
def GoodLifts (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) (E : Finset (Sym2 V))
    (pick : Sym2 V → Finset V) (cap : ℕ) : Prop :=
  (∀ e ∈ E, pick e ⊆ A ∧ (pick e).card = 2 ∧ ∀ u ∈ pick e, ∀ w ∈ e, G.Adj u w) ∧
    (∀ e ∈ E, ∀ f ∈ E, e ≠ f → pick e ≠ pick f) ∧
    (∀ e ∈ E, ∀ f ∈ E, e ≠ f → ∀ w, w ∈ e → w ∈ f → Disjoint (pick e) (pick f)) ∧
    (∀ u, usage E pick u ≤ cap)

omit [Fintype V] in
/-- Two distinct two-element sets share at most one element. -/
theorem card_inter_le_one_of_ne {X Y : Finset V} (hX : X.card = 2) (hY : Y.card = 2)
    (hXY : X ≠ Y) : (X ∩ Y).card ≤ 1 := by
  by_contra h
  push_neg at h
  have h1 : X ∩ Y = X := eq_of_subset_of_card_le inter_subset_left (by omega)
  have h2 : X ∩ Y = Y := eq_of_subset_of_card_le inter_subset_right (by omega)
  exact hXY (h1.symm.trans h2)

omit [Fintype V] in
theorem toFinset_injective_sym2 {e f : Sym2 V} (h : e.toFinset = f.toFinset) : e = f :=
  Sym2.ext fun x => by rw [← Sym2.mem_toFinset, ← Sym2.mem_toFinset, h]

theorem mem_outsideEdges_iff {x y : V} :
    s(x, y) ∈ outsideEdges G A ↔ G.Adj x y ∧ x ∉ A ∧ y ∉ A := by
  simp [outsideEdges, Sym2.toFinset_mk_eq, Finset.insert_subset_iff]

/-- A lifted piece of a lift choice is a `K₄` of `G`, of type `(2,2)`. -/
theorem liftOf_isItem (hA : G.IsClique (A : Set V)) {E : Finset (Sym2 V)}
    (hE : E ⊆ outsideEdges G A) {pick : Sym2 V → Finset V} {cap : ℕ}
    (hP : GoodLifts G A E pick cap) {e : Sym2 V} (he : e ∈ E) :
    IsItem G (liftOf pick e) ∧ (liftOf pick e ∩ A).card = 2 ∧
      (liftOf pick e \ A).card = 2 := by
  obtain ⟨p, rfl⟩ := Quot.exists_rep e
  obtain ⟨x, y⟩ := p
  have hO := mem_outsideEdges_iff.1 (hE he)
  obtain ⟨hsub, hcard, hadj⟩ := hP.1 _ he
  obtain ⟨u, v, huv, hpick⟩ := Finset.card_eq_two.1 hcard
  have hu : u ∈ A := hsub (by simp [hpick])
  have hv : v ∈ A := hsub (by simp [hpick])
  have hux := hadj u (by simp [hpick]) x (Sym2.mem_mk_left x y)
  have huy := hadj u (by simp [hpick]) y (Sym2.mem_mk_right x y)
  have hvx := hadj v (by simp [hpick]) x (Sym2.mem_mk_left x y)
  have hvy := hadj v (by simp [hpick]) y (Sym2.mem_mk_right x y)
  have heq : liftOf pick (Quot.mk _ (x, y)) = liftedPiece u v x y := by
    show pick s(x, y) ∪ (s(x, y)).toFinset = _
    rw [hpick, Sym2.toFinset_mk_eq]
    ext w; simp [liftedPiece]; tauto
  rw [heq]
  exact ⟨(liftedPiece_isItem hA hu hv huv hO.2.1 hO.2.2 hO.1 hux huy hvx hvy).1,
    by rw [liftedPiece_inter_core hu hv hO.2.1 hO.2.2, card_pair huv],
    by rw [liftedPiece_sdiff_core hu hv hO.2.1 hO.2.2, card_pair (G.ne_of_adj hO.1)]⟩

/-- Distinct lifted pieces of a lift choice share at most one vertex. -/
theorem card_inter_liftOf_le_one {E : Finset (Sym2 V)} (hE : E ⊆ outsideEdges G A)
    {pick : Sym2 V → Finset V} {cap : ℕ} (hP : GoodLifts G A E pick cap)
    {e f : Sym2 V} (he : e ∈ E) (hf : f ∈ E) (hef : e ≠ f) :
    (liftOf pick e ∩ liftOf pick f).card ≤ 1 := by
  have hZ : ∀ g ∈ E, ∀ w ∈ g.toFinset, w ∉ A := by
    intro g hg w hw
    obtain ⟨p, rfl⟩ := Quot.exists_rep g
    obtain ⟨x, y⟩ := p
    have hO := mem_outsideEdges_iff.1 (hE hg)
    have : w = x ∨ w = y := by simpa [Sym2.toFinset_mk_eq] using hw
    rcases this with rfl | rfl
    · exact hO.2.1
    · exact hO.2.2
  have hsplit : liftOf pick e ∩ liftOf pick f ⊆
      (pick e ∩ pick f) ∪ (e.toFinset ∩ f.toFinset) := by
    intro w hw
    simp only [liftOf, mem_inter, mem_union] at hw ⊢
    obtain ⟨h1 | h1, h2 | h2⟩ := hw
    · exact Or.inl ⟨h1, h2⟩
    · exact absurd ((hP.1 e he).1 h1) (hZ f hf w h2)
    · exact absurd ((hP.1 f hf).1 h2) (hZ e he w h1)
    · exact Or.inr ⟨h1, h2⟩
  have hnd : ∀ g ∈ E, g.toFinset.card = 2 := by
    intro g hg
    obtain ⟨p, rfl⟩ := Quot.exists_rep g
    obtain ⟨x, y⟩ := p
    have hO := mem_outsideEdges_iff.1 (hE hg)
    exact Sym2.card_toFinset_of_not_isDiag _ (by simpa using G.ne_of_adj hO.1)
  refine le_trans (card_le_card hsplit) (le_trans (card_union_le _ _) ?_)
  by_cases hshare : ∃ w, w ∈ e ∧ w ∈ f
  · obtain ⟨w, hwe, hwf⟩ := hshare
    have hd := hP.2.2.1 e he f hf hef w hwe hwf
    rw [disjoint_iff_inter_eq_empty.1 hd, card_empty, zero_add]
    exact card_inter_le_one_of_ne (hnd e he) (hnd f hf)
      (fun h => hef (toFinset_injective_sym2 h))
  · push_neg at hshare
    have : e.toFinset ∩ f.toFinset = ∅ := by
      ext w
      simp only [mem_inter, Sym2.mem_toFinset, notMem_empty, iff_false, not_and]
      exact hshare w
    rw [this, card_empty, add_zero]
    exact card_inter_le_one_of_ne (hP.1 e he).2.1 (hP.1 f hf).2.1 (hP.2.1 e he f hf hef)

/-- Double counting: the usages add up to `2|E|`. -/
theorem sum_usage {E : Finset (Sym2 V)} {pick : Sym2 V → Finset V}
    (h2 : ∀ e ∈ E, (pick e).card = 2) :
    ∑ u, usage E pick u = 2 * E.card := by
  calc ∑ u, usage E pick u = ∑ u, ∑ e ∈ E, (if u ∈ pick e then 1 else 0) := by
        exact sum_congr rfl fun u _ => card_filter _ _
    _ = ∑ e ∈ E, ∑ u, (if u ∈ pick e then 1 else 0) := sum_comm
    _ = ∑ e ∈ E, 2 := sum_congr rfl fun e he => by
        rw [← h2 e he, ← card_filter, filter_mem_eq_inter, univ_inter]
    _ = 2 * E.card := by rw [sum_const, smul_eq_mul, mul_comm]

/-- **The greedy choice of lifted pieces.** -/
theorem exists_goodLifts (E : Finset (Sym2 V)) (hE : E ⊆ outsideEdges G A) (cap s : ℕ)
    (hcap : 2 * E.card ≤ cap * (s + 1))
    (hroom : ∀ x y, s(x, y) ∈ E →
      E.card ≤ ((commonCore G A x y).card - 2 * (edgeDeg E x + edgeDeg E y) - s).choose 2) :
    ∃ pick, GoodLifts G A E pick cap := by
  suffices H : ∀ E' ⊆ E, ∃ pick, GoodLifts G A E' pick cap from H E subset_rfl
  intro E'
  induction E' using Finset.induction_on with
  | empty =>
    intro _
    refine ⟨fun _ => ∅, by simp, by simp, by simp, fun u => by simp [usage]⟩
  | @insert e E' he ih =>
  intro hsub
  obtain ⟨pick, hP1, hP2, hP3, hP4⟩ := ih ((subset_insert e E').trans hsub)
  obtain ⟨p, rfl⟩ := Quot.exists_rep e
  obtain ⟨x, y⟩ := p
  replace he : s(x, y) ∉ E' := he
  replace hsub : insert s(x, y) E' ⊆ E := hsub
  have heE : s(x, y) ∈ E := hsub (mem_insert_self _ _)
  have hO := mem_outsideEdges_iff.1 (hE heE)
  have hE'E : E' ⊆ E := (subset_insert _ E').trans hsub
  have hcardlt : E'.card < E.card := by
    have := card_le_card hsub
    rw [card_insert_of_notMem he] at this
    omega
  -- blocked and saturated core vertices
  set Bl := (E'.filter fun f => x ∈ f ∨ y ∈ f).biUnion pick with hBl
  set Sat := A.filter fun u => cap ≤ usage E' pick u with hSat
  set Free := (commonCore G A x y \ Bl) \ Sat with hFree
  have hBlc : Bl.card ≤ 2 * (edgeDeg E x + edgeDeg E y) := by
    calc Bl.card ≤ ∑ f ∈ E'.filter (fun f => x ∈ f ∨ y ∈ f), (pick f).card := card_biUnion_le
      _ = ∑ f ∈ E'.filter (fun f => x ∈ f ∨ y ∈ f), 2 :=
          sum_congr rfl fun f hf => (hP1 f (mem_filter.1 hf).1).2.1
      _ = 2 * (E'.filter fun f => x ∈ f ∨ y ∈ f).card := by rw [sum_const, smul_eq_mul, mul_comm]
      _ ≤ 2 * (edgeDeg E x + edgeDeg E y) := by
          apply Nat.mul_le_mul_left
          rw [filter_or]
          refine le_trans (card_union_le _ _) (add_le_add ?_ ?_) <;>
            exact card_le_card (filter_subset_filter _ hE'E)
  have hSatc : Sat.card ≤ s := by
    by_contra hlt
    push_neg at hlt
    have h1 : cap * Sat.card ≤ ∑ u ∈ Sat, usage E' pick u := by
      rw [mul_comm, ← smul_eq_mul, ← sum_const]
      exact sum_le_sum fun u hu => (mem_filter.1 hu).2
    have h2 : ∑ u ∈ Sat, usage E' pick u ≤ ∑ u, usage E' pick u :=
      sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => Nat.zero_le _)
    have h3 := sum_usage (E := E') (pick := pick) (fun f hf => (hP1 f hf).2.1)
    have h4 : cap * (s + 1) ≤ cap * Sat.card := Nat.mul_le_mul_left _ hlt
    omega
  have hFreec : (commonCore G A x y).card - 2 * (edgeDeg E x + edgeDeg E y) - s ≤
      Free.card := by
    have h1 : (commonCore G A x y).card - Bl.card ≤ (commonCore G A x y \ Bl).card :=
      le_card_sdiff Bl (commonCore G A x y)
    have h2 : (commonCore G A x y \ Bl).card - Sat.card ≤ Free.card :=
      le_card_sdiff Sat (commonCore G A x y \ Bl)
    omega
  -- a fresh core pair
  have hfresh : (E'.image pick).card < (Free.powersetCard 2).card := by
    rw [card_powersetCard]
    have h1 := hroom x y heE
    have h2 : ((commonCore G A x y).card - 2 * (edgeDeg E x + edgeDeg E y) - s).choose 2 ≤
        Free.card.choose 2 := Nat.choose_le_choose 2 hFreec
    have h3 : (E'.image pick).card ≤ E'.card := card_image_le
    omega
  obtain ⟨S, hS, hSnot⟩ := exists_mem_notMem_of_card_lt_card hfresh
  obtain ⟨hSsub, hScard⟩ := mem_powersetCard.1 hS
  have hSfree : ∀ u ∈ S, u ∈ A ∧ G.Adj u x ∧ G.Adj u y ∧ u ∉ Bl ∧ u ∉ Sat := by
    intro u hu
    have := hSsub hu
    simp only [hFree, commonCore, mem_sdiff, mem_filter] at this
    exact ⟨this.1.1.1, this.1.1.2.1, this.1.1.2.2, this.1.2, this.2⟩
  have hne : ∀ f ∈ E', f ≠ s(x, y) := fun f hf h => he (by rw [← h]; exact hf)
  refine ⟨fun f => if f = s(x, y) then S else pick f, ?_, ?_, ?_, ?_⟩
  · intro f hf
    rcases mem_insert.1 hf with rfl | hf
    · simp only [if_true]
      refine ⟨fun u hu => (hSfree u hu).1, hScard, fun u hu w hw => ?_⟩
      rcases Sym2.mem_iff.1 hw with rfl | rfl
      · exact (hSfree u hu).2.1
      · exact (hSfree u hu).2.2.1
    · simp only [hne f hf, if_false]
      exact hP1 f hf
  · intro f hf g hg hfg
    rcases mem_insert.1 hf with rfl | hf <;> rcases mem_insert.1 hg with rfl | hg
    · exact absurd rfl hfg
    · simp only [if_true, hne g hg, if_false]
      exact fun h => hSnot (mem_image.2 ⟨g, hg, h.symm⟩)
    · simp only [if_true, hne f hf, if_false]
      exact fun h => hSnot (mem_image.2 ⟨f, hf, h⟩)
    · simp only [hne f hf, hne g hg, if_false]
      exact hP2 f hf g hg hfg
  · have hkey : ∀ g ∈ E', ∀ w, w ∈ s(x, y) → w ∈ g → Disjoint S (pick g) := by
      intro g hg w hw hwg
      rw [Finset.disjoint_left]
      intro u huS hug
      apply (hSfree u huS).2.2.2.1
      refine mem_biUnion.2 ⟨g, mem_filter.2 ⟨hg, ?_⟩, hug⟩
      rcases Sym2.mem_iff.1 hw with rfl | rfl
      · exact Or.inl hwg
      · exact Or.inr hwg
    intro f hf g hg hfg w hwf hwg
    rcases mem_insert.1 hf with rfl | hf <;> rcases mem_insert.1 hg with rfl | hg
    · exact absurd rfl hfg
    · simp only [if_true, hne g hg, if_false]
      exact hkey g hg w hwf hwg
    · simp only [if_true, hne f hf, if_false]
      exact (hkey f hf w hwg hwf).symm
    · simp only [hne f hf, hne g hg, if_false]
      exact hP3 f hf g hg hfg w hwf hwg
  · intro u
    have hsplit : ((insert s(x, y) E').filter fun f =>
        u ∈ (if f = s(x, y) then S else pick f)) =
        (if u ∈ S then insert s(x, y) (E'.filter fun f => u ∈ pick f)
          else E'.filter fun f => u ∈ pick f) := by
      ext f
      by_cases hf : f = s(x, y)
      · subst hf
        by_cases huS : u ∈ S <;> simp [huS, he]
      · by_cases huS : u ∈ S <;> simp [hf, huS]
    unfold usage
    rw [hsplit]
    by_cases huS : u ∈ S
    · simp only [huS, if_true]
      rw [card_insert_of_notMem (fun h => he (mem_filter.1 h).1)]
      have hu := hSfree u huS
      have : ¬ cap ≤ usage E' pick u := fun h => hu.2.2.2.2 (mem_filter.2 ⟨hu.1, h⟩)
      unfold usage at this
      omega
    · simp only [huS, if_false]
      exact hP4 u

end PaperIV.LiftedPieces
