import Mathlib

/-!
# E34 — sampling with repetition versus sampling a uniform `m`-set

All probabilities are written as counts.  A *sample with repetition* is a sequence
`w : Fin m → Fin n` (all `n^m` of them equally likely); its vertex set is `img w`.

**Transfer lemma** (`transfer`).  For an upward-closed property `B` of vertex sets and
`m ≤ n`,
`#{w | B (img w)} · C(n, m) ≤ n^m · #{U : |U| = m, B U}`,
i.e. `P_seq(B) ≤ P_{m-set}(B)`.  Proof: the number of `w` with `img w = A` depends only on
`|A|` (it is the number of surjections `Fin m → Fin |A|`), and for `j ≤ m` the proportion of
`j`-sets satisfying `B` is at most the proportion of `m`-sets satisfying `B` (double counting
of pairs `A ⊆ U`).

Sequences are convenient because independence is automatic: a sequence of length `a + b`
is a pair of sequences (`card_append`).
-/

namespace E34

open Finset

open scoped Classical

variable {n : ℕ}

/-- The vertex set of a sample with repetition. -/
def img {m : ℕ} (w : Fin m → Fin n) : Finset (Fin n) := univ.image w

theorem mem_img {m : ℕ} (w : Fin m → Fin n) (v : Fin n) : v ∈ img w ↔ ∃ i, w i = v := by
  simp [img]

theorem card_img_le {m : ℕ} (w : Fin m → Fin n) : (img w).card ≤ m := by
  unfold img; exact card_image_le.trans (by simp)

/-- Number of surjections `Fin m → Fin j`. -/
noncomputable def surjCount (m j : ℕ) : ℕ :=
  (univ.filter (fun f : Fin m → Fin j => Function.Surjective f)).card

theorem surjCount_eq_zero {m j : ℕ} (h : m < j) : surjCount m j = 0 := by
  unfold surjCount
  rw [card_eq_zero, filter_eq_empty_iff]
  intro f _ hf
  have := Fintype.card_le_of_surjective f hf
  simp at this; omega

/-- The number of sequences with a given vertex set `A` depends only on `|A|`. -/
theorem card_img_eq (A : Finset (Fin n)) (m : ℕ) :
    (univ.filter (fun w : Fin m → Fin n => img w = A)).card = surjCount m A.card := by
  unfold surjCount
  set e := A.orderEmbOfFin rfl
  symm
  refine card_bij (fun f _ => fun i => e (f i)) ?_ ?_ ?_
  · intro f hf
    simp only [mem_filter, mem_univ, true_and] at hf ⊢
    ext v
    rw [mem_img]
    constructor
    · rintro ⟨i, rfl⟩
      have : e (f i) ∈ Set.range e := ⟨_, rfl⟩
      rw [Finset.range_orderEmbOfFin] at this
      exact this
    · intro hv
      have : v ∈ Set.range e := by rw [Finset.range_orderEmbOfFin]; exact hv
      obtain ⟨k, rfl⟩ := this
      obtain ⟨i, rfl⟩ := hf k
      exact ⟨i, rfl⟩
  · intro f _ g _ h
    funext i
    exact e.injective (congrFun h i)
  · intro w hw
    simp only [mem_filter, mem_univ, true_and] at hw
    have hmem : ∀ i, w i ∈ Set.range e := by
      intro i; rw [Finset.range_orderEmbOfFin, ← hw, mem_coe, mem_img]; exact ⟨i, rfl⟩
    choose f hf using hmem
    refine ⟨f, ?_, funext hf⟩
    simp only [mem_filter, mem_univ, true_and]
    intro k
    have : e k ∈ img w := by
      rw [hw]
      have : e k ∈ Set.range e := ⟨k, rfl⟩
      rw [Finset.range_orderEmbOfFin] at this; exact this
    obtain ⟨i, hi⟩ := (mem_img w _).1 this
    exact ⟨i, e.injective ((hf i).trans hi)⟩

/-- Exact number of `m`-supersets of a `j`-set. -/
theorem card_supersets_eq (A : Finset (Fin n)) (m : ℕ) (hAm : A.card ≤ m) :
    ((powersetCard m univ).filter (fun U => A ⊆ U)).card = (n - A.card).choose (m - A.card) := by
  have heq : (powersetCard m univ).filter (fun U => A ⊆ U) =
      (powersetCard (m - A.card) (univ \ A)).image (fun W => W ∪ A) := by
    ext U
    simp only [mem_filter, mem_powersetCard, subset_univ, true_and, mem_image]
    constructor
    · rintro ⟨hUc, hAU⟩
      refine ⟨U \ A, ⟨sdiff_subset_sdiff (subset_univ _) (Finset.Subset.refl _), ?_⟩,
        sdiff_union_of_subset hAU⟩
      rw [card_sdiff_of_subset hAU, hUc]
    · rintro ⟨W, ⟨hW, hWc⟩, rfl⟩
      refine ⟨?_, subset_union_right⟩
      have hd : Disjoint W A := by
        rw [disjoint_left]; intro x hx hxA; exact (mem_sdiff.1 (hW hx)).2 hxA
      rw [card_union_of_disjoint hd, hWc]; omega
  rw [heq, card_image_of_injOn, card_powersetCard, card_sdiff_of_subset (subset_univ _),
    card_univ, Fintype.card_fin]
  intro W hW W' hW' h
  rw [mem_coe, mem_powersetCard] at hW hW'
  have h1 : Disjoint W A := by
    rw [disjoint_left]; intro x hx hxA; exact (mem_sdiff.1 (hW.1 hx)).2 hxA
  have h2 : Disjoint W' A := by
    rw [disjoint_left]; intro x hx hxA; exact (mem_sdiff.1 (hW'.1 hx)).2 hxA
  simp only at h
  rw [← union_sdiff_cancel_right h1, ← union_sdiff_cancel_right h2, h]

/-- The `j`-sets with property `B`. -/
noncomputable def levelSets (B : Finset (Fin n) → Prop) (j : ℕ) : Finset (Finset (Fin n)) :=
  (powersetCard j univ).filter B

/-- **Monotonicity of the proportion** for upward-closed `B`. -/
theorem levelSets_mono (B : Finset (Fin n) → Prop) (hB : ∀ A A', A ⊆ A' → B A → B A')
    {j m : ℕ} (hjm : j ≤ m) (hmn : m ≤ n) :
    (levelSets B j).card * n.choose m ≤ (levelSets B m).card * n.choose j := by
  have hdc : (levelSets B j).card * (n - j).choose (m - j) ≤
      (levelSets B m).card * m.choose j := by
    refine card_mul_le_card_mul (fun A U => A ⊆ U) ?_ ?_
    · intro A hA
      simp only [levelSets, mem_filter, mem_powersetCard] at hA
      rw [← hA.1.2, ← card_supersets_eq A m (by omega)]
      refine card_le_card ?_
      intro U hU
      simp only [mem_filter, mem_powersetCard] at hU
      simp only [bipartiteAbove, levelSets, mem_filter, mem_powersetCard]
      exact ⟨⟨hU.1, hB _ _ hU.2 hA.2⟩, hU.2⟩
    · intro U hU
      simp only [levelSets, mem_filter, mem_powersetCard] at hU
      rw [← hU.1.2, ← card_powersetCard]
      refine card_le_card ?_
      intro A hA
      simp only [bipartiteBelow, levelSets, mem_filter, mem_powersetCard] at hA
      rw [mem_powersetCard]
      exact ⟨hA.2, hA.1.1.2⟩
  have hid := Nat.choose_mul (n := n) (k := m) (s := j) hjm
  have hpos : 0 < m.choose j := Nat.choose_pos hjm
  have : (levelSets B j).card * n.choose m * m.choose j ≤
      (levelSets B m).card * n.choose j * m.choose j := by
    calc (levelSets B j).card * n.choose m * m.choose j
        = (levelSets B j).card * (n - j).choose (m - j) * n.choose j := by
          rw [mul_assoc, hid]; ring
      _ ≤ (levelSets B m).card * m.choose j * n.choose j := Nat.mul_le_mul_right _ hdc
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_right this hpos

/-- Grouping a sum over vertex sets by cardinality. -/
theorem sum_by_card (B : Finset (Fin n) → Prop) (f : ℕ → ℕ) :
    ∑ A ∈ univ.filter B, f A.card = ∑ j ∈ range (n + 1), f j * (levelSets B j).card := by
  rw [← sum_fiberwise_of_maps_to (g := fun A : Finset (Fin n) => A.card) (t := range (n + 1))]
  · refine sum_congr rfl (fun j _ => ?_)
    rw [sum_congr rfl (g := fun _ => f j), sum_const, smul_eq_mul, mul_comm]
    · congr 1
      unfold levelSets
      congr 1
      ext A
      simp [and_comm]
    · intro A hA
      rw [(mem_filter.1 hA).2]
  · intro A _
    rw [mem_range]
    have := card_le_univ A
    simp at this; omega

/-- Counting sequences through their vertex sets. -/
theorem card_seq_eq_sum (B : Finset (Fin n) → Prop) (m : ℕ) :
    (univ.filter (fun w : Fin m → Fin n => B (img w))).card =
      ∑ A ∈ univ.filter B, surjCount m A.card := by
  rw [card_eq_sum_card_fiberwise (f := img) (t := univ.filter B)]
  · refine sum_congr rfl (fun A hA => ?_)
    rw [← card_img_eq A m]
    congr 1
    ext w
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · exact fun h => h.2
    · intro h; exact ⟨h ▸ (mem_filter.1 hA).2, h⟩
  · intro w hw
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hw ⊢
    exact hw

/-- **Transfer lemma**: `P_seq(B) ≤ P_{m-set}(B)` for upward-closed `B`. -/
theorem transfer (B : Finset (Fin n) → Prop) (hB : ∀ A A', A ⊆ A' → B A → B A')
    {m : ℕ} (hmn : m ≤ n) :
    (univ.filter (fun w : Fin m → Fin n => B (img w))).card * n.choose m ≤
      n ^ m * (levelSets B m).card := by
  have htot : n ^ m = ∑ j ∈ range (n + 1), surjCount m j * n.choose j := by
    have h1 := card_seq_eq_sum (n := n) (fun _ => True) m
    simp only [filter_true, card_univ, Fintype.card_fun, Fintype.card_fin] at h1
    have h2 := sum_by_card (n := n) (fun _ => True) (surjCount m)
    simp only [filter_true] at h2
    rw [h1, h2]
    refine sum_congr rfl (fun j hj => ?_)
    congr 1
    unfold levelSets
    rw [filter_true, card_powersetCard, card_univ, Fintype.card_fin]
  rw [card_seq_eq_sum, sum_by_card, sum_mul, htot, sum_mul]
  refine sum_le_sum (fun j hj => ?_)
  by_cases hjm : j ≤ m
  · have := levelSets_mono B hB hjm hmn
    calc surjCount m j * (levelSets B j).card * n.choose m
        = surjCount m j * ((levelSets B j).card * n.choose m) := by ring
      _ ≤ surjCount m j * ((levelSets B m).card * n.choose j) := Nat.mul_le_mul_left _ this
      _ = _ := by ring
  · rw [surjCount_eq_zero (by omega)]; simp

/-- Vertex set of a concatenation. -/
theorem img_append {a b : ℕ} (u : Fin a → Fin n) (v : Fin b → Fin n) :
    img (Fin.append u v) = img u ∪ img v := by
  ext x
  simp only [mem_img, mem_union]
  constructor
  · rintro ⟨i, hi⟩
    refine Fin.addCases (fun i hi => Or.inl ⟨i, ?_⟩) (fun i hi => Or.inr ⟨i, ?_⟩) i hi
    · rwa [Fin.append_left] at hi
    · rwa [Fin.append_right] at hi
  · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact ⟨Fin.castAdd b i, Fin.append_left u v i⟩
    · exact ⟨Fin.natAdd a i, Fin.append_right u v i⟩

/-- **Independence**: a sample of length `a + b` is a pair of samples. -/
theorem card_append (a b : ℕ) (P : (Fin a → Fin n) → (Fin b → Fin n) → Prop) :
    (univ.filter (fun w : Fin (a + b) → Fin n =>
      P (fun i => w (Fin.castAdd b i)) (fun i => w (Fin.natAdd a i)))).card =
    (univ.filter (fun p : (Fin a → Fin n) × (Fin b → Fin n) => P p.1 p.2)).card := by
  symm
  refine card_bij (fun p _ => Fin.append p.1 p.2) ?_ ?_ ?_
  · intro p hp
    simp only [mem_filter, mem_univ, true_and] at hp ⊢
    simpa [Fin.append_left, Fin.append_right] using hp
  · intro p _ q _ h
    have h1 := (Fin.appendEquiv a b).injective h
    exact h1
  · intro w hw
    refine ⟨((fun i => w (Fin.castAdd b i)), (fun i => w (Fin.natAdd a i))), ?_, ?_⟩
    · simpa using hw
    · exact Fin.append_castAdd_natAdd

/-- Counting over pairs: if for every first coordinate at most `c` second coordinates satisfy
`P`, the number of pairs is at most `N · c`. -/
theorem card_pairs_le {α β : Type*} [Fintype α] [Fintype β] (P : α → β → Prop) (c : ℕ)
    (h : ∀ a, (univ.filter (fun b => P a b)).card ≤ c) :
    (univ.filter (fun p : α × β => P p.1 p.2)).card ≤ Fintype.card α * c := by
  have e : (univ.filter (fun p : α × β => P p.1 p.2)).card =
      ∑ a, (univ.filter (fun b => P a b)).card := by
    rw [card_filter, Fintype.sum_prod_type]
    exact sum_congr rfl (fun a _ => (card_filter _ _).symm)
  rw [e]
  calc ∑ a, (univ.filter (fun b => P a b)).card ≤ ∑ _a : α, c := sum_le_sum (fun a _ => h a)
    _ = _ := by simp

theorem card_filter_prod_eq_sum_left {α β : Type*} [Fintype α] [Fintype β] (P : α → β → Prop)
    [DecidablePred (fun p : α × β => P p.1 p.2)] [∀ a, DecidablePred (P a)] :
    (univ.filter (fun p : α × β => P p.1 p.2)).card = ∑ a, (univ.filter (fun b => P a b)).card := by
  rw [card_filter, Fintype.sum_prod_type]
  exact sum_congr rfl (fun a _ => (card_filter _ _).symm)

theorem card_filter_prod_eq_sum_right {α β : Type*} [Fintype α] [Fintype β] (P : α → β → Prop)
    [DecidablePred (fun p : α × β => P p.1 p.2)] [∀ b, DecidablePred (fun a => P a b)] :
    (univ.filter (fun p : α × β => P p.1 p.2)).card = ∑ b, (univ.filter (fun a => P a b)).card := by
  rw [card_filter, Fintype.sum_prod_type_right]
  exact sum_congr rfl (fun a _ => (card_filter _ _).symm)

end E34
