import E34.Theorem2

/-!
# E34 — Theorems 5 and 6 of arXiv:1902.06135: `M₂`-free bipartite graphs

For disjoint `L, R ⊆ Fin n`:
* `HasM2 G L R X` — `G[L ∩ X, R ∩ X]` contains an induced matching of size two.
* `chainMisOn G L R A rk` — number of pairs `(l, r) ∈ (L ∩ A) × (R ∩ A)` on which `G`
  disagrees with the chain graph `l ~ r ↔ rk r < rk l` (Theorem 5(iii)).
* `hasM2_of_noPeelable` — Theorem 5, (i) ⇒ (ii).
* `peel` — the peeling procedure of Theorem 6: either a non-empty core without `c`-peelable
  vertices, or a chain graph with at most `c·|A|` mismatches.
* `thm6` — Theorem 6 (counting form, sampling with repetition): if every chain graph has more
  than `ε n²` mismatches with `G[L, R]`, at most `(m+1)(1-ε)^(m-1) n^m` sequences of length `m`
  induce an `M₂`-free bipartite graph.
-/

namespace E34

open Finset

open scoped Classical

variable {n : ℕ}

/-- `G[L ∩ X, R ∩ X]` contains an induced `M₂`. -/
def HasM2 (G : SimpleGraph (Fin n)) (L R X : Finset (Fin n)) : Prop :=
  ∃ l1 ∈ L ∩ X, ∃ l2 ∈ L ∩ X, ∃ r1 ∈ R ∩ X, ∃ r2 ∈ R ∩ X,
    G.Adj l1 r1 ∧ G.Adj l2 r2 ∧ ¬ G.Adj l1 r2 ∧ ¬ G.Adj l2 r1

theorem HasM2.mono {G : SimpleGraph (Fin n)} {L R X Y : Finset (Fin n)} (h : HasM2 G L R X)
    (hXY : X ⊆ Y) : HasM2 G L R Y := by
  obtain ⟨l1, h1, l2, h2, r1, h3, r2, h4, e⟩ := h
  exact ⟨l1, inter_subset_inter_left hXY h1, l2, inter_subset_inter_left hXY h2,
    r1, inter_subset_inter_left hXY h3, r2, inter_subset_inter_left hXY h4, e⟩

/-- Mismatches with the chain graph of rank `rk`, inside `A`. -/
noncomputable def chainMisOn (G : SimpleGraph (Fin n)) (L R A : Finset (Fin n))
    (rk : Fin n → ℕ) : ℕ :=
  (((L ∩ A) ×ˢ (R ∩ A)).filter (fun p => ¬ (G.Adj p.1 p.2 ↔ rk p.2 < rk p.1))).card

/-- `v` is not `c`-peelable in `G[L ∩ C, R ∩ C]`. -/
def NonPeel (G : SimpleGraph (Fin n)) (L R C : Finset (Fin n)) (c : ℝ) (v : Fin n) : Prop :=
  (v ∈ L ∧ c < (((R ∩ C).filter (fun r => G.Adj v r)).card : ℝ)) ∨
    (v ∈ R ∧ c < (((L ∩ C).filter (fun l => ¬ G.Adj l v)).card : ℝ))

/-- **Theorem 5, (i) ⇒ (ii).** If no vertex of `L₀ ∪ R₀ ≠ ∅` is peelable, there is an `M₂`. -/
theorem hasM2_of_noPeelable (G : SimpleGraph (Fin n)) (L R X : Finset (Fin n))
    (hne : ((L ∪ R) ∩ X).Nonempty)
    (hL : ∀ l ∈ L ∩ X, ∃ r ∈ R ∩ X, G.Adj l r)
    (hR : ∀ r ∈ R ∩ X, ∃ l ∈ L ∩ X, ¬ G.Adj l r) : HasM2 G L R X := by
  have hLne : (L ∩ X).Nonempty := by
    obtain ⟨v, hv⟩ := hne
    rw [mem_inter, mem_union] at hv
    rcases hv.1 with h | h
    · exact ⟨v, mem_inter.2 ⟨h, hv.2⟩⟩
    · obtain ⟨l, hl, -⟩ := hR v (mem_inter.2 ⟨h, hv.2⟩); exact ⟨l, hl⟩
  obtain ⟨l1, hl1, hmin⟩ := exists_min_image (L ∩ X)
    (fun l => ((R ∩ X).filter (fun r => G.Adj l r)).card) hLne
  obtain ⟨r1, hr1, hadj1⟩ := hL l1 hl1
  obtain ⟨l2, hl2, hnadj⟩ := hR r1 hr1
  have hle := hmin l2 hl2
  have : ¬ ((R ∩ X).filter (fun r => G.Adj l2 r) ⊆ (R ∩ X).filter (fun r => G.Adj l1 r)) := by
    intro hsub
    have hlt : ((R ∩ X).filter (fun r => G.Adj l2 r)).card <
        ((R ∩ X).filter (fun r => G.Adj l1 r)).card := by
      refine card_lt_card ⟨hsub, fun h => hnadj ?_⟩
      have := h (mem_filter.2 ⟨hr1, hadj1⟩)
      exact (mem_filter.1 this).2
    omega
  rw [not_subset] at this
  obtain ⟨r2, hr2, hr2'⟩ := this
  rw [mem_filter] at hr2 hr2'
  refine ⟨l1, hl1, l2, hl2, r1, hr1, r2, hr2.1, hadj1, hr2.2, fun h => hr2' ⟨hr2.1, h⟩, hnadj⟩

/-- **The peeling procedure** of Theorem 6. -/
theorem peel (G : SimpleGraph (Fin n)) (L R : Finset (Fin n)) (hLR : Disjoint L R) (c : ℝ)
    (hc : 0 ≤ c) (A : Finset (Fin n)) :
    (∃ C ⊆ A, C.Nonempty ∧ ∀ v ∈ C, NonPeel G L R C c v) ∨
      ∃ rk : Fin n → ℕ, (chainMisOn G L R A rk : ℝ) ≤ c * A.card := by
  induction A using Finset.strongInduction with
  | H A ih =>
  rcases A.eq_empty_or_nonempty with hA | hA
  · subst hA
    right; refine ⟨fun _ => 0, ?_⟩
    simp [chainMisOn]
  by_cases hall : ∀ v ∈ A, NonPeel G L R A c v
  · exact Or.inl ⟨A, Subset.refl _, hA, hall⟩
  push_neg at hall
  obtain ⟨v, hvA, hv⟩ := hall
  rcases ih (A.erase v) (erase_ssubset hvA) with ⟨C, hC, hCne, hCp⟩ | ⟨rk', hrk'⟩
  · exact Or.inl ⟨C, hC.trans (erase_subset _ _), hCne, hCp⟩
  right
  let rk : Fin n → ℕ := fun u => if u = v then 0 else rk' u + 1
  refine ⟨rk, ?_⟩
  set M := ((L ∩ A) ×ˢ (R ∩ A)).filter (fun p => ¬ (G.Adj p.1 p.2 ↔ rk p.2 < rk p.1))
  set M' := ((L ∩ A.erase v) ×ˢ (R ∩ A.erase v)).filter
    (fun p => ¬ (G.Adj p.1 p.2 ↔ rk' p.2 < rk' p.1))
  have hsub : M ⊆ M' ∪ (M.filter (fun p => p.1 = v) ∪ M.filter (fun p => p.2 = v)) := by
    intro p hp
    by_cases h1 : p.1 = v
    · exact mem_union_right _ (mem_union_left _ (mem_filter.2 ⟨hp, h1⟩))
    by_cases h2 : p.2 = v
    · exact mem_union_right _ (mem_union_right _ (mem_filter.2 ⟨hp, h2⟩))
    refine mem_union_left _ ?_
    rw [mem_filter, mem_product] at hp ⊢
    obtain ⟨⟨hp1, hp2⟩, hp3⟩ := hp
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [mem_inter] at hp1 ⊢; exact ⟨hp1.1, mem_erase.2 ⟨h1, hp1.2⟩⟩
    · rw [mem_inter] at hp2 ⊢; exact ⟨hp2.1, mem_erase.2 ⟨h2, hp2.2⟩⟩
    · simp only [rk, h1, h2, if_false, Nat.add_lt_add_iff_right] at hp3
      exact hp3
  have hA1 : ((M.filter (fun p => p.1 = v)).card : ℝ) + (M.filter (fun p => p.2 = v)).card ≤ c := by
    by_cases hvL : v ∈ L
    · have hvR : v ∉ R := disjoint_left.1 hLR hvL
      have e2 : M.filter (fun p => p.2 = v) = ∅ := by
        rw [filter_eq_empty_iff]
        intro p hp h
        have := (mem_product.1 (mem_filter.1 hp).1).2
        rw [h] at this
        exact hvR (mem_inter.1 this).1
      have e1 : (M.filter (fun p => p.1 = v)).card ≤
          ((R ∩ A).filter (fun r => G.Adj v r)).card := by
        refine card_le_card_of_injOn (fun p => p.2) ?_ ?_
        · intro p hp
          rw [coe_filter] at hp
          obtain ⟨hpM, hpv⟩ := hp
          rw [mem_filter, mem_product] at hpM
          rw [coe_filter]
          refine ⟨hpM.1.2, ?_⟩
          have h3 := hpM.2
          simp only [rk, hpv, if_true, Nat.not_lt_zero, iff_false, not_not] at h3
          exact h3
        · intro p hp p' hp' h
          rw [coe_filter] at hp hp'
          exact Prod.ext (hp.2.trans hp'.2.symm) h
      have hle : (((R ∩ A).filter (fun r => G.Adj v r)).card : ℝ) ≤ c := by
        by_contra hlt; push_neg at hlt
        exact hv (Or.inl ⟨hvL, hlt⟩)
      rw [e2, card_empty, Nat.cast_zero, add_zero]
      exact le_trans (by exact_mod_cast e1) hle
    · have e1 : M.filter (fun p => p.1 = v) = ∅ := by
        rw [filter_eq_empty_iff]
        intro p hp h
        have := (mem_product.1 (mem_filter.1 hp).1).1
        rw [h] at this
        exact hvL (mem_inter.1 this).1
      rw [e1, card_empty, Nat.cast_zero, zero_add]
      by_cases hvR : v ∈ R
      · have e2 : (M.filter (fun p => p.2 = v)).card ≤
            ((L ∩ A).filter (fun l => ¬ G.Adj l v)).card := by
          refine card_le_card_of_injOn (fun p => p.1) ?_ ?_
          · intro p hp
            rw [coe_filter] at hp
            obtain ⟨hpM, hpv⟩ := hp
            rw [mem_filter, mem_product] at hpM
            rw [coe_filter]
            refine ⟨hpM.1.1, ?_⟩
            have h3 := hpM.2
            have hp1 : p.1 ≠ v := fun h => hvL (h ▸ (mem_inter.1 hpM.1.1).1)
            simp only [rk, hpv, if_true, hp1, if_false, Nat.zero_lt_succ, iff_true] at h3
            exact h3
          · intro p hp p' hp' h
            rw [coe_filter] at hp hp'
            exact Prod.ext h (hp.2.trans hp'.2.symm)
        have hle : (((L ∩ A).filter (fun l => ¬ G.Adj l v)).card : ℝ) ≤ c := by
          by_contra hlt; push_neg at hlt
          exact hv (Or.inr ⟨hvR, hlt⟩)
        exact le_trans (by exact_mod_cast e2) hle
      · have e2 : M.filter (fun p => p.2 = v) = ∅ := by
          rw [filter_eq_empty_iff]
          intro p hp h
          have := (mem_product.1 (mem_filter.1 hp).1).2
          rw [h] at this
          exact hvR (mem_inter.1 this).1
        rw [e2]; simpa using hc
  have hcard : (M.card : ℝ) ≤ M'.card + ((M.filter (fun p => p.1 = v)).card +
      (M.filter (fun p => p.2 = v)).card) := by
    have := (card_le_card hsub).trans ((card_union_le _ _).trans
      (Nat.add_le_add_left (card_union_le _ _) _))
    exact_mod_cast this
  have hAc : ((A.erase v).card : ℝ) = A.card - 1 := by
    rw [card_erase_of_mem hvA, Nat.cast_sub (card_pos.2 hA)]; simp
  have hM' : (M'.card : ℝ) ≤ c * (A.erase v).card := hrk'
  show (M.card : ℝ) ≤ c * A.card
  rw [hAc] at hM'
  nlinarith

/-- Sequences avoiding a set. -/
theorem card_avoid (m : ℕ) (B : Finset (Fin n)) :
    (univ.filter (fun w : Fin m → Fin n => ∀ j, w j ∉ B)).card = (n - B.card) ^ m := by
  have : univ.filter (fun w : Fin m → Fin n => ∀ j, w j ∉ B) = Fintype.piFinset (fun _ => Bᶜ) := by
    ext w; simp [Fintype.mem_piFinset]
  rw [this, Fintype.card_piFinset, prod_const, card_univ, Fintype.card_fin, card_compl,
    Fintype.card_fin]

/-- Sequences with a prescribed value at `i` avoiding a set elsewhere. -/
theorem card_avoid_at (m : ℕ) (i : Fin m) (v : Fin n) (B : Finset (Fin n)) :
    (univ.filter (fun w : Fin m → Fin n => w i = v ∧ ∀ j, j ≠ i → w j ∉ B)).card ≤
      (n - B.card) ^ (m - 1) := by
  have : univ.filter (fun w : Fin m → Fin n => w i = v ∧ ∀ j, j ≠ i → w j ∉ B) ⊆
      Fintype.piFinset (fun j => if j = i then {v} else Bᶜ) := by
    intro w hw
    rw [mem_filter] at hw
    rw [Fintype.mem_piFinset]
    intro j
    by_cases hj : j = i
    · subst hj; simp [hw.2.1]
    · simp [hj, hw.2.2 j hj]
  refine (card_le_card this).trans (le_of_eq ?_)
  rw [Fintype.card_piFinset]
  simp only [apply_ite Finset.card, card_singleton, card_compl, Fintype.card_fin]
  rw [prod_ite, prod_const_one, one_mul, prod_const]
  congr 1
  have h1 : (univ.filter (fun j : Fin m => j = i)).card = 1 := by
    rw [filter_eq' univ i]; simp
  have h2 := card_filter_add_card_filter_not (s := (univ : Finset (Fin m))) (fun j => j = i)
  rw [card_univ, Fintype.card_fin, h1] at h2
  omega

/-- **Theorem 6 of arXiv:1902.06135** (counting form, sampling with repetition). -/
theorem thm6 (G : SimpleGraph (Fin n)) (L R : Finset (Fin n)) (hLR : Disjoint L R) (ε : ℝ)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hfar : ∀ rk : Fin n → ℕ, ε * (n : ℝ) ^ 2 < chainMisOn G L R univ rk) (m : ℕ) :
    ((univ.filter (fun w : Fin m → Fin n => ¬ HasM2 G L R (img w))).card : ℝ) ≤
      (m + 1) * (1 - ε) ^ (m - 1) * (n : ℝ) ^ m := by
  have hc : 0 ≤ ε * n := by positivity
  rcases peel G L R hLR (ε * n) hc univ with ⟨C, -, hCne, hCp⟩ | ⟨rk, hrk⟩
  swap
  · exfalso
    have := hfar rk
    rw [card_univ, Fintype.card_fin] at hrk
    nlinarith
  -- the blocking sets
  let B : Fin n → Finset (Fin n) := fun v =>
    if v ∈ L then (R ∩ C).filter (fun r => G.Adj v r) else (L ∩ C).filter (fun l => ¬ G.Adj l v)
  have hB : ∀ v ∈ C, ε * n < ((B v).card : ℝ) := by
    intro v hv
    rcases hCp v hv with ⟨hvL, h⟩ | ⟨hvR, h⟩
    · simp only [B, hvL, if_true]; exact h
    · have hvL : v ∉ L := fun h => disjoint_left.1 hLR h hvR
      simp only [B, hvL, if_false]; exact h
  have hCbig : ε * n < (C.card : ℝ) := by
    obtain ⟨v, hv⟩ := hCne
    refine (hB v hv).trans_le ?_
    have : B v ⊆ C := by
      simp only [B]; split_ifs
      · exact (filter_subset _ _).trans inter_subset_right
      · exact (filter_subset _ _).trans inter_subset_right
    exact_mod_cast card_le_card this
  -- structure of M₂-free samples
  have hstruct : univ.filter (fun w : Fin m → Fin n => ¬ HasM2 G L R (img w)) ⊆
      univ.filter (fun w : Fin m → Fin n => ∀ j, w j ∉ C) ∪
        univ.biUnion (fun i : Fin m => C.biUnion (fun v =>
          univ.filter (fun w : Fin m → Fin n => w i = v ∧ ∀ j, j ≠ i → w j ∉ B v))) := by
    intro w hw
    rw [mem_filter] at hw
    by_cases hmiss : ∀ j, w j ∉ C
    · exact mem_union_left _ (mem_filter.2 ⟨mem_univ _, hmiss⟩)
    refine mem_union_right _ ?_
    push_neg at hmiss
    -- apply Theorem 5 to `X = img w ∩ C`
    by_contra hno
    apply hw.2
    have key := hasM2_of_noPeelable G L R (img w ∩ C) ?_ ?_ ?_
    · exact key.mono inter_subset_left
    · obtain ⟨j, hj⟩ := hmiss
      rcases hCp (w j) hj with ⟨h, -⟩ | ⟨h, -⟩
      · exact ⟨w j, mem_inter.2 ⟨mem_union_left _ h, mem_inter.2 ⟨(mem_img w _).2 ⟨j, rfl⟩, hj⟩⟩⟩
      · exact ⟨w j, mem_inter.2 ⟨mem_union_right _ h, mem_inter.2 ⟨(mem_img w _).2 ⟨j, rfl⟩, hj⟩⟩⟩
    · intro l hl
      obtain ⟨hlL, hlw, hlC⟩ : l ∈ L ∧ l ∈ img w ∧ l ∈ C := by
        simp only [mem_inter] at hl; exact ⟨hl.1, hl.2.1, hl.2.2⟩
      obtain ⟨i, rfl⟩ := (mem_img w _).1 hlw
      have : ¬ ∀ j, j ≠ i → w j ∉ B (w i) := fun h =>
        hno (mem_biUnion.2 ⟨i, mem_univ _, mem_biUnion.2 ⟨w i, hlC, mem_filter.2 ⟨mem_univ _, rfl, h⟩⟩⟩)
      push_neg at this
      obtain ⟨j, -, hj⟩ := this
      simp only [B, hlL, if_true, mem_filter, mem_inter] at hj
      exact ⟨w j, mem_inter.2 ⟨hj.1.1, mem_inter.2 ⟨(mem_img w _).2 ⟨j, rfl⟩, hj.1.2⟩⟩, hj.2⟩
    · intro r hr
      obtain ⟨hrR, hrw, hrC⟩ : r ∈ R ∧ r ∈ img w ∧ r ∈ C := by
        simp only [mem_inter] at hr; exact ⟨hr.1, hr.2.1, hr.2.2⟩
      have hrL : r ∉ L := fun h => disjoint_left.1 hLR h hrR
      obtain ⟨i, rfl⟩ := (mem_img w _).1 hrw
      have : ¬ ∀ j, j ≠ i → w j ∉ B (w i) := fun h =>
        hno (mem_biUnion.2 ⟨i, mem_univ _, mem_biUnion.2 ⟨w i, hrC, mem_filter.2 ⟨mem_univ _, rfl, h⟩⟩⟩)
      push_neg at this
      obtain ⟨j, -, hj⟩ := this
      simp only [B, hrL, if_false, mem_filter, mem_inter] at hj
      exact ⟨w j, mem_inter.2 ⟨hj.1.1, mem_inter.2 ⟨(mem_img w _).2 ⟨j, rfl⟩, hj.1.2⟩⟩, hj.2⟩
  -- counting
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hr0 : 0 ≤ 1 - ε := by linarith
  have hCn : C.card ≤ n := (card_le_univ C).trans (by simp)
  have hBn : ∀ v, (B v).card ≤ n := fun v => (card_le_univ _).trans (by simp)
  have h1 : ((univ.filter (fun w : Fin m → Fin n => ∀ j, w j ∉ C)).card : ℝ) ≤
      (n : ℝ) ^ m * (1 - ε) ^ (m - 1) := by
    rw [card_avoid, Nat.cast_pow, Nat.cast_sub hCn]
    have : (n : ℝ) - C.card ≤ n * (1 - ε) := by nlinarith
    calc ((n : ℝ) - C.card) ^ m ≤ (n * (1 - ε)) ^ m :=
          pow_le_pow_left₀ (by linarith [(by exact_mod_cast hCn : (C.card : ℝ) ≤ n)]) this m
      _ = (n : ℝ) ^ m * (1 - ε) ^ m := mul_pow _ _ _
      _ ≤ (n : ℝ) ^ m * (1 - ε) ^ (m - 1) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hr0 (by linarith) (Nat.sub_le _ _))
            (by positivity)
  have h2 : ∀ (i : Fin m) (v : Fin n), v ∈ C → ((univ.filter (fun w : Fin m → Fin n =>
      w i = v ∧ ∀ j, j ≠ i → w j ∉ B v)).card : ℝ) ≤ ((n : ℝ) * (1 - ε)) ^ (m - 1) := by
    intro i v hv
    have := card_avoid_at m i v (B v)
    have h' : (((n - (B v).card) ^ (m - 1) : ℕ) : ℝ) = ((n : ℝ) - (B v).card) ^ (m - 1) := by
      rw [Nat.cast_pow, Nat.cast_sub (hBn v)]
    refine (by exact_mod_cast this : _ ≤ (((n - (B v).card) ^ (m - 1) : ℕ) : ℝ)).trans ?_
    rw [h']
    have hb := hB v hv
    exact pow_le_pow_left₀ (by linarith [(by exact_mod_cast hBn v : ((B v).card : ℝ) ≤ n)])
      (by nlinarith) _
  have h3 : ((univ.biUnion (fun i : Fin m => C.biUnion (fun v =>
      univ.filter (fun w : Fin m → Fin n => w i = v ∧ ∀ j, j ≠ i → w j ∉ B v)))).card : ℝ) ≤
      m * (n : ℝ) ^ m * (1 - ε) ^ (m - 1) := by
    have hc1 := (card_biUnion_le (s := (univ : Finset (Fin m))) (t := fun i => C.biUnion (fun v =>
      univ.filter (fun w : Fin m → Fin n => w i = v ∧ ∀ j, j ≠ i → w j ∉ B v))))
    have hc2 : ∀ i : Fin m, ((C.biUnion (fun v => univ.filter (fun w : Fin m → Fin n =>
        w i = v ∧ ∀ j, j ≠ i → w j ∉ B v))).card : ℝ) ≤ n * ((n : ℝ) * (1 - ε)) ^ (m - 1) := by
      intro i
      have := card_biUnion_le (s := C) (t := fun v => univ.filter (fun w : Fin m → Fin n =>
        w i = v ∧ ∀ j, j ≠ i → w j ∉ B v))
      have h' : ((C.biUnion (fun v => univ.filter (fun w : Fin m → Fin n =>
          w i = v ∧ ∀ j, j ≠ i → w j ∉ B v))).card : ℝ) ≤ ∑ v ∈ C, ((univ.filter
            (fun w : Fin m → Fin n => w i = v ∧ ∀ j, j ≠ i → w j ∉ B v)).card : ℝ) := by
        exact_mod_cast this
      refine h'.trans ((sum_le_sum (fun v hv => h2 i v hv)).trans ?_)
      rw [sum_const, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hCn) (by positivity)
    have h' : ((univ.biUnion (fun i : Fin m => C.biUnion (fun v =>
        univ.filter (fun w : Fin m → Fin n => w i = v ∧ ∀ j, j ≠ i → w j ∉ B v)))).card : ℝ) ≤
        ∑ i : Fin m, ((C.biUnion (fun v => univ.filter (fun w : Fin m → Fin n =>
          w i = v ∧ ∀ j, j ≠ i → w j ∉ B v))).card : ℝ) := by exact_mod_cast hc1
    refine h'.trans ((sum_le_sum (fun i _ => hc2 i)).trans ?_)
    rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm; simp
    · have : (n : ℝ) * ((n : ℝ) * (1 - ε)) ^ (m - 1) = (n : ℝ) ^ m * (1 - ε) ^ (m - 1) := by
        rw [mul_pow, ← mul_assoc, ← pow_succ']; congr 2; omega
      rw [this]; ring_nf; exact le_refl _
  have hU := card_le_card hstruct
  have hU' : ((univ.filter (fun w : Fin m → Fin n => ¬ HasM2 G L R (img w))).card : ℝ) ≤
      ((univ.filter (fun w : Fin m → Fin n => ∀ j, w j ∉ C)).card : ℝ) +
      ((univ.biUnion (fun i : Fin m => C.biUnion (fun v =>
        univ.filter (fun w : Fin m → Fin n => w i = v ∧ ∀ j, j ≠ i → w j ∉ B v)))).card : ℝ) := by
    exact_mod_cast hU.trans (card_union_le _ _)
  linarith

end E34
