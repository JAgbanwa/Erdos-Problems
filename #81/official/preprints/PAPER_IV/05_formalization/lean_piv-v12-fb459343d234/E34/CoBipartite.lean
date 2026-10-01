import E34.CycleCount

/-!
# E34 — Lemma L2: co-bipartite graphs of rooted defect `s`

If `V = A ⊔ Aᶜ` with `A` and `Aᶜ` cliques of `G` and `G` has rooted defect `≤ s`, then some
chordal `G'` satisfies `editDist G G' ≤ 2·√s·n^(3/2) + n`.

1. *Order of `B = Aᶜ`* (`exists_rank`): eliminate `B` with root `A`, obtaining a rank
   `σ` injective on `B` such that each `b ∈ B` is defect-simplicial in
   `U_b = A ∪ {b' ∈ B : σ b ≤ σ b'}`.  Let `D_b = N_{U_b}(b) \ C_b` (`|D_b| ≤ s`).
2. *Inversions* (`card_inv_step_le`): if `σ b < σ b'`, `a ~ b` and `a ≁ b'`, then `a, b'` are
   non-adjacent neighbours of `b` in `U_b`, so `a ∈ D_b` or `b' ∈ D_b`.  Hence each `b`
   contributes at most `s·n` inversions and `Σ_a I_a ≤ s·n²`.  (This replaces the König step
   of the note: `D_b` itself is a vertex cover of the non-edges.)
3. *One row* (`row_cost`): some threshold `t` has cost `f ≤ 2√I + 1`.
4. *Chain target* (`chainGraph`): `A`, `B` cliques, `a ~ b ⇔ t_a ≤ σ b`; it has a perfect
   elimination order (`isChordal_of_rank`).
5. *Cauchy–Schwarz*: `Σ_a (2√I_a + 1) ≤ 2√(|A| Σ I_a) + |A| ≤ 2√s·n^(3/2) + n`.
-/

namespace E34

open Finset PaperIV.RootedSimplicialDefect

/-! ## Perfect elimination by a rank function gives chordality -/

/-- If every vertex's higher-ranked neighbours are pairwise adjacent (for an injective rank),
the graph has no induced `C_k`, `k ≥ 4`. -/
theorem isChordal_of_rank {V : Type*} (H : SimpleGraph V) (ρ : V → ℕ) (hρ : Function.Injective ρ)
    (h : ∀ v x y, H.Adj v x → H.Adj v y → ρ v < ρ x → ρ v < ρ y → x ≠ y → H.Adj x y) :
    AlonShapira.IsChordal H := by
  intro k F hF
  obtain ⟨hk, rfl⟩ := hF
  refine ⟨fun e => ?_⟩
  obtain ⟨p, -, hp⟩ := Finset.exists_min_image (univ : Finset (Fin k)) (fun i => ρ (e i))
    ⟨⟨0, by omega⟩, mem_univ _⟩
  set q₁ := succPos (by omega) p
  set q₂ := predPos (by omega) p
  have hlt : ∀ q, q ≠ p → ρ (e p) < ρ (e q) := by
    intro q hq
    have hle := hp q (mem_univ _)
    rcases lt_or_eq_of_le hle with h' | h'
    · exact h'
    · exact absurd (e.injective (hρ h')).symm hq
  have ha1 : H.Adj (e p) (e q₁) := e.map_adj_iff.2 (cyc_adj_succ hk p)
  have ha2 : H.Adj (e p) (e q₂) := e.map_adj_iff.2 (cyc_adj_pred hk p)
  have hne : e q₁ ≠ e q₂ := fun h' => succ_ne_pred hk p (e.injective h')
  have := h _ _ _ ha1 ha2 (hlt _ (cyc_adj_succ hk p).ne.symm) (hlt _ (cyc_adj_pred hk p).ne.symm) hne
  exact not_cyc_adj_succ_pred hk p (e.map_adj_iff.1 this)

/-! ## One row: threshold cost versus inversions -/

section Row

variable {ι : Type*} [DecidableEq ι] (B : Finset ι) (σ : ι → ℕ) (r : ι → Prop) [DecidablePred r]

/-- Cost of making the row monotone with threshold `t`. -/
def rowCost (t : ℕ) : ℕ :=
  (B.filter (fun b => σ b < t ∧ r b)).card + (B.filter (fun b => t ≤ σ b ∧ ¬ r b)).card

/-- Inversions of the row. -/
def rowInv : ℕ :=
  ((B ×ˢ B).filter (fun p => σ p.1 < σ p.2 ∧ r p.1 ∧ ¬ r p.2)).card

/-- Number of ones before position `t`. -/
def onesBefore (t : ℕ) : ℕ := (B.filter (fun b => σ b < t ∧ r b)).card

theorem onesBefore_succ_le (hσ : Set.InjOn σ B) (t : ℕ) :
    onesBefore B σ r (t + 1) ≤ onesBefore B σ r t + 1 := by
  unfold onesBefore
  have hsub : B.filter (fun b => σ b < t + 1 ∧ r b) ⊆
      B.filter (fun b => σ b < t ∧ r b) ∪ B.filter (fun b => σ b = t) := by
    intro b hb
    simp only [mem_filter] at hb ⊢
    simp only [mem_union, mem_filter]
    rcases Nat.lt_or_ge (σ b) t with h | h
    · left; exact ⟨hb.1, h, hb.2.2⟩
    · right; exact ⟨hb.1, by omega⟩
  have h1 : (B.filter (fun b => σ b = t)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [mem_filter] at ha hb
    exact hσ ha.1 hb.1 (ha.2.trans hb.2.symm)
  exact (card_le_card hsub).trans ((card_union_le _ _).trans (by omega))

theorem exists_onesBefore_eq (hσ : Set.InjOn σ B) :
    ∀ M h : ℕ, h ≤ onesBefore B σ r M → ∃ t ≤ M, onesBefore B σ r t = h := by
  intro M
  induction M with
  | zero =>
    intro h hh
    refine ⟨0, le_refl _, ?_⟩
    have : onesBefore B σ r 0 = 0 := by
      unfold onesBefore
      rw [card_eq_zero, filter_eq_empty_iff]
      intro b _ hb; omega
    omega
  | succ M ih =>
    intro h hh
    rcases Nat.lt_or_ge (onesBefore B σ r M) h with hlt | hge
    · have := onesBefore_succ_le B σ r hσ M
      exact ⟨M + 1, le_refl _, by omega⟩
    · obtain ⟨t, ht, htt⟩ := ih h hge
      exact ⟨t, by omega, htt⟩

theorem inv_ge_product (t : ℕ) :
    onesBefore B σ r t * (B.filter (fun b => t ≤ σ b ∧ ¬ r b)).card ≤ rowInv B σ r := by
  unfold onesBefore rowInv
  rw [← card_product]
  apply card_le_card
  intro p hp
  simp only [mem_product, mem_filter] at hp ⊢
  obtain ⟨⟨h1, h2, h3⟩, ⟨h4, h5, h6⟩⟩ := hp
  exact ⟨⟨h1, h4⟩, by omega, h3, h6⟩

/-- **One row**: some threshold has cost `≤ 2√I + 1`. -/
theorem row_cost (hσ : Set.InjOn σ B) :
    ∃ t : ℕ, (rowCost B σ r t : ℝ) ≤ 2 * Real.sqrt (rowInv B σ r) + 1 := by
  set M := B.sup σ + 1 with hM
  obtain ⟨t₀, -, ht₀⟩ := Finset.exists_min_image (range (M + 1)) (rowCost B σ r)
    ⟨0, mem_range.2 (by omega)⟩
  refine ⟨t₀, ?_⟩
  set f := rowCost B σ r t₀ with hf
  -- total ones
  have hMz : (B.filter (fun b => M ≤ σ b ∧ ¬ r b)).card = 0 := by
    rw [card_eq_zero, filter_eq_empty_iff]
    intro b hb h
    have := Finset.le_sup (f := σ) hb
    omega
  have hfM : f ≤ onesBefore B σ r M := by
    have := ht₀ M (mem_range.2 (by omega))
    unfold rowCost at this
    rw [hMz] at this
    unfold onesBefore
    omega
  set h := (f + 1) / 2 with hh
  obtain ⟨t, -, ht⟩ := exists_onesBefore_eq B σ r hσ M h (by omega)
  -- the cost at `t` is at least `f`
  have hcost_t : f ≤ rowCost B σ r t := by
    rcases Nat.lt_or_ge t (M + 1) with htM | htM
    · exact ht₀ t (mem_range.2 htM)
    · have e1 : rowCost B σ r t = rowCost B σ r M := by
        unfold rowCost
        have ea : B.filter (fun b => σ b < t ∧ r b) = B.filter (fun b => σ b < M ∧ r b) := by
          apply filter_congr
          intro b hb
          have := Finset.le_sup (f := σ) hb
          constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by omega, h2⟩
        have eb : B.filter (fun b => t ≤ σ b ∧ ¬ r b) = ∅ := by
          rw [filter_eq_empty_iff]
          intro b hb h'
          have := Finset.le_sup (f := σ) hb
          omega
        rw [ea, eb, hMz, card_empty]
      rw [e1]; exact ht₀ M (mem_range.2 (by omega))
  have hz : f - h ≤ (B.filter (fun b => t ≤ σ b ∧ ¬ r b)).card := by
    unfold rowCost at hcost_t
    unfold onesBefore at ht
    omega
  have hprod := inv_ge_product B σ r t
  rw [ht] at hprod
  have hI : h * (f - h) ≤ rowInv B σ r := (Nat.mul_le_mul_left _ hz).trans hprod
  -- `f² ≤ 4 I + 1`
  have hsq : f * f ≤ 4 * rowInv B σ r + 1 := by
    have : f * f ≤ 4 * (h * (f - h)) + 1 := by
      rcases Nat.even_or_odd f with ⟨q, hq⟩ | ⟨q, hq⟩
      · have e1 : h = q := by omega
        have e2 : f - h = q := by omega
        rw [e2, e1, hq]; nlinarith
      · have e1 : h = q + 1 := by omega
        have e2 : f - h = q := by omega
        rw [e2, e1, hq]; nlinarith
    omega
  rcases Nat.eq_zero_or_pos f with h0 | hpos
  · rw [h0]; simp; positivity
  · have hsqR : ((f : ℝ) - 1) ^ 2 ≤ 4 * (rowInv B σ r : ℝ) := by
      have : (f : ℝ) * f ≤ 4 * (rowInv B σ r : ℝ) + 1 := by exact_mod_cast hsq
      have h1 : (1 : ℝ) ≤ f := by exact_mod_cast hpos
      nlinarith
    have := Real.abs_le_sqrt hsqR
    have h2 : Real.sqrt (4 * (rowInv B σ r : ℝ)) = 2 * Real.sqrt (rowInv B σ r) := by
      rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num)]
    rw [h2] at this
    have := le_abs_self ((f : ℝ) - 1)
    linarith

end Row

/-! ## Elimination order of `B` with root `A` -/

variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

theorem exists_rank {s : ℕ} (hG : RootedDefectAt G s) (A : Finset (Fin n))
    (hA : G.IsClique (A : Set (Fin n))) :
    ∀ B' : Finset (Fin n), Disjoint A B' → ∃ σ : Fin n → ℕ, Set.InjOn σ B' ∧
      ∀ b ∈ B', DefectSimplicialOn G (A ∪ B'.filter (fun b' => σ b ≤ σ b')) s b := by
  intro B'
  induction B' using Finset.strongInduction with
  | H B' ih =>
    intro hdisj
    rcases B'.eq_empty_or_nonempty with hB | hB
    · subst hB
      exact ⟨fun _ => 0, by simp, by simp⟩
    · obtain ⟨b₀, hb₀, hdef⟩ := hG (A ∪ B') A subset_union_left hA (by
        obtain ⟨b, hb⟩ := hB
        exact ⟨b, mem_sdiff.2 ⟨mem_union_right _ hb, disjoint_right.1 hdisj hb⟩⟩)
      have hb₀B : b₀ ∈ B' := by
        rcases mem_union.1 (mem_sdiff.1 hb₀).1 with h | h
        · exact absurd h (mem_sdiff.1 hb₀).2
        · exact h
      obtain ⟨σ', hinj, hprop⟩ := ih (B'.erase b₀) (erase_ssubset hb₀B)
        (disjoint_of_subset_right (erase_subset _ _) hdisj)
      refine ⟨fun b => if b = b₀ then 0 else σ' b + 1, ?_, ?_⟩
      · intro x hx y hy hxy
        simp only at hxy
        by_cases hx0 : x = b₀
        · by_cases hy0 : y = b₀
          · rw [hx0, hy0]
          · simp [hx0, hy0] at hxy
        · by_cases hy0 : y = b₀
          · simp [hx0, hy0] at hxy
          · simp only [hx0, hy0, if_false] at hxy
            exact hinj (mem_erase.2 ⟨hx0, hx⟩) (mem_erase.2 ⟨hy0, hy⟩) (by omega)
      · intro b hb
        by_cases hb0 : b = b₀
        · subst hb0
          have e : B'.filter (fun b' => (if b = b then 0 else σ' b + 1) ≤
              (if b' = b then 0 else σ' b' + 1)) = B' := by
            apply filter_true_of_mem; intro x _; simp
          rw [e]
          have : A ∪ B' = A ∪ B' := rfl
          simpa using hdef
        · have e : B'.filter (fun b' => (if b = b₀ then 0 else σ' b + 1) ≤
              (if b' = b₀ then 0 else σ' b' + 1)) =
              (B'.erase b₀).filter (fun b' => σ' b ≤ σ' b') := by
            ext x
            simp only [mem_filter, mem_erase, hb0, if_false]
            by_cases hx0 : x = b₀
            · simp [hx0]
            · simp [hx0]
          rw [e]
          exact hprop b (mem_erase.2 ⟨hb0, hb⟩)

/-! ## Inversions per eliminated vertex -/

/-- The inversions charged to `b`. -/
def invAt (A : Finset (Fin n)) (σ : Fin n → ℕ) (b : Fin n) : Finset (Fin n × Fin n) :=
  (Aᶜ ×ˢ A).filter (fun p => σ b < σ p.1 ∧ G.Adj p.2 b ∧ ¬ G.Adj p.2 p.1)

theorem card_inter_add_compl (D A : Finset (Fin n)) : (D ∩ A).card + (D ∩ Aᶜ).card = D.card := by
  rw [← card_union_of_disjoint]
  · congr 1
    ext x; simp only [mem_union, mem_inter, mem_compl]; tauto
  · rw [disjoint_left]; intro x hx hx'
    exact (mem_compl.1 (mem_inter.1 hx').2) (mem_inter.1 hx).2

theorem card_invAt_le {s : ℕ} (A : Finset (Fin n)) (hB : G.IsClique ((Aᶜ : Finset (Fin n)) : Set (Fin n)))
    (σ : Fin n → ℕ) (b : Fin n) (hbA : b ∉ A)
    (hdef : DefectSimplicialOn G (A ∪ (Aᶜ).filter (fun b' => σ b ≤ σ b')) s b) :
    (invAt G A σ b).card ≤ s * n := by
  obtain ⟨C, hCsub, hC, hcard⟩ := hdef
  set N := neighborsIn G (A ∪ (Aᶜ).filter (fun b' => σ b ≤ σ b')) b
  set D := N \ C
  have hD : D.card ≤ s := by rw [card_sdiff_of_subset hCsub]; omega
  have hsub : invAt G A σ b ⊆ (Aᶜ ×ˢ (D ∩ A)) ∪ ((D ∩ Aᶜ) ×ˢ A) := by
    intro p hp
    simp only [invAt, mem_filter, mem_product] at hp
    obtain ⟨⟨hp1, hp2⟩, hlt, hab, hnab⟩ := hp
    have hb'N : p.1 ∈ N := by
      simp only [N, neighborsIn, mem_filter, mem_union]
      refine ⟨Or.inr ⟨hp1, by omega⟩, ?_⟩
      have hne : b ≠ p.1 := by intro h; rw [h] at hlt; omega
      exact hB (mem_compl.2 hbA) hp1 hne
    have haN : p.2 ∈ N := by
      simp only [N, neighborsIn, mem_filter, mem_union]
      exact ⟨Or.inl hp2, hab.symm⟩
    have hne : p.2 ≠ p.1 := by
      intro h; rw [h] at hp2; exact (mem_compl.1 hp1) hp2
    by_cases h2 : p.2 ∈ C
    · by_cases h1 : p.1 ∈ C
      · exact absurd (hC h2 h1 hne) hnab
      · refine mem_union_right _ (mem_product.2 ⟨mem_inter.2 ⟨mem_sdiff.2 ⟨hb'N, h1⟩, hp1⟩, hp2⟩)
    · exact mem_union_left _ (mem_product.2 ⟨hp1, mem_inter.2 ⟨mem_sdiff.2 ⟨haN, h2⟩, hp2⟩⟩)
  refine (card_le_card hsub).trans ((card_union_le _ _).trans ?_)
  rw [card_product, card_product]
  have hA' : A.card ≤ n := by simpa using card_le_univ A
  have hB' : (Aᶜ).card ≤ n := by simpa using card_le_univ (Aᶜ)
  have hsplit := card_inter_add_compl D A
  calc (Aᶜ).card * (D ∩ A).card + (D ∩ Aᶜ).card * A.card
      ≤ n * (D ∩ A).card + (D ∩ Aᶜ).card * n :=
        Nat.add_le_add (Nat.mul_le_mul_right _ hB') (Nat.mul_le_mul_left _ hA')
    _ = D.card * n := by rw [← hsplit]; ring
    _ ≤ s * n := Nat.mul_le_mul_right _ hD

/-- Double counting: the row inversions summed over `a ∈ A` are the inversions charged to the
vertices `b ∈ B`. -/
theorem sum_rowInv_eq (A : Finset (Fin n)) (σ : Fin n → ℕ) :
    ∑ a ∈ A, rowInv (Aᶜ) σ (fun b => G.Adj a b) = ∑ b ∈ Aᶜ, (invAt G A σ b).card := by
  unfold rowInv invAt
  simp only [card_filter, sum_product]
  rw [Finset.sum_comm]
  refine sum_congr rfl (fun b _ => ?_)
  rw [Finset.sum_comm]

/-! ## The chain target -/

/-- `A` and `Aᶜ` cliques, and `a ∈ A` adjacent to `b ∉ A` iff `t a ≤ σ b`. -/
def chainGraph (A : Finset (Fin n)) (σ t : Fin n → ℕ) : SimpleGraph (Fin n) where
  Adj x y := x ≠ y ∧ ((x ∈ A ↔ y ∈ A) ∨ (x ∈ A ∧ y ∉ A ∧ t x ≤ σ y) ∨
    (y ∈ A ∧ x ∉ A ∧ t y ≤ σ x))
  symm := by
    intro x y ⟨hne, h⟩
    refine ⟨hne.symm, ?_⟩
    rcases h with h | h | h
    · exact Or.inl h.symm
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)
  loopless := ⟨fun x h => h.1 rfl⟩

theorem chainGraph_isChordal (A : Finset (Fin n)) (σ t : Fin n → ℕ)
    (hσ : Set.InjOn σ ((Aᶜ : Finset (Fin n)) : Set (Fin n))) :
    AlonShapira.IsChordal (chainGraph A σ t) := by
  set M := (Aᶜ).sup σ + 1
  have hM : ∀ x, x ∉ A → σ x < M := fun x hx =>
    Nat.lt_succ_of_le (Finset.le_sup (f := σ) (mem_compl.2 hx))
  let ρ : Fin n → ℕ := fun x => if x ∈ A then M + x.val else σ x
  have hρ : Function.Injective ρ := by
    intro x y hxy
    simp only [ρ] at hxy
    by_cases hx : x ∈ A <;> by_cases hy : y ∈ A <;> simp only [hx, hy, if_true, if_false] at hxy
    · exact Fin.ext (by omega)
    · have := hM y hy; omega
    · have := hM x hx; omega
    · exact hσ (by simpa using hx) (by simpa using hy) hxy
  refine isChordal_of_rank _ ρ hρ ?_
  intro v x y hvx hvy hlx hly hxy
  refine ⟨hxy, ?_⟩
  simp only [ρ] at hlx hly
  by_cases hv : v ∈ A
  · simp only [hv, if_true] at hlx hly
    have hx : x ∈ A := by
      by_contra hx; simp only [hx, if_false] at hlx; have := hM x hx; omega
    have hy : y ∈ A := by
      by_contra hy; simp only [hy, if_false] at hly; have := hM y hy; omega
    exact Or.inl (iff_of_true hx hy)
  · simp only [hv, if_false] at hlx hly
    obtain ⟨-, hvx⟩ := hvx
    obtain ⟨-, hvy⟩ := hvy
    by_cases hx : x ∈ A <;> by_cases hy : y ∈ A
    · exact Or.inl (iff_of_true hx hy)
    · -- x ∈ A, y ∉ A
      simp only [hy, if_false] at hly
      have htx : t x ≤ σ v := by
        rcases hvx with h | h | h
        · exact absurd (h.2 hx) hv
        · exact absurd h.1 hv
        · exact h.2.2
      exact Or.inr (Or.inl ⟨hx, hy, by omega⟩)
    · simp only [hx, if_false] at hlx
      have hty : t y ≤ σ v := by
        rcases hvy with h | h | h
        · exact absurd (h.2 hy) hv
        · exact absurd h.1 hv
        · exact h.2.2
      exact Or.inr (Or.inr ⟨hy, hx, by omega⟩)
    · exact Or.inl (iff_of_false hx hy)

theorem chainGraph_adj_cross (A : Finset (Fin n)) (σ t : Fin n → ℕ) {a b : Fin n}
    (ha : a ∈ A) (hb : b ∉ A) : (chainGraph A σ t).Adj a b ↔ t a ≤ σ b := by
  constructor
  · rintro ⟨-, h | h | h⟩
    · exact absurd (h.1 ha) hb
    · exact h.2.2
    · exact absurd h.1 hb
  · intro h
    refine ⟨fun e => hb (e ▸ ha), Or.inr (Or.inl ⟨ha, hb, h⟩)⟩

/-- The edit distance to the chain target is at most the sum of the row costs. -/
theorem editDist_chain_le (A : Finset (Fin n)) (hA : G.IsClique (A : Set (Fin n)))
    (hB : G.IsClique ((Aᶜ : Finset (Fin n)) : Set (Fin n))) (σ t : Fin n → ℕ) :
    AlonShapira.editDist G (chainGraph A σ t) ≤
      ∑ a ∈ A, rowCost (Aᶜ) σ (fun b => G.Adj a b) (t a) := by
  classical
  set H := chainGraph A σ t
  set Mm := (A ×ˢ Aᶜ).filter (fun p => ¬ (G.Adj p.1 p.2 ↔ H.Adj p.1 p.2))
  have hsub : symmDiff G.edgeFinset H.edgeFinset ⊆ Mm.image (fun p => s(p.1, p.2)) := by
    intro e he
    induction e using Sym2.ind with
    | h x y =>
      simp only [Finset.mem_symmDiff, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
      have hmis : ¬ (G.Adj x y ↔ H.Adj x y) := by tauto
      have hxy : x ≠ y := by
        intro h; subst h; exact hmis (iff_of_false (G.irrefl) (H.irrefl))
      rw [mem_image]
      by_cases hx : x ∈ A <;> by_cases hy : y ∈ A
      · exact absurd (iff_of_true (hA hx hy hxy) ⟨hxy, Or.inl (iff_of_true hx hy)⟩) hmis
      · exact ⟨(x, y), mem_filter.2 ⟨mem_product.2 ⟨hx, mem_compl.2 hy⟩, hmis⟩, rfl⟩
      · refine ⟨(y, x), mem_filter.2 ⟨mem_product.2 ⟨hy, mem_compl.2 hx⟩, ?_⟩, Sym2.eq_swap⟩
        rwa [G.adj_comm, H.adj_comm]
      · exact absurd (iff_of_true (hB (mem_compl.2 hx) (mem_compl.2 hy) hxy)
          ⟨hxy, Or.inl (iff_of_false hx hy)⟩) hmis
  rw [editDist_eq_card]
  refine (card_le_card hsub).trans (card_image_le.trans ?_)
  have : Mm = A.biUnion (fun a => ((Aᶜ).filter (fun b => ¬ (G.Adj a b ↔ H.Adj a b))).map
      ⟨fun b => (a, b), fun x y h => by simpa using h⟩) := by
    ext p
    simp only [Mm, mem_filter, mem_product, mem_biUnion, mem_map, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨p.1, h1, p.2, ⟨h2, h3⟩, rfl⟩
    · rintro ⟨a, ha, b, ⟨hb, hab⟩, rfl⟩; exact ⟨⟨ha, hb⟩, hab⟩
  rw [this]
  refine card_biUnion_le.trans (sum_le_sum fun a ha => ?_)
  rw [card_map]
  unfold rowCost
  refine le_trans (card_le_card ?_) (card_union_le _ _)
  intro b hb
  rw [mem_filter] at hb
  obtain ⟨hbA, hmis⟩ := hb
  have hbA' : b ∉ A := mem_compl.1 hbA
  rw [chainGraph_adj_cross A σ t ha hbA'] at hmis
  rw [mem_union, mem_filter, mem_filter]
  by_cases hadj : G.Adj a b
  · left; exact ⟨hbA, by by_contra h; exact hmis (iff_of_true hadj (by omega)), hadj⟩
  · right; exact ⟨hbA, by by_contra h; exact hmis (iff_of_false hadj (by omega)), hadj⟩

/-! ## Lemma L2 -/

/-- **Lemma L2.** A co-bipartite graph (`A`, `Aᶜ` cliques) of rooted defect `≤ s` is within
`2·√s·n·√n + n` edits of a chordal graph (a chain graph between the two cliques). -/
theorem coBipartite_edit_le {s : ℕ} (hG : RootedDefectAt G s) (A : Finset (Fin n))
    (hA : G.IsClique (A : Set (Fin n))) (hB : G.IsClique ((Aᶜ : Finset (Fin n)) : Set (Fin n))) :
    ∃ G' : SimpleGraph (Fin n), AlonShapira.IsChordal G' ∧
      (AlonShapira.editDist G G' : ℝ) ≤ 2 * Real.sqrt s * ((n : ℝ) * Real.sqrt n) + n := by
  classical
  obtain ⟨σ, hσ, hdef⟩ := exists_rank G hG A hA (Aᶜ) disjoint_compl_right
  have hrow : ∀ a : Fin n, ∃ t : ℕ, (rowCost (Aᶜ) σ (fun b => G.Adj a b) t : ℝ) ≤
      2 * Real.sqrt (rowInv (Aᶜ) σ (fun b => G.Adj a b)) + 1 :=
    fun a => row_cost (Aᶜ) σ _ hσ
  choose t ht using hrow
  refine ⟨chainGraph A σ t, chainGraph_isChordal A σ t hσ, ?_⟩
  have h1 : (AlonShapira.editDist G (chainGraph A σ t) : ℝ) ≤
      ∑ a ∈ A, (rowCost (Aᶜ) σ (fun b => G.Adj a b) (t a) : ℝ) := by
    exact_mod_cast editDist_chain_le G A hA hB σ t
  have h2 : ∑ a ∈ A, (rowCost (Aᶜ) σ (fun b => G.Adj a b) (t a) : ℝ) ≤
      ∑ a ∈ A, (2 * Real.sqrt (rowInv (Aᶜ) σ (fun b => G.Adj a b)) + 1) :=
    sum_le_sum fun a _ => ht a
  rw [sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul, mul_one] at h2
  -- Cauchy–Schwarz
  have hCS : ∑ a ∈ A, Real.sqrt (rowInv (Aᶜ) σ (fun b => G.Adj a b)) ≤
      Real.sqrt (A.card) * Real.sqrt (∑ a ∈ A, (rowInv (Aᶜ) σ (fun b => G.Adj a b) : ℝ)) := by
    have := Real.sum_sqrt_mul_sqrt_le A (f := fun _ => (1 : ℝ))
      (g := fun a => (rowInv (Aᶜ) σ (fun b => G.Adj a b) : ℝ)) (fun _ => by norm_num)
      (fun _ => by positivity)
    simpa using this
  -- total inversions
  have hinv : ∑ a ∈ A, (rowInv (Aᶜ) σ (fun b => G.Adj a b) : ℝ) ≤ (s : ℝ) * n * n := by
    have hN : ∑ a ∈ A, rowInv (Aᶜ) σ (fun b => G.Adj a b) ≤ n * (s * n) := by
      rw [sum_rowInv_eq]
      have hb : ∀ b ∈ (Aᶜ : Finset (Fin n)), (invAt G A σ b).card ≤ s * n := fun b hb =>
        card_invAt_le G A hB σ b (mem_compl.1 hb) (hdef b hb)
      refine (sum_le_sum hb).trans ?_
      rw [sum_const, smul_eq_mul]
      exact Nat.mul_le_mul_right _ (by simpa using card_le_univ (Aᶜ))
    have : ((∑ a ∈ A, rowInv (Aᶜ) σ (fun b => G.Adj a b) : ℕ) : ℝ) ≤ ((n * (s * n) : ℕ) : ℝ) := by
      exact_mod_cast hN
    push_cast at this
    linarith
  have hAn : (A.card : ℝ) ≤ n := by exact_mod_cast (by simpa using card_le_univ A)
  have hs1 : Real.sqrt (A.card) ≤ Real.sqrt n := Real.sqrt_le_sqrt hAn
  have hs2 : Real.sqrt (∑ a ∈ A, (rowInv (Aᶜ) σ (fun b => G.Adj a b) : ℝ)) ≤
      Real.sqrt s * n := by
    calc Real.sqrt (∑ a ∈ A, (rowInv (Aᶜ) σ (fun b => G.Adj a b) : ℝ))
        ≤ Real.sqrt ((s : ℝ) * n * n) := Real.sqrt_le_sqrt hinv
      _ = Real.sqrt s * n := by
        rw [mul_assoc, Real.sqrt_mul (by positivity), Real.sqrt_mul_self (by positivity)]
  have hprod : Real.sqrt (A.card) * Real.sqrt (∑ a ∈ A, (rowInv (Aᶜ) σ (fun b => G.Adj a b) : ℝ))
      ≤ Real.sqrt n * (Real.sqrt s * n) :=
    mul_le_mul hs1 hs2 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  nlinarith [Real.sqrt_nonneg (n : ℝ), Real.sqrt_nonneg (s : ℝ)]

/-- **Lemma L2**, in the form of the note: `editDist ≤ 2·√s·n^(3/2) + n`. -/
theorem coBipartite_edit_le' {s : ℕ} (hG : RootedDefectAt G s) (A : Finset (Fin n))
    (hA : G.IsClique (A : Set (Fin n))) (hB : G.IsClique ((Aᶜ : Finset (Fin n)) : Set (Fin n))) :
    ∃ G' : SimpleGraph (Fin n), AlonShapira.IsChordal G' ∧
      (AlonShapira.editDist G G' : ℝ) ≤ 2 * Real.sqrt s * (n : ℝ) ^ ((3 : ℝ) / 2) + n := by
  obtain ⟨G', h1, h2⟩ := coBipartite_edit_le G hG A hA hB
  refine ⟨G', h1, ?_⟩
  have e : (n : ℝ) ^ ((3 : ℝ) / 2) = (n : ℝ) * Real.sqrt n := by
    rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add' (by positivity) (by norm_num),
      Real.rpow_one, Real.sqrt_eq_rpow]
  rw [e]; exact h2

end E34
