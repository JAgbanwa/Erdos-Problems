import E34.ChordalTools

/-!
# E34 — Lemma 3 of arXiv:1902.06135 (nearly simplicial vertices)

`pG G u` is the paper's `p_G(u)`: the number of (unordered) non-adjacent pairs of neighbours
of `u`.

**Lemma 3 (as proved here).** Let `V = X ⊔ Y` with `G[Y]` chordal and `p_G(x) ≤ ε n²` for every
`x ∈ X`.  Then some chordal `H` with `H[Y] = G[Y]` satisfies `editDist G H ≤ 8 √ε n²`.

Differences with the paper: the constant is `8` instead of `6` (the bookkeeping below counts
ordered pairs), and the hypothesis `n ≥ 1/ε` is not needed (Claim 3 uses the elementary
form of Lemma 4, `exists_large_clique`).

Proof.  *Claim 1*: `Σ_u q_A(u) = Σ_{a ∈ A} 2 p_G(a)`, so some `u ∈ A` has `q_A(u) ≤ 2εn²`.
*Claim 2* (`core`): by induction on the set `A ⊆ X` of unprocessed vertices, a centre map
`π` (vertices of a part are sent to its centre) with ordered cost `≤ 6 √ε n |A|`: a vertex of
low degree in `A` forms a singleton part (cost `≤ 2 √ε n`), otherwise the centre `c` with
`q_A(c) ≤ 2εn²` takes its whole neighbourhood in `A` (cost `≤ 2p(c) + 2q_A(c) ≤ 6εn²`, and
the part has more than `√ε n` vertices).  *Claim 3*: each neighbourhood `N_Y(c)` loses at
most `√(2εn²)` vertices to a clique, by Lemma 4.
-/

namespace E34

open Finset

open scoped Classical

variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

/-- The paper's `p_G(u)`: unordered non-adjacent pairs of neighbours of `u`. -/
def pG (u : Fin n) : ℕ :=
  ((univ ×ˢ univ).filter (fun p : Fin n × Fin n =>
    p.1 < p.2 ∧ G.Adj u p.1 ∧ G.Adj u p.2 ∧ ¬ G.Adj p.1 p.2)).card

/-- Ordered version of `pG`. -/
def pOrd (u : Fin n) : ℕ :=
  ((univ ×ˢ univ).filter (fun p : Fin n × Fin n =>
    p.1 ≠ p.2 ∧ G.Adj u p.1 ∧ G.Adj u p.2 ∧ ¬ G.Adj p.1 p.2)).card

theorem pOrd_eq (u : Fin n) : pOrd G u = 2 * pG G u := by
  unfold pOrd pG
  set R : Fin n × Fin n → Prop := fun p => G.Adj u p.1 ∧ G.Adj u p.2 ∧ ¬ G.Adj p.1 p.2
  have hsplit : (univ ×ˢ univ).filter (fun p : Fin n × Fin n =>
      p.1 ≠ p.2 ∧ G.Adj u p.1 ∧ G.Adj u p.2 ∧ ¬ G.Adj p.1 p.2) =
      (univ ×ˢ univ).filter (fun p : Fin n × Fin n =>
        p.1 < p.2 ∧ G.Adj u p.1 ∧ G.Adj u p.2 ∧ ¬ G.Adj p.1 p.2) ∪
      ((univ ×ˢ univ).filter (fun p : Fin n × Fin n =>
        p.1 < p.2 ∧ G.Adj u p.1 ∧ G.Adj u p.2 ∧ ¬ G.Adj p.1 p.2)).map
          (Equiv.prodComm _ _).toEmbedding := by
    ext ⟨a, b⟩
    simp only [mem_filter, mem_product, mem_univ, true_and, mem_union, mem_map,
      Equiv.coe_toEmbedding, Equiv.prodComm_apply, Prod.exists, Prod.swap_prod_mk,
      Prod.mk.injEq]
    constructor
    · rintro ⟨hab, h1, h2, h3⟩
      rcases lt_or_gt_of_ne hab with h | h
      · exact Or.inl ⟨h, h1, h2, h3⟩
      · exact Or.inr ⟨b, a, ⟨h, h2, h1, fun h' => h3 h'.symm⟩, rfl, rfl⟩
    · rintro (⟨h, h1, h2, h3⟩ | ⟨x, y, ⟨h, h1, h2, h3⟩, rfl, rfl⟩)
      · exact ⟨ne_of_lt h, h1, h2, h3⟩
      · exact ⟨ne_of_gt h, h2, h1, fun h' => h3 h'.symm⟩
  rw [hsplit, card_union_of_disjoint, card_map]
  · ring
  · rw [disjoint_left]
    rintro ⟨a, b⟩ h1 h2
    simp only [mem_filter, mem_map, Equiv.coe_toEmbedding, Equiv.prodComm_apply, Prod.exists,
      Prod.swap_prod_mk, Prod.mk.injEq, mem_product, mem_univ, true_and] at h1 h2
    obtain ⟨x, y, ⟨h, -⟩, rfl, rfl⟩ := h2
    exact lt_asymm h h1.1

/-- The paper's `q_A(u)`: induced paths `u – a – v` with middle vertex `a ∈ A`. -/
def qA (A : Finset (Fin n)) (u : Fin n) : ℕ :=
  ((A ×ˢ univ).filter (fun p : Fin n × Fin n =>
    G.Adj u p.1 ∧ G.Adj p.1 p.2 ∧ u ≠ p.2 ∧ ¬ G.Adj u p.2)).card

/-- Double counting of Claim 1. -/
theorem sum_qA (A : Finset (Fin n)) : ∑ u, qA G A u = ∑ a ∈ A, pOrd G a := by
  unfold qA pOrd
  simp only [card_filter, sum_product]
  rw [Finset.sum_comm]
  refine sum_congr rfl (fun a _ => ?_)
  refine sum_congr rfl (fun u _ => sum_congr rfl (fun v _ => ?_))
  by_cases h1 : G.Adj u a <;> by_cases h2 : G.Adj a v <;> by_cases h3 : u = v <;>
    by_cases h4 : G.Adj u v <;> simp [h1, h2, h3, h4, G.adj_comm a u]

/-- **Claim 1.** -/
theorem claim1 (A : Finset (Fin n)) (hA : A.Nonempty) (B : ℝ)
    (hp : ∀ a ∈ A, (pOrd G a : ℝ) ≤ B) : ∃ c ∈ A, (qA G A c : ℝ) ≤ B := by
  have h1 : ∑ u ∈ A, (qA G A u : ℝ) ≤ ∑ u ∈ A, B := by
    calc ∑ u ∈ A, (qA G A u : ℝ) ≤ ∑ u, (qA G A u : ℝ) :=
          sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => by positivity)
      _ = ∑ a ∈ A, (pOrd G a : ℝ) := by exact_mod_cast sum_qA G A
      _ ≤ ∑ u ∈ A, B := sum_le_sum hp
  exact exists_le_of_sum_le hA h1

/-! ## The modified graph -/

/-- `X` is partitioned by the centre map `π`; parts are cliques, a vertex `u ∈ X` sees
`N (π u)` in `Y = Xᶜ`, and `G[Y]` is kept. -/
def Hg (X : Finset (Fin n)) (π : Fin n → Fin n) (N : Fin n → Finset (Fin n)) :
    SimpleGraph (Fin n) where
  Adj u w := u ≠ w ∧ ((u ∈ X ∧ w ∈ X ∧ π u = π w) ∨ (u ∈ X ∧ w ∉ X ∧ w ∈ N (π u)) ∨
    (u ∉ X ∧ w ∈ X ∧ u ∈ N (π w)) ∨ (u ∉ X ∧ w ∉ X ∧ G.Adj u w))
  symm := by
    intro u w ⟨hne, h⟩
    refine ⟨hne.symm, ?_⟩
    rcases h with h | h | h | h
    · exact Or.inl ⟨h.2.1, h.1, h.2.2.symm⟩
    · exact Or.inr (Or.inr (Or.inl ⟨h.2.1, h.1, h.2.2⟩))
    · exact Or.inr (Or.inl ⟨h.2.1, h.1, h.2.2⟩)
    · exact Or.inr (Or.inr (Or.inr ⟨h.2.1, h.1, h.2.2.symm⟩))
  loopless := ⟨fun u h => h.1 rfl⟩

variable {G}

theorem Hg_adj_XX {X : Finset (Fin n)} {π : Fin n → Fin n} {N : Fin n → Finset (Fin n)}
    {u w : Fin n} (hu : u ∈ X) (hw : w ∈ X) : (Hg G X π N).Adj u w ↔ u ≠ w ∧ π u = π w := by
  simp only [Hg, hu, hw, not_true, true_and, false_and, and_false, or_false, false_or]

theorem Hg_adj_XY {X : Finset (Fin n)} {π : Fin n → Fin n} {N : Fin n → Finset (Fin n)}
    {u w : Fin n} (hu : u ∈ X) (hw : w ∉ X) : (Hg G X π N).Adj u w ↔ w ∈ N (π u) := by
  simp only [Hg, hu, hw, not_true, true_and, false_and, and_false, or_false, false_or,
    not_false_eq_true]
  exact ⟨fun h => h.2, fun h => ⟨fun e => hw (e ▸ hu), h⟩⟩

theorem Hg_adj_YX {X : Finset (Fin n)} {π : Fin n → Fin n} {N : Fin n → Finset (Fin n)}
    {u w : Fin n} (hu : u ∉ X) (hw : w ∈ X) : (Hg G X π N).Adj u w ↔ u ∈ N (π w) := by
  rw [SimpleGraph.adj_comm, Hg_adj_XY hw hu]

theorem Hg_adj_YY {X : Finset (Fin n)} {π : Fin n → Fin n} {N : Fin n → Finset (Fin n)}
    {u w : Fin n} (hu : u ∉ X) (hw : w ∉ X) : (Hg G X π N).Adj u w ↔ G.Adj u w := by
  simp only [Hg, hu, hw, not_false_eq_true, true_and, false_and, and_false, or_false,
    false_or]
  exact ⟨fun h => h.2, fun h => ⟨G.ne_of_adj h, h⟩⟩

variable (G)

/-- `N_Y(c)`. -/
def NY (X : Finset (Fin n)) (c : Fin n) : Finset (Fin n) := (Xᶜ).filter (G.Adj c)

/-- Ordered cost of the pairs `(u, w)` with `u ∈ A`, `w ∈ A ∪ Y`. -/
noncomputable def cost (X : Finset (Fin n)) (π : Fin n → Fin n) (A : Finset (Fin n)) : ℕ :=
  ((A ×ˢ univ).filter (fun p : Fin n × Fin n => p.1 ≠ p.2 ∧ (p.2 ∈ A ∨ p.2 ∉ X) ∧
    ¬ (G.Adj p.1 p.2 ↔ (Hg G X π (NY G X)).Adj p.1 p.2))).card

theorem cost_congr (X : Finset (Fin n)) {π π' : Fin n → Fin n} (A : Finset (Fin n))
    (hAX : A ⊆ X) (h : ∀ u ∈ A, π u = π' u) : cost G X π A = cost G X π' A := by
  unfold cost
  congr 1
  apply filter_congr
  rintro ⟨u, w⟩ hp
  simp only [mem_product] at hp
  have hu := hp.1
  simp only
  constructor <;> rintro ⟨h1, h2, h3⟩ <;> refine ⟨h1, h2, ?_⟩
  · rcases h2 with hw | hw
    · rwa [Hg_adj_XX (G := G) (N := NY G X) (hAX hu) (hAX hw), h u hu, h w hw, ← Hg_adj_XX (G := G) (N := NY G X) (hAX hu) (hAX hw)] at h3
    · rwa [Hg_adj_XY (G := G) (N := NY G X) (hAX hu) hw, h u hu, ← Hg_adj_XY (G := G) (N := NY G X) (hAX hu) hw] at h3
  · rcases h2 with hw | hw
    · rwa [Hg_adj_XX (G := G) (N := NY G X) (hAX hu) (hAX hw), ← h u hu, ← h w hw, ← Hg_adj_XX (G := G) (N := NY G X) (hAX hu) (hAX hw)] at h3
    · rwa [Hg_adj_XY (G := G) (N := NY G X) (hAX hu) hw, ← h u hu, ← Hg_adj_XY (G := G) (N := NY G X) (hAX hu) hw] at h3

/-- Splitting the cost when a part `P` is removed from `A`. -/
theorem cost_split (X : Finset (Fin n)) (π : Fin n → Fin n) (A P : Finset (Fin n))
    (hPA : P ⊆ A) :
    cost G X π A ≤ cost G X π (A \ P) +
      ((P ×ˢ univ).filter (fun p : Fin n × Fin n => p.1 ≠ p.2 ∧ (p.2 ∈ A ∨ p.2 ∉ X) ∧
        ¬ (G.Adj p.1 p.2 ↔ (Hg G X π (NY G X)).Adj p.1 p.2))).card +
      (((A \ P) ×ˢ P).filter (fun p : Fin n × Fin n =>
        ¬ (G.Adj p.1 p.2 ↔ (Hg G X π (NY G X)).Adj p.1 p.2))).card := by
  unfold cost
  refine le_trans (card_le_card ?_) (le_trans (card_union_le _ _)
    (Nat.add_le_add_right (card_union_le _ _) _))
  rintro ⟨u, w⟩ hp
  simp only [mem_filter, mem_product, mem_univ, and_true, mem_union, mem_sdiff] at hp ⊢
  obtain ⟨hu, hne, hw, hm⟩ := hp
  by_cases huP : u ∈ P
  · exact Or.inl (Or.inr ⟨huP, hne, hw, hm⟩)
  · by_cases hwP : w ∈ P
    · exact Or.inr ⟨⟨⟨hu, huP⟩, hwP⟩, hm⟩
    · refine Or.inl (Or.inl ⟨⟨hu, huP⟩, hne, ?_, hm⟩)
      rcases hw with hw | hw
      · exact Or.inl ⟨hw, hwP⟩
      · exact Or.inr hw

/-- In-degree of `u` inside `A`. -/
def dIn (A : Finset (Fin n)) (u : Fin n) : ℕ := (A.filter (G.Adj u)).card

/-- **Claim 2** (ordered cost form). -/
theorem core (X : Finset (Fin n)) (ε : ℝ) (hε : 0 ≤ ε)
    (hp : ∀ x ∈ X, (pOrd G x : ℝ) ≤ 2 * ε * (n : ℝ) ^ 2) :
    ∀ A ⊆ X, ∃ π : Fin n → Fin n, (∀ u ∈ A, π u ∈ A) ∧
      (cost G X π A : ℝ) ≤ 6 * (Real.sqrt ε * n) * A.card := by
  set r := Real.sqrt ε * n with hr
  have hr0 : 0 ≤ r := by positivity
  have hr2 : r * r = ε * (n : ℝ) ^ 2 := by
    rw [hr]; nlinarith [Real.mul_self_sqrt hε]
  intro A
  induction A using Finset.strongInduction with
  | H A ih =>
    intro hAX
    rcases A.eq_empty_or_nonempty with hA | hA
    · subst hA
      refine ⟨id, by simp, ?_⟩
      simp [cost]
    by_cases hlow : ∃ u ∈ A, (dIn G A u : ℝ) ≤ r
    · -- Case 1: a singleton part
      obtain ⟨u₀, hu₀, hd⟩ := hlow
      set P : Finset (Fin n) := {u₀}
      have hPA : P ⊆ A := by simpa [P] using hu₀
      obtain ⟨π', hπ'A, hπ'c⟩ := ih (A \ P) (sdiff_ssubset hPA (by simp [P]))
        (sdiff_subset.trans hAX)
      set π : Fin n → Fin n := fun u => if u = u₀ then u₀ else π' u
      have hπA : ∀ u ∈ A, π u ∈ A := by
        intro u hu
        by_cases h : u = u₀
        · simp [π, h, hu₀]
        · simp only [π, h, if_false]
          exact (mem_sdiff.1 (hπ'A u (mem_sdiff.2 ⟨hu, by simpa [P] using h⟩))).1
      have hcongr : cost G X π (A \ P) = cost G X π' (A \ P) :=
        cost_congr G X _ (sdiff_subset.trans hAX) (fun u hu => by
          have : u ≠ u₀ := by simpa [P] using (mem_sdiff.1 hu).2
          simp [π, this])
      have hsplit := cost_split G X π A P hPA
      have hn1 : ((P ×ˢ univ).filter (fun p : Fin n × Fin n => p.1 ≠ p.2 ∧ (p.2 ∈ A ∨ p.2 ∉ X) ∧
          ¬ (G.Adj p.1 p.2 ↔ (Hg G X π (NY G X)).Adj p.1 p.2))).card ≤ dIn G A u₀ := by
        have : ((P ×ˢ univ).filter (fun p : Fin n × Fin n => p.1 ≠ p.2 ∧ (p.2 ∈ A ∨ p.2 ∉ X) ∧
            ¬ (G.Adj p.1 p.2 ↔ (Hg G X π (NY G X)).Adj p.1 p.2))) ⊆
            P ×ˢ (A.filter (G.Adj u₀)) := by
          rintro ⟨u, w⟩ h
          simp only [mem_filter, mem_product, mem_univ, and_true, P, mem_singleton] at h ⊢
          obtain ⟨rfl, hne, hw, hm⟩ := h
          have hux : u ∈ X := hAX hu₀
          rcases hw with hw | hw
          · have hwne : w ≠ u := fun e => hne e.symm
            have hπw : π w ∈ A \ P := by
              simp only [π, hwne, if_false]
              exact hπ'A w (mem_sdiff.2 ⟨hw, by simpa [P] using hwne⟩)
            have hH : ¬ (Hg G X π (NY G X)).Adj u w := by
              rw [Hg_adj_XX hux (hAX hw)]
              rintro ⟨-, he⟩
              have : π u = u := by simp [π]
              rw [this] at he
              exact (mem_sdiff.1 hπw).2 (by simp [P, he])
            refine ⟨rfl, hw, ?_⟩
            by_contra hna
            exact hm (iff_of_false hna hH)
          · exfalso
            apply hm
            rw [Hg_adj_XY hux hw]
            simp [NY, π, hw]
        refine (card_le_card this).trans ?_
        simp [P, dIn]
      have hn2 : (((A \ P) ×ˢ P).filter (fun p : Fin n × Fin n =>
          ¬ (G.Adj p.1 p.2 ↔ (Hg G X π (NY G X)).Adj p.1 p.2))).card ≤ dIn G A u₀ := by
        have : (((A \ P) ×ˢ P).filter (fun p : Fin n × Fin n =>
            ¬ (G.Adj p.1 p.2 ↔ (Hg G X π (NY G X)).Adj p.1 p.2))) ⊆
            (A.filter (G.Adj u₀)) ×ˢ P := by
          rintro ⟨w, u⟩ h
          simp only [mem_filter, mem_product, mem_sdiff, P, mem_singleton] at h ⊢
          obtain ⟨⟨⟨hw, hwne⟩, rfl⟩, hm⟩ := h
          have hπw : π w ∈ A \ P := by
            simp only [π, hwne, if_false]
            exact hπ'A w (mem_sdiff.2 ⟨hw, by simpa [P] using hwne⟩)
          have hH : ¬ (Hg G X π (NY G X)).Adj w u := by
            rw [Hg_adj_XX (hAX hw) (hAX hu₀)]
            rintro ⟨-, he⟩
            have : π u = u := by simp [π]
            rw [this] at he
            exact (mem_sdiff.1 hπw).2 (by simp [P, ← he])
          refine ⟨⟨hw, ?_⟩, rfl⟩
          by_contra hna
          exact hm (iff_of_false (fun h => hna h.symm) hH)
        refine (card_le_card this).trans ?_
        simp [P, dIn]
      refine ⟨π, hπA, ?_⟩
      have hcardA : A.card = (A \ P).card + 1 := by
        rw [card_sdiff_of_subset hPA]; simp [P]; have := card_pos.2 hA; omega
      have hc : (cost G X π A : ℝ) ≤ cost G X π' (A \ P) + dIn G A u₀ + dIn G A u₀ := by
        rw [← hcongr]; exact_mod_cast (hsplit.trans (by omega))
      rw [hcardA]; push_cast
      nlinarith
    · -- Case 2: a large part around a good centre
      push_neg at hlow
      have hpA : ∀ a ∈ A, (pOrd G a : ℝ) ≤ 2 * ε * (n : ℝ) ^ 2 := fun a ha => hp a (hAX ha)
      obtain ⟨c, hcA, hqc⟩ := claim1 G A hA _ hpA
      set P : Finset (Fin n) := A.filter (fun u => u = c ∨ G.Adj c u)
      have hPA : P ⊆ A := filter_subset _ _
      have hcP : c ∈ P := mem_filter.2 ⟨hcA, Or.inl rfl⟩
      obtain ⟨π', hπ'A, hπ'c⟩ := ih (A \ P) (sdiff_ssubset hPA ⟨c, hcP⟩)
        (sdiff_subset.trans hAX)
      set π : Fin n → Fin n := fun u => if u ∈ P then c else π' u
      have hπA : ∀ u ∈ A, π u ∈ A := by
        intro u hu
        by_cases h : u ∈ P
        · simp [π, h, hcA]
        · simp only [π, h, if_false]
          exact (mem_sdiff.1 (hπ'A u (mem_sdiff.2 ⟨hu, h⟩))).1
      have hπP : ∀ u ∈ P, π u = c := fun u hu => by simp [π, hu]
      have hπA' : ∀ w ∈ A \ P, π w ∈ A \ P := fun w hw => by
        simp only [π, (mem_sdiff.1 hw).2, if_false]; exact hπ'A w hw
      have hcongr : cost G X π (A \ P) = cost G X π' (A \ P) :=
        cost_congr G X _ (sdiff_subset.trans hAX) (fun u hu => by
          simp [π, (mem_sdiff.1 hu).2])
      have hsplit := cost_split G X π A P hPA
      have hcX : c ∈ X := hAX hcA
      -- the two relevant sets
      set NE := (univ ×ˢ univ).filter (fun p : Fin n × Fin n =>
        p.1 ≠ p.2 ∧ G.Adj c p.1 ∧ G.Adj c p.2 ∧ ¬ G.Adj p.1 p.2)
      set Q := (A ×ˢ univ).filter (fun p : Fin n × Fin n =>
        G.Adj c p.1 ∧ G.Adj p.1 p.2 ∧ c ≠ p.2 ∧ ¬ G.Adj c p.2)
      have hNE : NE.card = pOrd G c := rfl
      have hQ : Q.card = qA G A c := rfl
      have hmemP : ∀ u, u ∈ P ↔ u ∈ A ∧ (u = c ∨ G.Adj c u) := fun u => mem_filter
      have hn1 : ((P ×ˢ univ).filter (fun p : Fin n × Fin n => p.1 ≠ p.2 ∧ (p.2 ∈ A ∨ p.2 ∉ X) ∧
          ¬ (G.Adj p.1 p.2 ↔ (Hg G X π (NY G X)).Adj p.1 p.2))).card ≤ NE.card + Q.card := by
        refine (card_le_card ?_).trans (card_union_le _ _)
        rintro ⟨u, w⟩ h
        simp only [mem_filter, mem_product, mem_univ, and_true] at h
        obtain ⟨huP, hne, hw, hm⟩ := h
        obtain ⟨huA, huc⟩ := (hmemP u).1 huP
        have hux : u ∈ X := hAX huA
        simp only [NE, Q, mem_union, mem_filter, mem_product, mem_univ, true_and, and_true]
        by_cases hwX : w ∈ X
        · have hwA : w ∈ A := hw.resolve_right (not_not.2 hwX)
          by_cases hwP : w ∈ P
          · -- both in the part: adjacent in `H`
            have hH : (Hg G X π (NY G X)).Adj u w := by
              rw [Hg_adj_XX hux hwX]; exact ⟨hne, by rw [hπP u huP, hπP w hwP]⟩
            have hna : ¬ G.Adj u w := fun h => hm (iff_of_true h hH)
            obtain ⟨-, hwc⟩ := (hmemP w).1 hwP
            have hu' : G.Adj c u := by
              rcases huc with rfl | h
              · rcases hwc with rfl | h'
                · exact absurd rfl hne
                · exact absurd h' hna
              · exact h
            have hw' : G.Adj c w := by
              rcases hwc with rfl | h
              · exact absurd hu'.symm hna
              · exact h
            exact Or.inl ⟨hne, hu', hw', hna⟩
          · have hπw := hπA' w (mem_sdiff.2 ⟨hwA, hwP⟩)
            have hH : ¬ (Hg G X π (NY G X)).Adj u w := by
              rw [Hg_adj_XX hux hwX]
              rintro ⟨-, he⟩
              rw [hπP u huP] at he
              exact (mem_sdiff.1 hπw).2 (he ▸ hcP)
            have ha : G.Adj u w := by by_contra hna; exact hm (iff_of_false hna hH)
            have hwc : ¬ (w = c ∨ G.Adj c w) := fun h => hwP ((hmemP w).2 ⟨hwA, h⟩)
            push_neg at hwc
            have hu' : G.Adj c u := by
              rcases huc with rfl | h
              · exact absurd ha hwc.2
              · exact h
            exact Or.inr ⟨huA, hu', ha, Ne.symm hwc.1, hwc.2⟩
        · have hH : (Hg G X π (NY G X)).Adj u w ↔ G.Adj c w := by
            rw [Hg_adj_XY hux hwX, hπP u huP]; simp [NY, hwX]
          rw [hH] at hm
          by_cases ha : G.Adj u w
          · have hcw : ¬ G.Adj c w := fun h => hm (iff_of_true ha h)
            have hu' : G.Adj c u := by
              rcases huc with rfl | h
              · exact absurd ha hcw
              · exact h
            exact Or.inr ⟨huA, hu', ha, fun e => hwX (e ▸ hcX), hcw⟩
          · have hcw : G.Adj c w := by by_contra h; exact hm (iff_of_false ha h)
            have hu' : G.Adj c u := by
              rcases huc with rfl | h
              · exact absurd hcw ha
              · exact h
            exact Or.inl ⟨hne, hu', hcw, ha⟩
      have hn2 : (((A \ P) ×ˢ P).filter (fun p : Fin n × Fin n =>
          ¬ (G.Adj p.1 p.2 ↔ (Hg G X π (NY G X)).Adj p.1 p.2))).card ≤ Q.card := by
        rw [← card_map (Equiv.prodComm _ _).toEmbedding]
        refine card_le_card ?_
        intro p hp
        simp only [mem_map, mem_filter, mem_product, mem_sdiff, Equiv.coe_toEmbedding,
          Equiv.prodComm_apply] at hp
        obtain ⟨⟨w, u⟩, ⟨⟨⟨hwA, hwP⟩, huP⟩, hm⟩, rfl⟩ := hp
        simp only [Prod.swap_prod_mk]
        obtain ⟨huA, huc⟩ := (hmemP u).1 huP
        have hπw := hπA' w (mem_sdiff.2 ⟨hwA, hwP⟩)
        have hH : ¬ (Hg G X π (NY G X)).Adj w u := by
          rw [Hg_adj_XX (hAX hwA) (hAX huA)]
          rintro ⟨-, he⟩
          rw [hπP u huP] at he
          exact (mem_sdiff.1 hπw).2 (he ▸ hcP)
        have ha : G.Adj w u := by by_contra hna; exact hm (iff_of_false hna hH)
        have hwc : ¬ (w = c ∨ G.Adj c w) := fun h => hwP ((hmemP w).2 ⟨hwA, h⟩)
        push_neg at hwc
        have hu' : G.Adj c u := by
          rcases huc with rfl | h
          · exact absurd ha.symm hwc.2
          · exact h
        simp only [Q, mem_filter, mem_product, mem_univ, and_true]
        exact ⟨huA, hu', ha.symm, Ne.symm hwc.1, hwc.2⟩
      refine ⟨π, hπA, ?_⟩
      -- size of the part
      have hPc : (dIn G A c : ℝ) + 1 ≤ P.card := by
        have : insert c (A.filter (G.Adj c)) ⊆ P := by
          intro u hu
          rcases mem_insert.1 hu with rfl | hu
          · exact hcP
          · exact (hmemP u).2 ⟨(mem_filter.1 hu).1, Or.inr (mem_filter.1 hu).2⟩
        have h2 := card_le_card this
        rw [card_insert_of_notMem (fun h => G.loopless.irrefl c (mem_filter.1 h).2)] at h2
        unfold dIn; exact_mod_cast h2
      have hrP : r ≤ P.card := by
        have := hlow c hcA; linarith
      have hcardA : (A.card : ℝ) = (A \ P).card + P.card := by
        rw [card_sdiff_of_subset hPA]
        have := card_le_card hPA
        push_cast [Nat.cast_sub this]; ring
      have hc : (cost G X π A : ℝ) ≤ cost G X π' (A \ P) + pOrd G c + 2 * qA G A c := by
        rw [← hcongr]
        have := hsplit.trans (Nat.add_le_add (Nat.add_le_add_left hn1 _) hn2)
        rw [hNE, hQ] at this
        exact_mod_cast (this.trans (by omega))
      have hpc := hp c hcX
      rw [hcardA]
      nlinarith

/-- The edit distance to `Hg … (NY G X)` is at most the ordered cost over `X`. -/
theorem editDist_le_cost (X : Finset (Fin n)) (π : Fin n → Fin n) :
    AlonShapira.editDist G (Hg G X π (NY G X)) ≤ cost G X π X := by
  rw [editDist_eq_card]
  unfold cost
  refine le_trans (card_le_card (t := Finset.image (fun p : Fin n × Fin n => s(p.1, p.2)) _) ?_)
    card_image_le
  intro e he
  induction e using Sym2.ind with
  | h u w =>
    simp only [Finset.mem_symmDiff, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
    have hm : ¬ (G.Adj u w ↔ (Hg G X π (NY G X)).Adj u w) := by tauto
    have hne : u ≠ w := by
      intro h; subst h; exact hm (iff_of_false (G.loopless.irrefl u) (SimpleGraph.irrefl _))
    rw [mem_image]
    by_cases hu : u ∈ X
    · refine ⟨(u, w), ?_, rfl⟩
      simp only [mem_filter, mem_product, mem_univ, and_true]
      exact ⟨hu, hne, by by_cases hw : w ∈ X <;> simp [hw], hm⟩
    · by_cases hw : w ∈ X
      · refine ⟨(w, u), ?_, Sym2.eq_swap⟩
        simp only [mem_filter, mem_product, mem_univ, and_true]
        refine ⟨hw, Ne.symm hne, Or.inr hu, ?_⟩
        rwa [G.adj_comm, (Hg G X π (NY G X)).adj_comm]
      · exact absurd ((Hg_adj_YY hu hw).symm) hm

/-- Triangle inequality for `AlonShapira.editDist`. -/
theorem asEditDist_triangle {m : ℕ} (G₁ G₂ G₃ : SimpleGraph (Fin m)) :
    AlonShapira.editDist G₁ G₃ ≤ AlonShapira.editDist G₁ G₂ + AlonShapira.editDist G₂ G₃ := by
  classical
  rw [editDist_eq_card, editDist_eq_card, editDist_eq_card]
  refine (card_le_card ?_).trans (card_union_le _ _)
  exact symmDiff_triangle G₁.edgeFinset G₂.edgeFinset G₃.edgeFinset

/-- **Lemma 3** (constant `8`). -/
theorem lemma3 (X : Finset (Fin n))
    (hY : AlonShapira.IsChordal (G.induce ((Xᶜ : Finset (Fin n)) : Set (Fin n))))
    (ε : ℝ) (hε : 0 ≤ ε) (hp : ∀ x ∈ X, (pG G x : ℝ) ≤ ε * (n : ℝ) ^ 2) :
    ∃ H : SimpleGraph (Fin n), AlonShapira.IsChordal H ∧
      (AlonShapira.editDist G H : ℝ) ≤ 8 * Real.sqrt ε * (n : ℝ) ^ 2 ∧
      ∀ u w, u ∉ X → w ∉ X → (H.Adj u w ↔ G.Adj u w) := by
  have hp' : ∀ x ∈ X, (pOrd G x : ℝ) ≤ 2 * ε * (n : ℝ) ^ 2 := by
    intro x hx; rw [pOrd_eq]; push_cast; linarith [hp x hx]
  obtain ⟨π, hπX, hcost⟩ := core G X ε hε hp' X (Subset.refl _)
  -- Claim 3: cliques in the neighbourhoods
  have hcl : ∀ c, ∃ C ⊆ NY G X c, G.IsClique (C : Set (Fin n)) ∧
      ((NY G X c).card - C.card) ^ 2 ≤ ordNE G (NY G X c) :=
    fun c => exists_large_clique G (Xᶜ) hY (NY G X c) (filter_subset _ _)
  choose C hCsub hCcl hCb using hcl
  set H := Hg G X π C
  have hXcard : (X.card : ℝ) ≤ n := by exact_mod_cast (by simpa using card_le_univ X)
  -- the loss in each neighbourhood
  have hloss : ∀ c ∈ X, (((NY G X c) \ C c).card : ℝ) ≤ Real.sqrt 2 * (Real.sqrt ε * n) := by
    intro c hc
    rw [card_sdiff_of_subset (hCsub c)]
    have h1 : ordNE G (NY G X c) ≤ pOrd G c := by
      unfold ordNE pOrd
      apply card_le_card
      intro p hp
      simp only [mem_filter, mem_product, NY, mem_univ, true_and] at hp ⊢
      exact ⟨hp.2.1, hp.1.1.2, hp.1.2.2, hp.2.2⟩
    have h2 : ((((NY G X c).card - (C c).card : ℕ) : ℝ)) ^ 2 ≤ 2 * ε * (n : ℝ) ^ 2 := by
      have : (((NY G X c).card - (C c).card) ^ 2 : ℕ) ≤ pOrd G c := (hCb c).trans h1
      have h3 : ((((NY G X c).card - (C c).card) ^ 2 : ℕ) : ℝ) ≤ pOrd G c := by exact_mod_cast this
      push_cast at h3 ⊢
      linarith [hp' c hc]
    have h4 : Real.sqrt (2 * ε * (n : ℝ) ^ 2) = Real.sqrt 2 * (Real.sqrt ε * n) := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by norm_num), Real.sqrt_sq (by positivity)]
      ring
    rw [← h4]
    exact Real.le_sqrt_of_sq_le h2
  -- edit distance between the two modified graphs
  have hHH : (AlonShapira.editDist (Hg G X π (NY G X)) H : ℝ) ≤
      Real.sqrt 2 * (Real.sqrt ε * n) * n := by
    have hsub : symmDiff (Hg G X π (NY G X)).edgeFinset H.edgeFinset ⊆
        (X.biUnion (fun u => ((NY G X (π u)) \ C (π u)).map
          ⟨fun w => (u, w), fun a b h => by simpa using h⟩)).image (fun p => s(p.1, p.2)) := by
      intro e he
      induction e using Sym2.ind with
      | h u w =>
        simp only [Finset.mem_symmDiff, SimpleGraph.mem_edgeFinset,
          SimpleGraph.mem_edgeSet] at he
        have hm : ¬ ((Hg G X π (NY G X)).Adj u w ↔ H.Adj u w) := by tauto
        rw [mem_image]
        by_cases hu : u ∈ X <;> by_cases hw : w ∈ X
        · exact absurd (by rw [Hg_adj_XX hu hw, Hg_adj_XX hu hw]) hm
        · refine ⟨(u, w), ?_, rfl⟩
          simp only [mem_biUnion, mem_map, Function.Embedding.coeFn_mk, Prod.mk.injEq]
          refine ⟨u, hu, w, ?_, rfl, rfl⟩
          rw [Hg_adj_XY hu hw, Hg_adj_XY hu hw] at hm
          rw [mem_sdiff]
          by_contra hc
          push_neg at hc
          exact hm ⟨fun h => hc h, fun h => hCsub _ h⟩
        · refine ⟨(w, u), ?_, Sym2.eq_swap⟩
          simp only [mem_biUnion, mem_map, Function.Embedding.coeFn_mk, Prod.mk.injEq]
          refine ⟨w, hw, u, ?_, rfl, rfl⟩
          rw [Hg_adj_YX hu hw, Hg_adj_YX hu hw] at hm
          rw [mem_sdiff]
          by_contra hc
          push_neg at hc
          exact hm ⟨fun h => hc h, fun h => hCsub _ h⟩
        · exact absurd (by rw [Hg_adj_YY hu hw, Hg_adj_YY hu hw]) hm
    rw [editDist_eq_card]
    have h1 := (card_le_card hsub).trans card_image_le
    have h2 := h1.trans card_biUnion_le
    have h3 : ((∑ u ∈ X, (((NY G X (π u)) \ C (π u)).map
        ⟨fun w => (u, w), fun a b h => by simpa using h⟩).card : ℕ) : ℝ) ≤
        ∑ u ∈ X, Real.sqrt 2 * (Real.sqrt ε * n) := by
      push_cast
      exact sum_le_sum (fun u hu => by rw [card_map]; exact hloss _ (hπX u hu))
    rw [sum_const, nsmul_eq_mul] at h3
    have : (((symmDiff (Hg G X π (NY G X)).edgeFinset H.edgeFinset).card : ℕ) : ℝ) ≤
        X.card * (Real.sqrt 2 * (Real.sqrt ε * n)) := le_trans (by exact_mod_cast h2) h3
    have hk : 0 ≤ Real.sqrt 2 * (Real.sqrt ε * n) := by positivity
    calc _ ≤ _ := this
      _ ≤ (n : ℝ) * (Real.sqrt 2 * (Real.sqrt ε * n)) := mul_le_mul_of_nonneg_right hXcard hk
      _ = _ := by ring
  refine ⟨H, ?_, ?_, fun u w hu hw => Hg_adj_YY hu hw⟩
  · -- chordality
    apply isChordal_of_simplicial_outside H (Xᶜ)
    · have e : H.induce ((Xᶜ : Finset (Fin n)) : Set (Fin n)) =
          G.induce ((Xᶜ : Finset (Fin n)) : Set (Fin n)) := by
        ext ⟨u, hu⟩ ⟨w, hw⟩
        simp only [SimpleGraph.comap_adj, Function.Embedding.coe_subtype]
        have hu' : u ∉ X := by simpa using hu
        have hw' : w ∉ X := by simpa using hw
        exact Hg_adj_YY hu' hw'
      rw [e]; exact hY
    · intro x hx a b ha hb hab
      have hxX : x ∈ X := by simpa using hx
      have hπx := hπX x hxX
      by_cases haX : a ∈ X <;> by_cases hbX : b ∈ X
      · rw [Hg_adj_XX hxX haX] at ha
        rw [Hg_adj_XX hxX hbX] at hb
        rw [Hg_adj_XX haX hbX]
        exact ⟨hab, ha.2.symm.trans hb.2⟩
      · rw [Hg_adj_XX hxX haX] at ha
        rw [Hg_adj_XY hxX hbX] at hb
        rw [Hg_adj_XY haX hbX, ← ha.2]; exact hb
      · rw [Hg_adj_XY hxX haX] at ha
        rw [Hg_adj_XX hxX hbX] at hb
        rw [Hg_adj_YX haX hbX, ← hb.2]; exact ha
      · rw [Hg_adj_XY hxX haX] at ha
        rw [Hg_adj_XY hxX hbX] at hb
        rw [Hg_adj_YY haX hbX]
        exact hCcl _ ha hb hab
  · -- the edit bound
    have h1 : (AlonShapira.editDist G (Hg G X π (NY G X)) : ℝ) ≤ 6 * (Real.sqrt ε * n) * n := by
      have := editDist_le_cost G X π
      have h' : (AlonShapira.editDist G (Hg G X π (NY G X)) : ℝ) ≤ cost G X π X := by
        exact_mod_cast this
      have h6 := mul_le_mul_of_nonneg_left hXcard (by positivity : (0:ℝ) ≤ 6 * (Real.sqrt ε * n))
      linarith
    have htri : AlonShapira.editDist G H ≤ AlonShapira.editDist G (Hg G X π (NY G X)) +
        AlonShapira.editDist (Hg G X π (NY G X)) H := by
      exact asEditDist_triangle _ _ _
    have hs2 : Real.sqrt 2 ≤ 2 := by
      rw [show (2 : ℝ) = Real.sqrt 4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by norm_num)
    have : (AlonShapira.editDist G H : ℝ) ≤ 6 * (Real.sqrt ε * n) * n +
        Real.sqrt 2 * (Real.sqrt ε * n) * n := by
      have := htri; push_cast [← Nat.cast_add]
      linarith [(by exact_mod_cast this : (AlonShapira.editDist G H : ℝ) ≤
        (AlonShapira.editDist G (Hg G X π (NY G X)) : ℝ) +
          (AlonShapira.editDist (Hg G X π (NY G X)) H : ℝ))]
    have hsn : 0 ≤ Real.sqrt ε * n := by positivity
    nlinarith

end E34
