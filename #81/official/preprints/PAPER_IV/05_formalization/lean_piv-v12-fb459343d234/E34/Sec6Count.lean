import E34.Sec6Claim2

/-!
# E34 — §6 of arXiv:1902.06135: the probabilistic part (Claims 3–6 and the assembly)

The sample is `ω = (pS, wU)`: `q` ordered pairs for `S` and `ℓ` blocks of `M` vertices for `U`.

* `claim6_count` (Claim 6): for fixed `U`, the proportion of `pS` with `U ∩ Y ⊄ Y_S` is at most
  `|U| (1-δ)^q` (each pair of `pS` is an induced `P₃`-witness for `u ∈ Y` with probability
  `≥ δ`).
* `count_blocks`, `count_mono`: amplification by independent blocks (Claim 4) and monotonicity
  in the sample size.
* `pinned_count` (Claims 3–4 + union over trees): for fixed `pS`, at most a fraction
  `Ncodes q / 2^ℓ` of the `wU` make `H[U]` pinned on some tree with `≤ (4q²+1)²` vertices.
* `sec6_count`: if `G` is `ε`-far from chordal and the parameters satisfy three explicit
  inequalities, then at most half of the samples `ω` induce a chordal graph.
-/

namespace E34

open Finset

open scoped Classical

variable {n : ℕ}

/-! ## Generic counting tools -/

/-- Vertex set of a block sample. -/
def uSet {ℓ M : ℕ} (wU : Fin ℓ → Fin M → Fin n) : Finset (Fin n) :=
  univ.biUnion (fun j => img (wU j))

theorem card_uSet_le {ℓ M : ℕ} (wU : Fin ℓ → Fin M → Fin n) : (uSet wU).card ≤ ℓ * M := by
  unfold uSet
  refine card_biUnion_le.trans ?_
  calc ∑ j, (img (wU j)).card ≤ ∑ _j : Fin ℓ, M := sum_le_sum (fun j _ => card_img_le _)
    _ = ℓ * M := by simp

/-- **Amplification by blocks.** -/
theorem count_blocks (P : Finset (Fin n) → Prop) (hP : ∀ A B, A ⊆ B → P B → P A) (ℓ M : ℕ) :
    (univ.filter (fun wU : Fin ℓ → Fin M → Fin n => P (uSet wU))).card ≤
      (univ.filter (fun w : Fin M → Fin n => P (img w))).card ^ ℓ := by
  set A := univ.filter (fun w : Fin M → Fin n => P (img w))
  calc (univ.filter (fun wU : Fin ℓ → Fin M → Fin n => P (uSet wU))).card
      ≤ (Fintype.piFinset (fun _ : Fin ℓ => A)).card := by
        refine card_le_card ?_
        intro wU hwU
        rw [mem_filter] at hwU
        rw [Fintype.mem_piFinset]
        intro j
        rw [mem_filter]
        refine ⟨mem_univ _, hP _ _ ?_ hwU.2⟩
        intro v hv
        exact mem_biUnion.2 ⟨j, mem_univ _, hv⟩
    _ = A.card ^ ℓ := by rw [Fintype.card_piFinset]; simp

/-- **Monotonicity in the sample size.** -/
theorem count_mono (P : Finset (Fin n) → Prop) (hP : ∀ A B, A ⊆ B → P B → P A) {m M : ℕ}
    (hmM : m ≤ M) :
    (univ.filter (fun w : Fin M → Fin n => P (img w))).card ≤
      (univ.filter (fun w : Fin m → Fin n => P (img w))).card * n ^ (M - m) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hmM
  rw [Nat.add_sub_cancel_left]
  have e := card_append (n := n) m r (fun u v => P (img (Fin.append u v)))
  simp only [Fin.append_castAdd_natAdd] at e
  rw [e]
  calc (univ.filter (fun p : (Fin m → Fin n) × (Fin r → Fin n) =>
        P (img (Fin.append p.1 p.2)))).card
      ≤ (univ.filter (fun p : (Fin m → Fin n) × (Fin r → Fin n) => P (img p.1))).card := by
        refine card_le_card (fun p hp => ?_)
        rw [mem_filter] at hp ⊢
        refine ⟨mem_univ _, hP _ _ ?_ hp.2⟩
        rw [img_append]; exact subset_union_left
    _ = (univ.filter (fun w : Fin m → Fin n => P (img w))).card * n ^ r := by
        rw [card_filter_prod_eq_sum_left (fun a (_ : Fin r → Fin n) => P (img a)),
          card_filter (fun w => P (img w)), sum_mul]
        refine sum_congr rfl (fun a _ => ?_)
        by_cases h : P (img a) <;> simp [h]

/-! ## Claim 6 -/

/-- Pairs that are *not* a witness for `u`. -/
noncomputable def badPairs (G : SimpleGraph (Fin n)) (u : Fin n) : Finset (Fin n × Fin n) :=
  (univ ×ˢ univ).filter (fun p : Fin n × Fin n =>
    ¬ (p.1 ≠ p.2 ∧ G.Adj u p.1 ∧ G.Adj u p.2 ∧ ¬ G.Adj p.1 p.2))

theorem card_badPairs (G : SimpleGraph (Fin n)) (u : Fin n) :
    (badPairs G u).card + pOrd G u = n ^ 2 := by
  unfold badPairs pOrd
  rw [add_comm, card_filter_add_card_filter_not]
  simp [sq]

theorem card_badPairs_le (G : SimpleGraph (Fin n)) (δ : ℝ) (u : Fin n) (hu : u ∉ lowSet G δ) :
    ((badPairs G u).card : ℝ) ≤ (1 - δ) * (n : ℝ) ^ 2 := by
  have h1 := card_badPairs G u
  have h2 : ¬ ((pG G u : ℝ) ≤ δ / 2 * (n : ℝ) ^ 2) := by
    intro h; exact hu (mem_filter.2 ⟨mem_univ _, h⟩)
  have h3 := pOrd_eq G u
  have h4 : ((badPairs G u).card : ℝ) + pOrd G u = (n : ℝ) ^ 2 := by exact_mod_cast h1
  have h5 : (pOrd G u : ℝ) = 2 * pG G u := by exact_mod_cast h3
  push_neg at h2
  nlinarith

/-- **Claim 6** (counting form). -/
theorem claim6_count (G : SimpleGraph (Fin n)) (δ : ℝ) (hδ1 : δ ≤ 1) (U : Finset (Fin n)) (q : ℕ) :
    ((univ.filter (fun pS : Fin q → Fin n × Fin n =>
      ∃ u ∈ U, u ∉ lowSet G δ ∧ ¬ InYS G pS u)).card : ℝ) ≤
      U.card * ((1 - δ) * (n : ℝ) ^ 2) ^ q := by
  have hsub : univ.filter (fun pS : Fin q → Fin n × Fin n =>
      ∃ u ∈ U, u ∉ lowSet G δ ∧ ¬ InYS G pS u) ⊆
      (U.filter (fun u => u ∉ lowSet G δ)).biUnion
        (fun u => Fintype.piFinset (fun _ : Fin q => badPairs G u)) := by
    intro pS hpS
    obtain ⟨u, hu, hX, hY⟩ := (mem_filter.1 hpS).2
    refine mem_biUnion.2 ⟨u, mem_filter.2 ⟨hu, hX⟩, ?_⟩
    rw [Fintype.mem_piFinset]
    intro i
    simp only [badPairs, mem_filter, mem_product, mem_univ, true_and]
    rintro ⟨h1, h2, h3, h4⟩
    apply hY
    refine ⟨((i, false), (i, true)), ?_⟩
    simp only [Valid, sPt, Bool.false_eq_true, if_false, if_true]
    exact ⟨h2, h3, h1, h4⟩
  have hc := (card_le_card hsub).trans card_biUnion_le
  have hc' : ((univ.filter (fun pS : Fin q → Fin n × Fin n =>
      ∃ u ∈ U, u ∉ lowSet G δ ∧ ¬ InYS G pS u)).card : ℝ) ≤
      ∑ u ∈ U.filter (fun u => u ∉ lowSet G δ), ((badPairs G u).card : ℝ) ^ q := by
    have : ∀ u, (Fintype.piFinset (fun _ : Fin q => badPairs G u)).card =
        (badPairs G u).card ^ q := by
      intro u; rw [Fintype.card_piFinset]; simp
    simp only [this] at hc
    exact_mod_cast hc
  refine hc'.trans ?_
  calc ∑ u ∈ U.filter (fun u => u ∉ lowSet G δ), ((badPairs G u).card : ℝ) ^ q
      ≤ ∑ _u ∈ U.filter (fun u => u ∉ lowSet G δ), ((1 - δ) * (n : ℝ) ^ 2) ^ q := by
        refine sum_le_sum (fun u hu => ?_)
        exact pow_le_pow_left₀ (by positivity) (card_badPairs_le G δ u (mem_filter.1 hu).2) q
    _ ≤ ∑ _u ∈ U, ((1 - δ) * (n : ℝ) ^ 2) ^ q := by
        have h0 : 0 ≤ ((1 - δ) * (n : ℝ) ^ 2) := mul_nonneg (by linarith) (by positivity)
        exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => pow_nonneg h0 q)
    _ = U.card * ((1 - δ) * (n : ℝ) ^ 2) ^ q := by rw [sum_const, nsmul_eq_mul]

/-! ## Claims 3–4 and the union over trees -/

/-- Maximal number of vertices of the compressed trees. -/
def kMax (q : ℕ) : ℕ := (4 * q ^ 2 + 1) ^ 2

/-- Number of codes `(K0, parent map, pins)` with `K0 ≤ kMax q`. -/
def nCodes (q : ℕ) : ℕ := ∑ K0 ∈ range (kMax q + 1), K0 ^ K0 * K0 ^ (4 * q ^ 2 + 1)

theorem card_pos_labels (q : ℕ) : Fintype.card (Option (Pos q × Pos q)) = 4 * q ^ 2 + 1 := by
  simp [Fintype.card_option, Fintype.card_prod, Fintype.card_bool]; ring

/-- One tree, one pin map: amplified Lemma 11. -/
theorem pinned_count_one (m11 : ℝ → ℕ → ℕ) (hL : Lemma11With m11) (ε' : ℝ) (hε' : 0 < ε')
    (H : SimpleGraph (Fin n))
    (hfar : ∀ F : SimpleGraph (Fin n), AlonShapira.IsChordal F →
      ε' * (n : ℝ) ^ 2 < (AlonShapira.editDist H F : ℝ))
    {K0 : ℕ} (Γ : RTree K0) (x : Fin n → Fin K0) (ℓ M : ℕ) (hM : m11 ε' K0 ≤ M) :
    2 ^ ℓ * (univ.filter (fun wU : Fin ℓ → Fin M → Fin n =>
      PinnedOn Γ x H (uSet wU))).card ≤ n ^ (M * ℓ) := by
  have hdown : ∀ A B : Finset (Fin n), A ⊆ B → PinnedOn Γ x H B → PinnedOn Γ x H A :=
    fun A B hAB h => h.mono hAB
  have h1 := hL ε' hε' K0 Γ n H x hfar
  have h2 := count_mono (fun U => PinnedOn Γ x H U) hdown hM
  have h3 : 2 * (univ.filter (fun w : Fin M → Fin n => PinnedOn Γ x H (img w))).card ≤ n ^ M := by
    calc 2 * (univ.filter (fun w : Fin M → Fin n => PinnedOn Γ x H (img w))).card
        ≤ 2 * ((univ.filter (fun w : Fin (m11 ε' K0) → Fin n => PinnedOn Γ x H (img w))).card *
          n ^ (M - m11 ε' K0)) := Nat.mul_le_mul_left _ h2
      _ = (2 * (univ.filter (fun w : Fin (m11 ε' K0) → Fin n =>
            PinnedOn Γ x H (img w))).card) * n ^ (M - m11 ε' K0) := by ring
      _ ≤ n ^ (m11 ε' K0) * n ^ (M - m11 ε' K0) := Nat.mul_le_mul_right _ h1
      _ = n ^ M := by rw [← pow_add, Nat.add_sub_cancel' hM]
  have h4 := count_blocks (fun U => PinnedOn Γ x H U) hdown ℓ M
  calc 2 ^ ℓ * (univ.filter (fun wU : Fin ℓ → Fin M → Fin n => PinnedOn Γ x H (uSet wU))).card
      ≤ 2 ^ ℓ * (univ.filter (fun w : Fin M → Fin n => PinnedOn Γ x H (img w))).card ^ ℓ :=
        Nat.mul_le_mul_left _ h4
    _ = (2 * (univ.filter (fun w : Fin M → Fin n => PinnedOn Γ x H (img w))).card) ^ ℓ := by
        rw [mul_pow]
    _ ≤ (n ^ M) ^ ℓ := Nat.pow_le_pow_left h3 ℓ
    _ = n ^ (M * ℓ) := by rw [← pow_mul]

/-- **Claims 3–4 + union bound over the compressed trees.** -/
theorem pinned_count (m11 : ℝ → ℕ → ℕ) (hL : Lemma11With m11) (ε' : ℝ) (hε' : 0 < ε')
    (H : SimpleGraph (Fin n))
    (hfar : ∀ F : SimpleGraph (Fin n), AlonShapira.IsChordal F →
      ε' * (n : ℝ) ^ 2 < (AlonShapira.editDist H F : ℝ))
    (q ℓ M : ℕ) (hM : ∀ K0 ≤ kMax q, m11 ε' K0 ≤ M) (lb : Fin n → Option (Pos q × Pos q)) :
    2 ^ ℓ * (univ.filter (fun wU : Fin ℓ → Fin M → Fin n =>
      ∃ K0, K0 ≤ kMax q ∧ ∃ Γ : RTree K0, ∃ y : Option (Pos q × Pos q) → Fin K0,
        PinnedOn Γ (fun u => y (lb u)) H (uSet wU))).card ≤ nCodes q * n ^ (M * ℓ) := by
  let inner : (K0 : ℕ) → (Fin K0 → Fin K0) × (Option (Pos q × Pos q) → Fin K0) →
      Finset (Fin ℓ → Fin M → Fin n) := fun K0 c =>
    univ.filter (fun wU => ∃ Γ : RTree K0, Γ.par = c.1 ∧ PinnedOn Γ (fun u => c.2 (lb u)) H (uSet wU))
  have hsub : univ.filter (fun wU : Fin ℓ → Fin M → Fin n =>
      ∃ K0, K0 ≤ kMax q ∧ ∃ Γ : RTree K0, ∃ y : Option (Pos q × Pos q) → Fin K0,
        PinnedOn Γ (fun u => y (lb u)) H (uSet wU)) ⊆
      (range (kMax q + 1)).biUnion (fun K0 => univ.biUnion (fun c => inner K0 c)) := by
    intro wU hwU
    obtain ⟨K0, hK0, Γ, y, hp⟩ := (mem_filter.1 hwU).2
    refine mem_biUnion.2 ⟨K0, mem_range.2 (by omega), mem_biUnion.2 ⟨(Γ.par, y), mem_univ _, ?_⟩⟩
    exact mem_filter.2 ⟨mem_univ _, Γ, rfl, hp⟩
  have hinner : ∀ K0, K0 ≤ kMax q → ∀ c, 2 ^ ℓ * (inner K0 c).card ≤ n ^ (M * ℓ) := by
    intro K0 hK0 c
    by_cases hex : ∃ Γ0 : RTree K0, Γ0.par = c.1
    · obtain ⟨Γ0, hΓ0⟩ := hex
      refine le_trans (Nat.mul_le_mul_left _ (card_le_card ?_))
        (pinned_count_one m11 hL ε' hε' H hfar Γ0 (fun u => c.2 (lb u)) ℓ M (hM K0 hK0))
      intro wU hwU
      obtain ⟨Γ, hΓ, hp⟩ := (mem_filter.1 hwU).2
      refine mem_filter.2 ⟨mem_univ _, ?_⟩
      exact (pinnedOn_congr (hΓ.trans hΓ0.symm) _ _ _).1 hp
    · have : inner K0 c = ∅ := by
        rw [filter_eq_empty_iff]
        rintro wU - ⟨Γ, hΓ, -⟩
        exact hex ⟨Γ, hΓ⟩
      rw [this]; simp
  calc 2 ^ ℓ * (univ.filter (fun wU : Fin ℓ → Fin M → Fin n =>
        ∃ K0, K0 ≤ kMax q ∧ ∃ Γ : RTree K0, ∃ y : Option (Pos q × Pos q) → Fin K0,
          PinnedOn Γ (fun u => y (lb u)) H (uSet wU))).card
      ≤ 2 ^ ℓ * ∑ K0 ∈ range (kMax q + 1), ∑ c, (inner K0 c).card := by
        refine Nat.mul_le_mul_left _ ((card_le_card hsub).trans (card_biUnion_le.trans ?_))
        exact sum_le_sum (fun K0 _ => card_biUnion_le)
    _ = ∑ K0 ∈ range (kMax q + 1), ∑ c, 2 ^ ℓ * (inner K0 c).card := by
        rw [mul_sum]; exact sum_congr rfl (fun K0 _ => by rw [mul_sum])
    _ ≤ ∑ K0 ∈ range (kMax q + 1), ∑ _c : (Fin K0 → Fin K0) × (Option (Pos q × Pos q) → Fin K0),
          n ^ (M * ℓ) := by
        refine sum_le_sum (fun K0 hK0 => sum_le_sum (fun c _ => hinner K0 ?_ c))
        rw [mem_range] at hK0; omega
    _ = nCodes q * n ^ (M * ℓ) := by
        rw [nCodes, sum_mul]
        refine sum_congr rfl (fun K0 _ => ?_)
        rw [sum_const, card_univ, smul_eq_mul, Fintype.card_prod, Fintype.card_fun,
          Fintype.card_fun, card_pos_labels, Fintype.card_fin]


end E34
