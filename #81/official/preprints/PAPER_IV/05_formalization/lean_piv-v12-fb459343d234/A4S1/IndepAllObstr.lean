import A4S1.IndepAllBounds

/-!
# E14 (copied from E10 `A4S1.OwnAllObstr`, no forbidden import)
# E10, own terminal for every rooted defect `s`: obstruction `(O_s)`, Erdős–Gallai for the core,
joint incidence

* `AllInput.no_core_pairs` — **(O_s) on the core**: the core does not contain `s + 1` disjoint
  non-adjacent pairs. Their `2s + 2` endpoints have more than `ω + s` common light neighbours
  (each core vertex misses at most `w/40` light vertices), and the endpoints together with these
  common neighbours form a vertex set in which every vertex has defect `≥ s + 1`.
* `AllInput.exists_nu` — `ν ≤ s` with `ν` disjoint non-adjacent pairs in the core but not
  `ν + 1`; with `erdos_gallai`, `M ≤ ν c − C(ν+1,2)` (`AllInput.core_eg`).
* `AllInput.joint` — **joint incidence**: for a family `P` of `ν` disjoint non-adjacent pairs in
  the core and at most `2s + 2` exceptional vertices `X`,
  `Σ_{t ∈ X} |N(t) ∩ pL| ≤ (s − ν)|pL| + n/9` (by `joint_peel`).
-/

namespace A4S1.IndepAll

open Finset PaperIV.FarRounding PaperIV.RootedSimplicialDefect A4S1.TerminalPacking

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {A : Finset V} {s : ℕ}

omit [Fintype V] [DecidableEq V] in
theorem all_sum_card_filter_comm (X Z : Finset V) :
    ∑ t ∈ X, (Z.filter (G.Adj t)).card = ∑ z ∈ Z, (X.filter (G.Adj z)).card := by
  simp only [card_filter]
  rw [sum_comm]
  refine sum_congr rfl fun z _ => sum_congr rfl fun t _ => ?_
  by_cases hzt : G.Adj z t
  · simp [hzt, hzt.symm]
  · have : ¬ G.Adj t z := fun h' => hzt h'.symm
    simp [hzt, this]

/-- The vertices of `L` adjacent to all of `B` miss at most `Σ_{e ∈ B} |L ∖ N(e)|` of `L`. -/
theorem all_card_common (L B : Finset V) :
    (L.card : ℚ) ≤ ((L.filter fun z => ∀ e ∈ B, G.Adj z e).card : ℚ) +
      ∑ e ∈ B, ((L.filter fun z => ¬ G.Adj e z).card : ℚ) := by
  have hsub : L ⊆ (L.filter fun z => ∀ e ∈ B, G.Adj z e) ∪
      B.biUnion (fun e => L.filter fun z => ¬ G.Adj e z) := by
    intro z hz
    by_cases hall : ∀ e ∈ B, G.Adj z e
    · exact mem_union_left _ (mem_filter.2 ⟨hz, hall⟩)
    · push_neg at hall
      obtain ⟨e, he, hne⟩ := hall
      exact mem_union_right _ (mem_biUnion.2 ⟨e, he, mem_filter.2 ⟨hz, fun h' => hne h'.symm⟩⟩)
  have h1 := card_le_card hsub
  have h2 := card_union_le (L.filter fun z => ∀ e ∈ B, G.Adj z e)
    (B.biUnion (fun e => L.filter fun z => ¬ G.Adj e z))
  have h3 := card_biUnion_le (s := B) (t := fun e => L.filter fun z => ¬ G.Adj e z)
  have : L.card ≤ (L.filter fun z => ∀ e ∈ B, G.Adj z e).card +
      ∑ e ∈ B, (L.filter fun z => ¬ G.Adj e z).card := by omega
  exact_mod_cast this

variable (h : AllInput G A s)
include h

theorem AllInput.Sw_le_n : ((s : ℚ) + 1) * scW V s ≤ Fintype.card V := by
  have h1 := scW_mul (V := V) (s := s)
  have h2 := (S_ge_one (s := s))
  have h3 : 0 ≤ scW V s := (h.v_pos.trans_le h.v_le_w).le
  nlinarith

theorem AllInput.S_le_w : ((s : ℚ) + 1) ^ 2 ≤ scW V s / 10 ^ 50 := by
  have h1 := h.v_big
  have h2 := scV_mul (V := V) (s := s)
  have h3 : ((s : ℚ) + 1) ^ 2 ≤ ((s : ℚ) + 1) ^ 4 := pow_le_pow_right₀ (S_ge_one (s := s)) (by norm_num)
  have h4 : 0 ≤ ((s : ℚ) + 1) ^ 2 := by positivity
  rw [le_div_iff₀ (by positivity)]
  nlinarith

theorem AllInput.S_le_w' : (s : ℚ) + 1 ≤ scW V s / 10 ^ 50 := by
  have h1 := h.S_le_w
  have h2 := (S_ge_one (s := s))
  nlinarith

/-- The clique bound for light vertices, as a natural number. -/
theorem AllInput.L_clique_nat {K : Finset V} (hK : K ⊆ pL G A s)
    (hKc : G.IsClique (K : Set V)) : K.card ≤ ⌈scW V s / 10 ^ 4⌉₊ := by
  have h1 := h.L_clique hK hKc
  have h2 : scW V s / 10 ^ 4 ≤ (⌈scW V s / 10 ^ 4⌉₊ : ℚ) := Nat.le_ceil _
  have : (K.card : ℚ) < (⌈scW V s / 10 ^ 4⌉₊ : ℚ) + 1 := by linarith
  exact_mod_cast Nat.lt_add_one_iff.1 (by exact_mod_cast this)

theorem AllInput.ceil_le : ((⌈scW V s / 10 ^ 4⌉₊ : ℕ) : ℚ) ≤ scW V s / 10 ^ 4 + 1 := by
  have hw : 0 ≤ scW V s / 10 ^ 4 := div_nonneg (h.v_pos.le.trans h.v_le_w) (by norm_num)
  exact (Nat.ceil_lt_add_one hw).le

omit h in
theorem pends_sub_core {P : Finset (V × V)} (hPc : ∀ p ∈ P, p.1 ∈ pCore G A s ∧
    p.2 ∈ pCore G A s ∧ ¬ G.Adj p.1 p.2) : pends P ⊆ pCore G A s := by
  intro e he
  obtain ⟨p, hp, h1 | h1⟩ := mem_pends.1 he
  · exact h1 ▸ (hPc p hp).1
  · exact h1 ▸ (hPc p hp).2.1

theorem AllInput.sum_miss_pends {B : Finset V} (hB : B ⊆ pCore G A s) :
    ∑ e ∈ B, (((pL G A s).filter fun z => ¬ G.Adj e z).card : ℚ) ≤ B.card * (scW V s / 40) := by
  have := sum_le_sum fun e (he : e ∈ B) => h.core_miss_L (hB he)
  rw [sum_const, nsmul_eq_mul] at this
  exact this

omit h in
theorem pL_core_disjoint : Disjoint (pL G A s) (pCore G A s) :=
  disjoint_left.2 fun _ hz hc =>
    disjoint_left.1 core_host_disjoint hc (mem_pHost.2 (Or.inl hz))

omit h in
theorem pL_T_disjoint : Disjoint (pL G A s) (pT G A s) :=
  disjoint_left.2 fun _ hz ht =>
    disjoint_left.1 host_T_disjoint (mem_pHost.2 (Or.inl hz)) ht

/-- **(O_s) on the core.** -/
theorem AllInput.no_core_pairs : ¬ HasMissPairs G (pCore G A s) (s + 1) := by
  rintro ⟨P, hP, hPc, hPm⟩
  have hB := pends_sub_core hPm
  set Com := (pL G A s).filter fun z => ∀ e ∈ pends P, G.Adj z e with hCom
  have hcom := all_card_common (G := G) (pL G A s) (pends P)
  have hmiss := h.sum_miss_pends hB
  have hpe : ((pends P).card : ℚ) ≤ 2 * ((s : ℚ) + 1) := by
    have := card_pends_le P
    rw [hPc] at this
    have h' : ((pends P).card : ℚ) ≤ ((2 * (s + 1) : ℕ) : ℚ) := by exact_mod_cast this
    push_cast at h'
    exact h'
  have hLlo := h.card_L_lo
  have hSw := h.Sw_le_n
  have hSw2 := h.S_le_w'
  have hv := h.v_pos; have hvw := h.v_le_w; have hwn := h.w_le_n
  have hw0 : 0 ≤ scW V s := hv.le.trans hvw
  have hmul : ((pends P).card : ℚ) * (scW V s / 40) ≤ 2 * ((s : ℚ) + 1) * (scW V s / 40) :=
    mul_le_mul_of_nonneg_right hpe (by positivity)
  have hComQ : scW V s / 10 ^ 4 + 1 + (s : ℚ) + 1 ≤ (Com.card : ℚ) := by nlinarith
  have hComL : Com ⊆ pL G A s := filter_subset _ _
  have hdisj : Disjoint (pends P) Com :=
    disjoint_left.2 fun e he hc => disjoint_left.1 pL_core_disjoint (hComL hc) (hB he)
  apply not_rootedDefect_of_rich h.rd (pends P ∪ Com)
  · obtain ⟨z, hz⟩ : Com.Nonempty := by
      rw [← card_pos]; have : (0 : ℚ) < Com.card := by linarith
      exact_mod_cast this
    exact ⟨z, mem_union_right _ hz⟩
  intro v hv C hCsub hC
  rcases mem_union.1 hv with hvP | hvC
  · -- an endpoint sees all of `Com`
    have hsub : Com ⊆ neighborsIn G (pends P ∪ Com) v := fun z hz =>
      mem_neighborsIn.2 ⟨mem_union_right _ hz, ((mem_filter.1 hz).2 v hvP).symm⟩
    have h1 : Com.card ≤ (Com \ C).card + (Com ∩ C).card := by
      rw [← card_union_of_disjoint (disjoint_sdiff_inter Com C), sdiff_union_inter]
    have h2 : (Com \ C).card ≤ (neighborsIn G (pends P ∪ Com) v \ C).card :=
      card_le_card (sdiff_subset_sdiff hsub (subset_refl _))
    have h3 := h.L_clique (K := Com ∩ C) (inter_subset_left.trans hComL)
      (hC.subset (by simp))
    have h1q : (Com.card : ℚ) ≤ (Com \ C).card + (Com ∩ C).card := by exact_mod_cast h1
    have h2q : ((Com \ C).card : ℚ) ≤ (neighborsIn G (pends P ∪ Com) v \ C).card := by
      exact_mod_cast h2
    have : ((s + 1 : ℕ) : ℚ) ≤ (neighborsIn G (pends P ∪ Com) v \ C).card := by
      push_cast; linarith
    exact_mod_cast this
  · -- a common neighbour sees all endpoints
    have := card_le_sdiff_of_pairs (N := neighborsIn G (pends P ∪ Com) v) hP
      (fun p hp => (hPm p hp).2.2) (fun p hp =>
        ⟨mem_neighborsIn.2 ⟨mem_union_left _ (fst_mem_pends hp),
          (mem_filter.1 hvC).2 _ (fst_mem_pends hp)⟩,
         mem_neighborsIn.2 ⟨mem_union_left _ (snd_mem_pends hp),
          (mem_filter.1 hvC).2 _ (snd_mem_pends hp)⟩⟩) hC
    omega

/-- The matching number `ν ≤ s` of the complement of the core. -/
theorem AllInput.exists_nu : ∃ ν ≤ s, HasMissPairs G (pCore G A s) ν ∧
    ¬ HasMissPairs G (pCore G A s) (ν + 1) := by
  classical
  have hex : ∃ m, ¬ HasMissPairs G (pCore G A s) (m + 1) := ⟨s, h.no_core_pairs⟩
  set m := Nat.find hex with hm
  have hspec : ¬ HasMissPairs G (pCore G A s) (m + 1) := Nat.find_spec hex
  have hle : m ≤ s := Nat.find_min' hex h.no_core_pairs
  refine ⟨m, hle, ?_, hspec⟩
  rcases hm0 : m with _ | m'
  · exact hasMissPairs_zero _
  · have hlt : m' < m := by omega
    have := Nat.find_min hex (hm ▸ hlt)
    push_neg at this
    exact this

theorem AllInput.card_core_ge (ν : ℕ) (hν : ν ≤ s) : 5 * ν + 1 ≤ (pCore G A s).card := by
  have h1 := h.card_core_lo
  have h2 := h.S_le_w'
  have hv := h.v_pos; have hvw := h.v_le_w; have hwn := h.w_le_n
  have hνq : (ν : ℚ) ≤ s := by exact_mod_cast hν
  have : ((5 * ν + 1 : ℕ) : ℚ) ≤ (pCore G A s).card := by push_cast; linarith
  exact_mod_cast this

/-- **Erdős–Gallai for the core.** -/
theorem AllInput.core_eg {ν : ℕ} (hν : ν ≤ s) (hno : ¬ HasMissPairs G (pCore G A s) (ν + 1)) :
    (pCore G A s).card.choose 2 + (ν + 1).choose 2 ≤
      (inEdges G (pCore G A s)).card + ν * (pCore G A s).card :=
  erdos_gallai ν (pCore G A s) (h.card_core_ge ν hν) hno

/-- **Joint incidence.** -/
theorem AllInput.joint {P : Finset (V × V)} (hP : IsPairFam P)
    (hPm : ∀ p ∈ P, p.1 ∈ pCore G A s ∧ p.2 ∈ pCore G A s ∧ ¬ G.Adj p.1 p.2)
    (hPs : P.card ≤ s) (X : Finset V) (hX : X ⊆ pT G A s) (hXc : X.card ≤ 2 * (s + 1)) :
    ∑ t ∈ X, (((pL G A s).filter (G.Adj t)).card : ℚ) ≤
      ((s - P.card : ℕ) : ℚ) * (pL G A s).card + Fintype.card V / 9 := by
  have hB := pends_sub_core hPm
  have hv := h.v_pos; have hvw := h.v_le_w; have hwn := h.w_le_n
  have hw0 : 0 ≤ scW V s := hv.le.trans hvw
  have hSw := h.Sw_le_n
  have hSw2 := h.S_le_w'
  have hSS := h.S_le_w
  have hS1 := (S_ge_one (s := s))
  have hpe : ((pends P).card : ℚ) ≤ 2 * (s : ℚ) := by
    have := card_pends_le P
    have : (pends P).card ≤ 2 * s := by omega
    exact_mod_cast this
  have hXq : (X.card : ℚ) ≤ 2 * ((s : ℚ) + 1) := by exact_mod_cast hXc
  -- distinct non-neighbours in the pruned clique
  obtain ⟨c, hc, hcinj⟩ := exists_sdr (pends P) (fun t => (pA0 G A s).filter fun a => ¬ G.Adj t a)
    X (fun t ht => by
      have h1 := pT_miss_A0 (hX ht)
      have : ((pends P).card : ℚ) + X.card < (((pA0 G A s).filter fun a => ¬ G.Adj t a).card : ℚ) := by
        nlinarith
      exact_mod_cast this)
  have hcA : ∀ t ∈ X, c t ∈ pA0 G A s := fun t ht => (mem_filter.1 (hc t ht).1).1
  have hcn : ∀ t ∈ X, ¬ G.Adj t (c t) := fun t ht => (mem_filter.1 (hc t ht).1).2
  set W := pends P ∪ X.image c with hW
  have hWcore : W ⊆ pCore G A s := by
    intro e he
    rcases mem_union.1 he with he | he
    · exact hB he
    · obtain ⟨t, ht, rfl⟩ := mem_image.1 he
      exact mem_pCore.2 (Or.inl (hcA t ht))
  set Z := (pL G A s).filter fun z => ∀ e ∈ W, G.Adj z e with hZ
  have hZL : Z ⊆ pL G A s := filter_subset _ _
  set ω := ⌈scW V s / 10 ^ 4⌉₊ with hω
  have hpeel := joint_peel h.rd Z X P c ω hP (fun p hp => (hPm p hp).2.2) hPs hcn hcinj
    (disjoint_left.2 fun z hz ht => disjoint_left.1 pL_T_disjoint (hZL hz) (hX ht))
    (disjoint_left.2 fun z hz hw => disjoint_left.1 pL_core_disjoint (hZL hz) (hWcore hw))
    (disjoint_left.2 fun t ht hw => disjoint_left.1 core_T_disjoint (hWcore hw) (hX ht))
    (disjoint_left.2 fun e he he' => by
      obtain ⟨t, ht, rfl⟩ := mem_image.1 he'
      exact (hc t ht).2 he)
    (fun z hz => (mem_filter.1 hz).2)
    (fun K hK hKc => h.L_clique_nat (hK.trans hZL) hKc)
  rw [← all_sum_card_filter_comm] at hpeel
  -- rows outside `Z`
  have hcom := all_card_common (G := G) (pL G A s) W
  have hWsum : ∑ e ∈ W, (((pL G A s).filter fun z => ¬ G.Adj e z).card : ℚ) ≤
      (pends P).card * (scW V s / 40) + X.card * (scV V s / 10 ^ 10) := by
    have e1 : ∑ e ∈ W, (((pL G A s).filter fun z => ¬ G.Adj e z).card : ℚ) ≤
        ∑ e ∈ pends P, (((pL G A s).filter fun z => ¬ G.Adj e z).card : ℚ) +
          ∑ e ∈ X.image c, (((pL G A s).filter fun z => ¬ G.Adj e z).card : ℚ) :=
      by
        have := sum_union_inter (s₁ := pends P) (s₂ := X.image c)
          (f := fun e => (((pL G A s).filter fun z => ¬ G.Adj e z).card : ℚ))
        have h0 : (0 : ℚ) ≤ ∑ e ∈ pends P ∩ X.image c,
            (((pL G A s).filter fun z => ¬ G.Adj e z).card : ℚ) := sum_nonneg fun _ _ => by positivity
        linarith
    have e2 := h.sum_miss_pends hB
    have e3 : ∑ e ∈ X.image c, (((pL G A s).filter fun z => ¬ G.Adj e z).card : ℚ) ≤
        ∑ _e ∈ X.image c, scV V s / 10 ^ 10 := by
      refine sum_le_sum fun e he => ?_
      obtain ⟨t, ht, rfl⟩ := mem_image.1 he
      exact h.A0_miss_L (hcA t ht)
    rw [sum_const, nsmul_eq_mul] at e3
    have e4 : ((X.image c).card : ℚ) ≤ X.card := by exact_mod_cast card_image_le
    have e5 : ((X.image c).card : ℚ) * (scV V s / 10 ^ 10) ≤ X.card * (scV V s / 10 ^ 10) :=
      mul_le_mul_of_nonneg_right e4 (by positivity)
    linarith
  have hLZ : ((pL G A s).card : ℚ) - Z.card ≤
      (pends P).card * (scW V s / 40) + X.card * (scV V s / 10 ^ 10) := by linarith
  have hper : ∀ t ∈ X, (((pL G A s).filter (G.Adj t)).card : ℚ) ≤
      ((Z.filter (G.Adj t)).card : ℚ) + ((pL G A s).card - Z.card) := by
    intro t _
    have hsub : (pL G A s).filter (G.Adj t) ⊆ Z.filter (G.Adj t) ∪ (pL G A s \ Z) := by
      intro z hz
      by_cases hzZ : z ∈ Z
      · exact mem_union_left _ (mem_filter.2 ⟨hzZ, (mem_filter.1 hz).2⟩)
      · exact mem_union_right _ (mem_sdiff.2 ⟨(mem_filter.1 hz).1, hzZ⟩)
    have e1 := (card_le_card hsub).trans (card_union_le _ _)
    rw [card_sdiff_of_subset hZL] at e1
    have e2 := card_le_card hZL
    have : (((pL G A s).filter (G.Adj t)).card : ℚ) ≤
        ((Z.filter (G.Adj t)).card : ℚ) + (((pL G A s).card - Z.card : ℕ) : ℚ) := by
      exact_mod_cast e1
    rw [Nat.cast_sub e2] at this
    exact this
  have hsum := sum_le_sum hper
  rw [sum_add_distrib, sum_const, nsmul_eq_mul] at hsum
  have hpeelq : ∑ t ∈ X, ((Z.filter (G.Adj t)).card : ℚ) ≤
      ((s - P.card : ℕ) : ℚ) * Z.card + 2 * ((ω : ℚ) + s) * X.card := by
    exact_mod_cast hpeel
  have hZle : (Z.card : ℚ) ≤ (pL G A s).card := by exact_mod_cast card_le_card hZL
  have hsP : (0 : ℚ) ≤ ((s - P.card : ℕ) : ℚ) := by positivity
  have hω1 := h.ceil_le
  rw [← hω] at hω1
  have hX0 : (0 : ℚ) ≤ X.card := by positivity
  -- error terms
  have t1 : ((s - P.card : ℕ) : ℚ) * Z.card ≤ ((s - P.card : ℕ) : ℚ) * (pL G A s).card :=
    mul_le_mul_of_nonneg_left hZle hsP
  have t2 : 2 * ((ω : ℚ) + s) * X.card ≤ 2 * (scW V s / 10 ^ 4 + 1 + s) * (2 * ((s : ℚ) + 1)) := by
    have hω0 : (0 : ℚ) ≤ ω := by positivity
    apply mul_le_mul (by linarith) hXq hX0 (by positivity)
  have t3 : (X.card : ℚ) * ((pL G A s).card - Z.card) ≤
      (2 * ((s : ℚ) + 1)) * (2 * (s : ℚ) * (scW V s / 40)) +
        (2 * ((s : ℚ) + 1)) * (2 * ((s : ℚ) + 1) * (scV V s / 10 ^ 10)) := by
    have hLZ0 : (0 : ℚ) ≤ (pL G A s).card - Z.card := by linarith
    have hb : ((pL G A s).card : ℚ) - Z.card ≤
        2 * (s : ℚ) * (scW V s / 40) + 2 * ((s : ℚ) + 1) * (scV V s / 10 ^ 10) := by
      have m1 : ((pends P).card : ℚ) * (scW V s / 40) ≤ 2 * (s : ℚ) * (scW V s / 40) :=
        mul_le_mul_of_nonneg_right hpe (by positivity)
      have m2 : (X.card : ℚ) * (scV V s / 10 ^ 10) ≤ 2 * ((s : ℚ) + 1) * (scV V s / 10 ^ 10) :=
        mul_le_mul_of_nonneg_right hXq (by positivity)
      linarith
    have := mul_le_mul hXq hb hLZ0 (by positivity)
    linarith [this, mul_add (2 * ((s : ℚ) + 1)) (2 * (s : ℚ) * (scW V s / 40))
      (2 * ((s : ℚ) + 1) * (scV V s / 10 ^ 10))]
  -- `S² w = n`, `S² v = w`
  have hn_eq := scW_mul (V := V) (s := s)
  have hw_eq := scV_mul (V := V) (s := s)
  have hsS : (s : ℚ) ≤ (s : ℚ) + 1 := by linarith
  have k1 : (2 * ((s : ℚ) + 1)) * (2 * (s : ℚ) * (scW V s / 40)) ≤ Fintype.card V / 10 := by
    have e1 : (s : ℚ) * scW V s ≤ ((s : ℚ) + 1) * scW V s := mul_le_mul_of_nonneg_right hsS hw0
    have e2 : ((s : ℚ) * scW V s) * ((s : ℚ) + 1) ≤ (((s : ℚ) + 1) * scW V s) * ((s : ℚ) + 1) :=
      mul_le_mul_of_nonneg_right e1 (by positivity)
    have e3 : (2 * ((s : ℚ) + 1)) * (2 * (s : ℚ) * (scW V s / 40)) =
        ((s : ℚ) * scW V s) * ((s : ℚ) + 1) / 10 := by ring
    have e4 : (((s : ℚ) + 1) * scW V s) * ((s : ℚ) + 1) = scW V s * ((s : ℚ) + 1) ^ 2 := by ring
    rw [e3]
    rw [e4, hn_eq] at e2
    linarith
  have k2 : (2 * ((s : ℚ) + 1)) * (2 * ((s : ℚ) + 1) * (scV V s / 10 ^ 10)) =
      4 * (scW V s / 10 ^ 10) := by
    rw [← hw_eq]; ring
  have k3 : 2 * (scW V s / 10 ^ 4 + 1 + s) * (2 * ((s : ℚ) + 1)) ≤
      4 * (Fintype.card V / 10 ^ 4) + 4 * (scW V s / 10 ^ 50) := by
    have e3 : 2 * (scW V s / 10 ^ 4 + 1 + s) * (2 * ((s : ℚ) + 1)) =
        4 * (((s : ℚ) + 1) * scW V s) / 10 ^ 4 + 4 * ((s : ℚ) + 1) ^ 2 := by ring
    rw [e3]
    linarith
  linarith

end A4S1.IndepAll
