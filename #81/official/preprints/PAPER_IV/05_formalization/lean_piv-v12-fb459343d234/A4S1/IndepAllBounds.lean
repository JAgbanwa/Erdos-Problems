import A4S1.IndepAllSetup

/-!
# E14 (copied from E10 `A4S1.OwnAllBounds`, no forbidden import)
# E10, own terminal for every rooted defect `s`: sizes and per-vertex bounds

`n = |V|`, `S = s + 1`, `w = n/S²`, `v = n/S⁴` (so `n v = w²`).  Main bounds:

* `|A ∖ pA0| ≤ v/10³¹`, `e(pR0) ≤ 2w²/10³¹`, `|pY| ≤ 4w/10²⁷`;
* a vertex of `pA0` misses at most `v/10¹⁰` light vertices; a light vertex misses at most
  `w/10⁴ + 2v/10⁴¹` vertices of `pA0`; a core vertex misses at most `w/40` light vertices;
* a clique of light vertices has fewer than `w/10⁴ + 1` vertices.
-/

namespace A4S1.IndepAll

open Finset PaperIV.FarRounding PaperIV.RootedSimplicialDefect A4S1.TerminalPacking

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {A : Finset V} {s : ℕ}

/-! ## The scales -/

omit [DecidableEq V] in
theorem scW_mul : scW V s * ((s : ℚ) + 1) ^ 2 = Fintype.card V := by
  unfold scW; field_simp

omit [DecidableEq V] in
theorem scV_mul : scV V s * ((s : ℚ) + 1) ^ 2 = scW V s := by
  unfold scV scW; field_simp

omit [DecidableEq V] in
theorem n_mul_scV : (Fintype.card V : ℚ) * scV V s = scW V s ^ 2 := by
  unfold scV scW; field_simp

omit [DecidableEq V] in
theorem epsS_mul_sq : epsS s * (Fintype.card V : ℚ) ^ 2 = scV V s ^ 2 / 10 ^ 41 := by
  unfold epsS scV; field_simp

omit [DecidableEq V] in
theorem epsS_mul_le (hv : 0 ≤ scV V s) : epsS s * (Fintype.card V : ℚ) ≤ scV V s / 10 ^ 41 := by
  have hS : (1 : ℚ) ≤ ((s : ℚ) + 1) ^ 4 := one_le_pow₀ (by linarith [(Nat.cast_nonneg s : (0:ℚ) ≤ s)])
  have h : epsS s * (Fintype.card V : ℚ) = scV V s / 10 ^ 41 / ((s : ℚ) + 1) ^ 4 := by
    unfold epsS scV; field_simp
  rw [h]
  exact div_le_self (by positivity) hS

theorem epsS_pos : 0 < epsS s := by unfold epsS; positivity

omit [DecidableEq V] in
theorem scV_big (hn : (10 : ℚ) ^ 50 * ((s : ℚ) + 1) ^ 8 ≤ Fintype.card V) :
    (10 : ℚ) ^ 50 * ((s : ℚ) + 1) ^ 4 ≤ scV V s := by
  unfold scV
  rw [le_div_iff₀ (by positivity)]
  nlinarith

theorem S_ge_one : (1 : ℚ) ≤ (s : ℚ) + 1 := by
  linarith [(Nat.cast_nonneg s : (0:ℚ) ≤ s)]

theorem S_le_S4 : ((s : ℚ) + 1) ≤ ((s : ℚ) + 1) ^ 4 := by
  have h1 : (1 : ℚ) ≤ (s : ℚ) + 1 := by linarith [(Nat.cast_nonneg s : (0:ℚ) ≤ s)]
  calc ((s : ℚ) + 1) = ((s : ℚ) + 1) ^ 1 := (pow_one _).symm
    _ ≤ ((s : ℚ) + 1) ^ 4 := pow_le_pow_right₀ h1 (by norm_num)

/-! ## Generic counting -/

theorem all_degree_split (X : Finset V) (v : V) :
    G.degree v = (X.filter (G.Adj v)).card + ((univ \ X).filter (G.Adj v)).card := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter,
    ← card_union_of_disjoint (disjoint_filter_filter disjoint_sdiff), ← filter_union,
    union_sdiff_of_subset (subset_univ X)]

omit [Fintype V] [DecidableEq V] in
theorem all_card_filter_not_q (S : Finset V) (p : V → Prop) [DecidablePred p] :
    ((S.filter fun z => ¬ p z).card : ℚ) = S.card - (S.filter p).card := by
  have h2 := card_filter_add_card_filter_not (s := S) p
  have h2q : ((S.filter p).card : ℚ) + (S.filter fun z => ¬ p z).card = S.card := by
    exact_mod_cast h2
  linarith

variable (h : AllInput G A s)
include h

theorem AllInput.n_pos : (0 : ℚ) < Fintype.card V :=
  lt_of_lt_of_le (by positivity) h.hn


theorem AllInput.v_big : (10 : ℚ) ^ 50 * ((s : ℚ) + 1) ^ 4 ≤ scV V s := scV_big h.hn

theorem AllInput.v_pos : 0 < scV V s := lt_of_lt_of_le (by positivity) h.v_big

theorem AllInput.v_le_w : scV V s ≤ scW V s := by
  have := scV_mul (V := V) (s := s)
  have h1 : (1 : ℚ) ≤ ((s : ℚ) + 1) ^ 2 := one_le_pow₀ (S_ge_one (s := s))
  have := h.v_pos
  nlinarith

theorem AllInput.w_le_n : scW V s ≤ Fintype.card V := by
  have := scW_mul (V := V) (s := s)
  have h1 : (1 : ℚ) ≤ ((s : ℚ) + 1) ^ 2 := one_le_pow₀ (S_ge_one (s := s))
  have := h.v_pos; have := h.v_le_w
  nlinarith

theorem AllInput.eps_n : epsS s * (Fintype.card V : ℚ) ≤ scV V s / 10 ^ 41 :=
  epsS_mul_le h.v_pos.le

/-- Few vertices are pruned. -/
theorem AllInput.card_pruned : ((A \ pA0 G A s).card : ℚ) ≤ scV V s / 10 ^ 31 := by
  set v := scV V s
  have hv0 := h.v_pos
  set col : V → ℕ := fun a => ((univ \ A).filter fun y => ¬ G.Adj a y).card with hcol
  have h1 : (A \ pA0 G A s).card • (v / 10 ^ 10) ≤ ∑ a ∈ A \ pA0 G A s, (col a : ℚ) := by
    apply card_nsmul_le_sum
    intro a ha
    obtain ⟨haA, haA₀⟩ := mem_sdiff.1 ha
    simp only [pA0, mem_filter, not_and, not_le] at haA₀
    exact (haA₀ haA).le
  have h2 : ∑ a ∈ A \ pA0 G A s, (col a : ℚ) ≤ ∑ a ∈ A, (col a : ℚ) :=
    sum_le_sum_of_subset_of_nonneg sdiff_subset (fun _ _ _ => by positivity)
  have h3 := h.miss
  rw [epsS_mul_sq] at h3
  push_cast at h3
  rw [nsmul_eq_mul] at h1
  have h4 : ((A \ pA0 G A s).card : ℚ) * (v / 10 ^ 10) ≤ (v / 10 ^ 31) * (v / 10 ^ 10) := by
    have : ∑ a ∈ A, (col a : ℚ) ≤ v ^ 2 / 10 ^ 41 := h3
    nlinarith
  exact le_of_mul_le_mul_right h4 (by positivity)

theorem AllInput.card_A0_lo :
    (Fintype.card V : ℚ) / 3 - 2 * (scV V s / 10 ^ 31) ≤ (pA0 G A s).card := by
  have h1 : ((A \ pA0 G A s).card : ℚ) = A.card - (pA0 G A s).card := by
    rw [card_sdiff_of_subset pA0_subset]
    have := card_le_card (pA0_subset (G := G) (A := A) (s := s))
    push_cast [Nat.cast_sub this]; ring
  have := h.card_pruned; have := h.size_lo; have := h.eps_n; have := h.v_pos
  linarith

theorem AllInput.card_A0_hi :
    ((pA0 G A s).card : ℚ) ≤ Fintype.card V / 3 + scV V s / 10 ^ 41 := by
  have : ((pA0 G A s).card : ℚ) ≤ A.card := by exact_mod_cast card_le_card pA0_subset
  have := h.size_hi; have := h.eps_n
  linarith

/-- The exterior of the pruned clique spans few edges. -/
theorem AllInput.R0_edges :
    ((inEdges G (pR0 G A s)).card : ℚ) ≤ 2 * (scW V s ^ 2 / 10 ^ 31) := by
  have hn0 := h.n_pos
  have hsplit : pR0 G A s = (univ \ A) ∪ (A \ pA0 G A s) := by
    ext v
    simp only [pR0, mem_sdiff, mem_univ, true_and, mem_union]
    constructor
    · intro hv; by_cases hvA : v ∈ A
      · exact Or.inr ⟨hvA, hv⟩
      · exact Or.inl hvA
    · rintro (hv | hv)
      · exact fun h' => hv (pA0_subset h')
      · exact hv.2
  have := card_inEdges_union_le (G := G) (univ \ A) (A \ pA0 G A s)
  rw [← hsplit] at this
  have h1 : ((inEdges G (pR0 G A s)).card : ℚ) ≤
      (inEdges G (univ \ A)).card + (A \ pA0 G A s).card * (Fintype.card V : ℚ) := by
    exact_mod_cast this
  have h2 : ((A \ pA0 G A s).card : ℚ) * Fintype.card V ≤
      scV V s / 10 ^ 31 * Fintype.card V :=
    mul_le_mul_of_nonneg_right h.card_pruned hn0.le
  have h3 := h.out
  rw [epsS_mul_sq] at h3
  have h4 := n_mul_scV (V := V) (s := s)
  have h5 : scV V s ^ 2 ≤ scW V s ^ 2 := pow_le_pow_left₀ h.v_pos.le h.v_le_w 2
  nlinarith

/-- Few heavy vertices. -/
theorem AllInput.card_Y : ((pY G A s).card : ℚ) ≤ 4 * (scW V s / 10 ^ 27) := by
  set w := scW V s
  have hw0 : 0 < w := lt_of_lt_of_le h.v_pos h.v_le_w
  set R := pR0 G A s
  have hs1 := sum_card_filter_adj_le (G := G) R
  have hs2 : ∑ v ∈ pY G A s, ((R.filter (G.Adj v)).card : ℚ) ≤
      ∑ v ∈ R, ((R.filter (G.Adj v)).card : ℚ) :=
    sum_le_sum_of_subset_of_nonneg pY_subset (fun _ _ _ => by positivity)
  have hs3 : (pY G A s).card • (w / 10 ^ 4) ≤ ∑ v ∈ pY G A s, ((R.filter (G.Adj v)).card : ℚ) := by
    apply card_nsmul_le_sum
    intro v hv
    exact (mem_filter.1 hv).2
  rw [nsmul_eq_mul] at hs3
  have hs1q : ∑ v ∈ R, ((R.filter (G.Adj v)).card : ℚ) ≤ 2 * (inEdges G R).card := by
    exact_mod_cast hs1
  have he := h.R0_edges
  have hkey : ((pY G A s).card : ℚ) * (w / 10 ^ 4) ≤ (4 * (w / 10 ^ 27)) * (w / 10 ^ 4) := by
    nlinarith
  exact le_of_mul_le_mul_right hkey (by positivity)

/-- A vertex of the pruned clique misses few light vertices; the misses lie outside `A`. -/
theorem AllInput.A0_miss_L_sub {a : V} (ha : a ∈ pA0 G A s) :
    (pL G A s).filter (fun z => ¬ G.Adj a z) ⊆ (univ \ A).filter fun y => ¬ G.Adj a y := by
  intro z hz
  obtain ⟨hzL, hnz⟩ := mem_filter.1 hz
  refine mem_filter.2 ⟨mem_sdiff.2 ⟨mem_univ z, fun hzA => hnz (h.clique (pA0_subset ha) hzA ?_)⟩,
    hnz⟩
  rintro rfl
  exact mem_pR0.1 (pL_subset hzL) ha

theorem AllInput.A0_miss_L {a : V} (ha : a ∈ pA0 G A s) :
    (((pL G A s).filter fun z => ¬ G.Adj a z).card : ℚ) ≤ scV V s / 10 ^ 10 := by
  have h1 := card_le_card (h.A0_miss_L_sub ha)
  have h2 := (mem_filter.1 ha).2
  have : (((pL G A s).filter fun z => ¬ G.Adj a z).card : ℚ) ≤
      (((univ \ A).filter fun y => ¬ G.Adj a y).card : ℚ) := by exact_mod_cast h1
  linarith

theorem AllInput.A0_miss_L_sum :
    ((∑ a ∈ pA0 G A s, ((pL G A s).filter fun z => ¬ G.Adj a z).card : ℕ) : ℚ) ≤
      scV V s ^ 2 / 10 ^ 41 := by
  have e1 : ∑ a ∈ pA0 G A s, ((pL G A s).filter fun z => ¬ G.Adj a z).card ≤
      ∑ a ∈ pA0 G A s, ((univ \ A).filter fun y => ¬ G.Adj a y).card :=
    sum_le_sum fun a ha => card_le_card (h.A0_miss_L_sub ha)
  have e2 : ∑ a ∈ pA0 G A s, ((univ \ A).filter fun y => ¬ G.Adj a y).card ≤
      ∑ a ∈ A, ((univ \ A).filter fun y => ¬ G.Adj a y).card :=
    sum_le_sum_of_subset_of_nonneg pA0_subset (fun _ _ _ => Nat.zero_le _)
  have := h.miss
  rw [epsS_mul_sq] at this
  have e3 : ((∑ a ∈ pA0 G A s, ((pL G A s).filter fun z => ¬ G.Adj a z).card : ℕ) : ℚ) ≤
      ((∑ a ∈ A, ((univ \ A).filter fun y => ¬ G.Adj a y).card : ℕ) : ℚ) := by
    exact_mod_cast e1.trans e2
  linarith

omit h in
theorem pL_extdeg {v : V} (hv : v ∈ pL G A s) :
    (((pR0 G A s).filter (G.Adj v)).card : ℚ) < scW V s / 10 ^ 4 := by
  by_contra hc
  push_neg at hc
  exact (mem_pL.1 hv).2 (mem_filter.2 ⟨(mem_pL.1 hv).1, hc⟩)

/-- A light vertex misses few vertices of the pruned clique (minimum degree). -/
theorem AllInput.L_miss_A0 {v : V} (hv : v ∈ pL G A s) :
    (((pA0 G A s).filter fun a => ¬ G.Adj v a).card : ℚ) ≤
      scW V s / 10 ^ 4 + 2 * (scV V s / 10 ^ 41) := by
  have hsplit := all_degree_split (G := G) (pA0 G A s) v
  have hsplitQ : (G.degree v : ℚ) = ((pA0 G A s).filter (G.Adj v)).card +
      ((pR0 G A s).filter (G.Adj v)).card := by exact_mod_cast hsplit
  have hlow := pL_extdeg hv
  have hdv := h.deg v
  have hc := all_card_filter_not_q (pA0 G A s) (fun a => G.Adj v a)
  have := h.card_A0_hi
  have := h.eps_n
  nlinarith

/-- A clique of light vertices is small. -/
theorem AllInput.L_clique {K : Finset V} (hK : K ⊆ pL G A s) (hKc : G.IsClique (K : Set V)) :
    (K.card : ℚ) < scW V s / 10 ^ 4 + 1 := by
  rcases K.eq_empty_or_nonempty with rfl | ⟨k, hk⟩
  · simp only [card_empty, Nat.cast_zero]; have := h.v_pos; have := h.v_le_w; linarith
  have hsub : K.erase k ⊆ (pR0 G A s).filter (G.Adj k) := by
    intro z hz
    obtain ⟨hzk, hzK⟩ := mem_erase.1 hz
    exact mem_filter.2 ⟨pL_subset (hK hzK), hKc hk hzK (Ne.symm hzk)⟩
  have h1 := card_le_card hsub
  rw [card_erase_of_mem hk] at h1
  have h2 := pL_extdeg (hK hk)
  have h3 : ((K.card - 1 : ℕ) : ℚ) ≤ (((pR0 G A s).filter (G.Adj k)).card : ℚ) := by
    exact_mod_cast h1
  have h4 : (K.card : ℚ) ≤ ((K.card - 1 : ℕ) : ℚ) + 1 := by
    have : K.card ≤ K.card - 1 + 1 := by omega
    exact_mod_cast this
  linarith

omit h in
theorem pYc_miss_L {v : V} (hv : v ∈ pYc G A s) :
    (((pL G A s).filter fun z => ¬ G.Adj v z).card : ℚ) ≤ scW V s / 40 := (mem_pYc.1 hv).2

theorem AllInput.core_miss_L {v : V} (hv : v ∈ pCore G A s) :
    (((pL G A s).filter fun z => ¬ G.Adj v z).card : ℚ) ≤ scW V s / 40 := by
  rcases mem_pCore.1 hv with hv | hv
  · have := h.A0_miss_L hv; have := h.v_pos; have := h.v_le_w; linarith
  · exact pYc_miss_L hv

omit h in
theorem notYc_miss_L {v : V} (hY : v ∈ pY G A s) (hv : v ∉ pYc G A s) :
    scW V s / 40 < (((pL G A s).filter fun z => ¬ G.Adj v z).card : ℚ) := by
  by_contra hc
  push_neg at hc
  exact hv (mem_pYc.2 ⟨hY, hc⟩)

omit h in
theorem pYr_miss_L {v : V} (hv : v ∈ pYr G A s) :
    scW V s / 40 < (((pL G A s).filter fun z => ¬ G.Adj v z).card : ℚ) :=
  notYc_miss_L (mem_pYr.1 hv).1.1 (mem_pYr.1 hv).1.2

omit h in
theorem pYr_miss_A0 {v : V} (hv : v ∈ pYr G A s) :
    (((pA0 G A s).filter fun a => ¬ G.Adj v a).card : ℚ) ≤ scW V s / 200 := (mem_pYr.1 hv).2

omit h in
theorem pT_miss_L {w : V} (hw : w ∈ pT G A s) :
    scW V s / 40 < (((pL G A s).filter fun z => ¬ G.Adj w z).card : ℚ) :=
  notYc_miss_L (mem_pT.1 hw).1 (mem_pT.1 hw).2.1

omit h in
theorem pT_miss_A0 {w : V} (hw : w ∈ pT G A s) :
    scW V s / 200 < (((pA0 G A s).filter fun a => ¬ G.Adj w a).card : ℚ) := by
  obtain ⟨hY, hc, hr⟩ := mem_pT.1 hw
  by_contra hcon
  push_neg at hcon
  exact hr (mem_pYr.2 ⟨⟨hY, hc⟩, hcon⟩)

/-! ## Sizes of the parts -/

theorem AllInput.card_T : ((pT G A s).card : ℚ) ≤ 4 * (scW V s / 10 ^ 27) := by
  have := card_Y_split (G := G) (A := A) (s := s)
  have : ((pT G A s).card : ℚ) ≤ (pY G A s).card := by exact_mod_cast (by omega)
  have := h.card_Y
  linarith

theorem AllInput.card_Yc : ((pYc G A s).card : ℚ) ≤ 4 * (scW V s / 10 ^ 27) := by
  have := card_Y_split (G := G) (A := A) (s := s)
  have : ((pYc G A s).card : ℚ) ≤ (pY G A s).card := by exact_mod_cast (by omega)
  have := h.card_Y
  linarith

theorem AllInput.card_Yr : ((pYr G A s).card : ℚ) ≤ 4 * (scW V s / 10 ^ 27) := by
  have := card_Y_split (G := G) (A := A) (s := s)
  have : ((pYr G A s).card : ℚ) ≤ (pY G A s).card := by exact_mod_cast (by omega)
  have := h.card_Y
  linarith

theorem AllInput.card_core_lo :
    (Fintype.card V : ℚ) / 3 - 2 * (scV V s / 10 ^ 31) ≤ (pCore G A s).card := by
  have := card_core (G := G) (A := A) (s := s)
  have : ((pA0 G A s).card : ℚ) ≤ (pCore G A s).card := by exact_mod_cast (by omega)
  have := h.card_A0_lo
  linarith

theorem AllInput.card_core_hi :
    ((pCore G A s).card : ℚ) ≤ Fintype.card V / 3 + scV V s / 10 ^ 41 +
      4 * (scW V s / 10 ^ 27) := by
  have h1 := card_core (G := G) (A := A) (s := s)
  have : ((pCore G A s).card : ℚ) = (pA0 G A s).card + (pYc G A s).card := by exact_mod_cast h1
  have := h.card_A0_hi; have := h.card_Yc
  linarith

theorem AllInput.card_L_hi :
    ((pL G A s).card : ℚ) ≤ 2 * (Fintype.card V : ℚ) / 3 + 2 * (scV V s / 10 ^ 31) := by
  have h1 := card_R0 (G := G) (A := A) (s := s)
  have h2 := card_R0_split (G := G) (A := A) (s := s)
  have : ((pL G A s).card : ℚ) + (pA0 G A s).card ≤ Fintype.card V := by
    exact_mod_cast (by omega)
  have := h.card_A0_lo
  linarith

theorem AllInput.card_L_lo :
    2 * (Fintype.card V : ℚ) / 3 - scV V s / 10 ^ 41 - 4 * (scW V s / 10 ^ 27) ≤
      (pL G A s).card := by
  have h1 := card_R0 (G := G) (A := A) (s := s)
  have h2 := card_R0_split (G := G) (A := A) (s := s)
  have : ((pL G A s).card : ℚ) + (pY G A s).card + (pA0 G A s).card = Fintype.card V := by
    exact_mod_cast (by omega)
  have := h.card_A0_hi; have := h.card_Y
  linarith

theorem AllInput.card_host_lo :
    2 * (Fintype.card V : ℚ) / 3 - scV V s / 10 ^ 41 - 4 * (scW V s / 10 ^ 27) ≤
      (pHost G A s).card := by
  have := card_host (G := G) (A := A) (s := s)
  have : ((pL G A s).card : ℚ) ≤ (pHost G A s).card := by exact_mod_cast (by omega)
  have := h.card_L_lo
  linarith

theorem AllInput.card_host_hi :
    ((pHost G A s).card : ℚ) ≤ 2 * (Fintype.card V : ℚ) / 3 + 2 * (scV V s / 10 ^ 31) +
      4 * (scW V s / 10 ^ 27) := by
  have h1 := card_host (G := G) (A := A) (s := s)
  have : ((pHost G A s).card : ℚ) = (pL G A s).card + (pYr G A s).card := by exact_mod_cast h1
  have := h.card_L_hi; have := h.card_Yr
  linarith

theorem AllInput.host_edges :
    ((inEdges G (pHost G A s)).card : ℚ) ≤ 2 * (scW V s ^ 2 / 10 ^ 31) := by
  have := card_le_card (inEdges_mono (G := G) (pHost_subset_pR0 (G := G) (A := A) (s := s)))
  have : ((inEdges G (pHost G A s)).card : ℚ) ≤ (inEdges G (pR0 G A s)).card := by
    exact_mod_cast this
  have := h.R0_edges
  linarith

end A4S1.IndepAll
