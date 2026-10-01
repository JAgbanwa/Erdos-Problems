import A4S1.IndepAllParams
namespace A4S1.IndepAll
open Finset PaperIV.FarRounding PaperIV.RootedSimplicialDefect A4S1.TerminalPacking
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {A : Finset V} {s : ℕ}
variable (h : AllInput G A s)
include h
set_option maxHeartbeats 1000000 in
/-- **Capacities.** -/
theorem AllInput.params_strict :
    ∃ k q σ τ D L : ℕ,
      (∀ v ∈ pHost G A s, ((pCore G A s).filter fun u => ¬ G.Adj v u).card +
        2 * (pT G A s).card ≤ σ) ∧
      (∀ u ∈ pCore G A s, ((pHost G A s).filter fun v => ¬ G.Adj u v).card +
        2 * (pT G A s).card ≤ τ) ∧
      (∀ v ∈ pHost G A s, ((pHost G A s).filter (G.Adj v)).card + 1 ≤ k) ∧
      (pCore G A s).card ≤ k ∧ k ≤ 2 * ((pCore G A s).card - 2 * σ) ∧
      PaperIV.EquitableEdgeColouring.classCeiling (inEdges G (pHost G A s)).card k ≤ q ∧
      3 * (((pCore G A s).card + 1) / 2) + 2 * τ + 4 * q ≤ (pHost G A s).card + 2 ∧
      (∀ X ⊆ pCore G A s, ∀ Y ⊆ pHost G A s,
        ((X ×ˢ Y).filter fun p => ¬ G.Adj p.1 p.2).card ≤ D) ∧
      D < L * L ∧ (L : ℚ) ≤ scW V s / 10 ^ 13 + 1 ∧
      k ≤ Fintype.card V ∧
      scW V s ≤ 2000 * ((2 * ((pCore G A s).card - 2 * σ) - k : ℕ) : ℚ) := by
  have hn0 := h.n_pos
  have hv := h.v_pos; have hvw := h.v_le_w; have hwn := h.w_le_n
  have hw0 : 0 < scW V s := hv.trans_le hvw
  have hwbig := h.S_le_w
  have hS1 := (S_ge_one (s := s))
  have hS2 : (1 : ℚ) ≤ ((s : ℚ) + 1) ^ 2 := one_le_pow₀ hS1
  have hw50 : (10 : ℚ) ^ 50 ≤ scW V s := by nlinarith only [hwbig, hS2]
  have hWq := h.card_T
  have hSlo := h.card_core_lo
  have hShi := h.card_core_hi
  have hHlo := h.card_host_lo
  have hHhi := h.card_host_hi
  have hYc := h.card_Yc
  have hYr := h.card_Yr
  have htot := card_total (G := G) (A := A) (s := s)
  have htotq : ((pCore G A s).card : ℚ) + (pHost G A s).card + (pT G A s).card =
      (Fintype.card V : ℚ) := by exact_mod_cast htot
  set w := scW V s with hwdef
  set vv := scV V s with hvvdef
  set n := (Fintype.card V : ℚ) with hndef
  -- σ
  set σ := (pHost G A s).sup fun v => ((pCore G A s).filter fun u => ¬ G.Adj v u).card +
    2 * (pT G A s).card with hσdef
  have hσ : ∀ v ∈ pHost G A s, ((pCore G A s).filter fun u => ¬ G.Adj v u).card +
      2 * (pT G A s).card ≤ σ := fun v hv =>
    le_sup (f := fun v => ((pCore G A s).filter fun u => ¬ G.Adj v u).card +
      2 * (pT G A s).card) hv
  have hσq : (σ : ℚ) ≤ w / 200 + 3 * (4 * (w / 10 ^ 27)) := by
    apply all_sup_le_q _ _ _ (by positivity)
    intro v hv
    have e1 := all_filter_union_le (pA0 G A s) (pYc G A s) (fun u => ¬ G.Adj v u)
    have e1q : (((pCore G A s).filter fun u => ¬ G.Adj v u).card : ℚ) ≤
        ((pA0 G A s).filter fun u => ¬ G.Adj v u).card + (pYc G A s).card := by
      exact_mod_cast e1
    have e2 : (((pA0 G A s).filter fun u => ¬ G.Adj v u).card : ℚ) ≤ w / 200 := by
      rcases mem_pHost.1 hv with hv | hv
      · have := h.L_miss_A0 hv; linarith
      · exact pYr_miss_A0 hv
    push_cast
    linarith
  -- τ
  set τ := (pCore G A s).sup fun u => ((pHost G A s).filter fun v => ¬ G.Adj u v).card +
    2 * (pT G A s).card with hτdef
  have hτ : ∀ u ∈ pCore G A s, ((pHost G A s).filter fun v => ¬ G.Adj u v).card +
      2 * (pT G A s).card ≤ τ := fun u hu =>
    le_sup (f := fun u => ((pHost G A s).filter fun v => ¬ G.Adj u v).card +
      2 * (pT G A s).card) hu
  have hτq : (τ : ℚ) ≤ w / 40 + 3 * (4 * (w / 10 ^ 27)) := by
    apply all_sup_le_q _ _ _ (by positivity)
    intro u hu
    have e1 := all_filter_union_le (pL G A s) (pYr G A s) (fun v => ¬ G.Adj u v)
    have e1q : (((pHost G A s).filter fun v => ¬ G.Adj u v).card : ℚ) ≤
        ((pL G A s).filter fun v => ¬ G.Adj u v).card + (pYr G A s).card := by exact_mod_cast e1
    have e2 := h.core_miss_L hu
    push_cast
    linarith
  -- k
  have h2σ : 2 * σ ≤ (pCore G A s).card := by
    have : (2 * σ : ℚ) ≤ (pCore G A s).card := by nlinarith only [hS2, hwbig, hvw, hwn, hSlo, hσq]
    exact_mod_cast this
  set d : ℕ := ⌊w / 1000⌋₊ with hddef
  have hdhi : (d : ℚ) ≤ w / 1000 := Nat.floor_le (by positivity)
  have hdlo : w / 2000 ≤ (d : ℚ) := by
    have := Nat.lt_floor_add_one (w / 1000)
    change w / 1000 < (d : ℚ) + 1 at this
    linarith only [this, hw50]
  have hdpre : d ≤ 2 * ((pCore G A s).card - 2 * σ) := by
    have hp : ((2 * ((pCore G A s).card - 2 * σ) : ℕ) : ℚ) =
        2 * (pCore G A s).card - 4 * σ := by
      push_cast [Nat.cast_sub h2σ]; ring
    have : (d : ℚ) ≤ ((2 * ((pCore G A s).card - 2 * σ) : ℕ) : ℚ) := by
      rw [hp]
      nlinarith only [hdhi, hS2, hwbig, hvw, hwn, hSlo, hσq]
    exact_mod_cast this
  set k := 2 * ((pCore G A s).card - 2 * σ) - d with hkdef
  have hkq : (k : ℚ) = 2 * (pCore G A s).card - 4 * σ - d := by
    rw [hkdef]; push_cast [Nat.cast_sub hdpre, Nat.cast_sub h2σ]; ring
  have htheta : k ≤ 2 * ((pCore G A s).card - 2 * σ) := Nat.sub_le _ _
  have hgap : scW V s ≤ 2000 * ((2 * ((pCore G A s).card - 2 * σ) - k : ℕ) : ℚ) := by
    have : 2 * ((pCore G A s).card - 2 * σ) - k = d := by omega
    rw [this]
    linarith only [hdlo]
  have hknUpper : k ≤ Fintype.card V := by
    have : (k : ℚ) ≤ n := by
      rw [hkq]
      have hd0 : (0 : ℚ) ≤ d := Nat.cast_nonneg _
      have hsigma0 : (0 : ℚ) ≤ σ := Nat.cast_nonneg _
      nlinarith only [hShi, hvw, hwn, hd0, hsigma0]
    change (k : ℚ) ≤ (Fintype.card V : ℚ) at this
    exact_mod_cast this
  have hkn : n / 2 ≤ (k : ℚ) := by rw [hkq]; nlinarith only [hS2, hwbig, hvw, hwn, hSlo, hσq, hdhi]
  have hΔ : ∀ v ∈ pHost G A s, ((pHost G A s).filter (G.Adj v)).card + 1 ≤ k := by
    intro v hv
    have : (((pHost G A s).filter (G.Adj v)).card : ℚ) + 1 ≤ k := by
      rcases mem_pHost.1 hv with hvL | hvY
      · have e1 : ((pHost G A s).filter (G.Adj v)).card ≤ ((pR0 G A s).filter (G.Adj v)).card :=
          card_le_card (filter_subset_filter _ pHost_subset_pR0)
        have e1q : (((pHost G A s).filter (G.Adj v)).card : ℚ) ≤
            ((pR0 G A s).filter (G.Adj v)).card := by exact_mod_cast e1
        have := pL_extdeg hvL
        nlinarith only [hS2, hwbig, hvw, hwn, hSlo, hσq, hdhi, hkq, e1q, this]
      · have e1 : (pL G A s).filter (fun z => ¬ G.Adj v z) ⊆
            (pHost G A s).filter (fun z => ¬ G.Adj v z) :=
          filter_subset_filter _ (fun z hz => mem_pHost.2 (Or.inl hz))
        have e1q : (((pL G A s).filter fun z => ¬ G.Adj v z).card : ℚ) ≤
            ((pHost G A s).filter fun z => ¬ G.Adj v z).card := by exact_mod_cast card_le_card e1
        have e2 := all_card_filter_not_q (pHost G A s) (fun z => G.Adj v z)
        have e3 := pYr_miss_L hvY
        rw [hkq]
        have hWn : (0 : ℚ) ≤ (pT G A s).card := by positivity
        nlinarith only [hS2, hwbig, hvw, htotq, hSlo, hσq, hdhi, e1q, e2, e3]
    exact_mod_cast this
  have hck : (pCore G A s).card ≤ k := by
    have : ((pCore G A s).card : ℚ) ≤ k := by rw [hkq]; nlinarith only [hS2, hwbig, hvw, hwn, hSlo, hσq, hdhi]
    exact_mod_cast this
  -- q
  set q := PaperIV.EquitableEdgeColouring.classCeiling (inEdges G (pHost G A s)).card k with hqdef
  have hqk := classCeiling_mul_le (inEdges G (pHost G A s)).card k
  have hqkq : (q : ℚ) * k ≤ (inEdges G (pHost G A s)).card + k := by exact_mod_cast hqk
  have hHe := h.host_edges
  have hqq : (q : ℚ) ≤ 4 * (w / 10 ^ 31) + 1 := by
    have hk0 : (0 : ℚ) < k := by linarith
    by_contra hc
    push_neg at hc
    have h1 : (4 * (w / 10 ^ 31)) * k < ((q : ℚ) - 1) * k :=
      mul_lt_mul_of_pos_right (by linarith) hk0
    have h2 : (4 * (w / 10 ^ 31)) * (n / 2) ≤ (4 * (w / 10 ^ 31)) * k :=
      mul_le_mul_of_nonneg_left hkn (by positivity)
    have h3 : w * w ≤ w * n := mul_le_mul_of_nonneg_left hwn hw0.le
    nlinarith only [hqkq, hHe, h1, h2, h3]
  -- D
  set D := (((pCore G A s) ×ˢ (pHost G A s)).filter fun p => ¬ G.Adj p.1 p.2).card with hDdef
  have hD : ∀ X ⊆ pCore G A s, ∀ Y ⊆ pHost G A s,
      ((X ×ˢ Y).filter fun p => ¬ G.Adj p.1 p.2).card ≤ D :=
    fun X hX Y hY => card_le_card (filter_subset_filter _ (product_subset_product hX hY))
  have hDq : (D : ℚ) ≤ (w / 10 ^ 13) ^ 2 := by
    have hcp := all_card_filter_product (pCore G A s) (pHost G A s) (fun a b => ¬ G.Adj a b)
    have e2 : ∑ u ∈ pCore G A s, ((pHost G A s).filter fun v => ¬ G.Adj u v).card =
        ∑ u ∈ pA0 G A s, ((pHost G A s).filter fun v => ¬ G.Adj u v).card +
          ∑ u ∈ pYc G A s, ((pHost G A s).filter fun v => ¬ G.Adj u v).card :=
      sum_union A0_Yc_disjoint
    have e3 : ∑ u ∈ pA0 G A s, ((pHost G A s).filter fun v => ¬ G.Adj u v).card ≤
        ∑ u ∈ pA0 G A s, ((pL G A s).filter fun v => ¬ G.Adj u v).card +
          ∑ u ∈ pA0 G A s, ((pYr G A s).filter fun v => ¬ G.Adj u v).card := by
      rw [← sum_add_distrib]
      exact sum_le_sum fun u _ => all_filter_union_le' _ _ _
    have e4 : ∑ u ∈ pA0 G A s, ((pYr G A s).filter fun v => ¬ G.Adj u v).card =
        ∑ y ∈ pYr G A s, ((pA0 G A s).filter fun a => ¬ G.Adj y a).card :=
      all_sum_card_filter_not_comm _ _
    have e5 : ∑ y ∈ pYr G A s, (((pA0 G A s).filter fun a => ¬ G.Adj y a).card : ℚ) ≤
        (pYr G A s).card * (w / 200) := by
      have := sum_le_sum fun y (hy : y ∈ pYr G A s) => pYr_miss_A0 hy
      rw [sum_const, nsmul_eq_mul] at this
      exact this
    have e6 : ∑ u ∈ pYc G A s, (((pHost G A s).filter fun v => ¬ G.Adj u v).card : ℚ) ≤
        (pYc G A s).card * (w / 40 + (pYr G A s).card) := by
      have : ∀ u ∈ pYc G A s, (((pHost G A s).filter fun v => ¬ G.Adj u v).card : ℚ) ≤
          w / 40 + (pYr G A s).card := by
        intro u hu
        have e1 := all_filter_union_le (pL G A s) (pYr G A s) (fun v => ¬ G.Adj u v)
        have e1q : (((pHost G A s).filter fun v => ¬ G.Adj u v).card : ℚ) ≤
            ((pL G A s).filter fun v => ¬ G.Adj u v).card + (pYr G A s).card := by
          exact_mod_cast e1
        have := pYc_miss_L hu
        linarith
      have := sum_le_sum this
      rw [sum_const, nsmul_eq_mul] at this
      exact this
    have e7 := h.A0_miss_L_sum
    have hDsum : (D : ℚ) ≤
        ((∑ u ∈ pA0 G A s, ((pL G A s).filter fun v => ¬ G.Adj u v).card : ℕ) : ℚ) +
        ∑ y ∈ pYr G A s, (((pA0 G A s).filter fun a => ¬ G.Adj y a).card : ℚ) +
        ∑ u ∈ pYc G A s, (((pHost G A s).filter fun v => ¬ G.Adj u v).card : ℚ) := by
      have : D ≤ ∑ u ∈ pA0 G A s, ((pL G A s).filter fun v => ¬ G.Adj u v).card +
          ∑ y ∈ pYr G A s, ((pA0 G A s).filter fun a => ¬ G.Adj y a).card +
          ∑ u ∈ pYc G A s, ((pHost G A s).filter fun v => ¬ G.Adj u v).card := by
        rw [hDdef, hcp, e2, ← e4]; omega
      exact_mod_cast this
    have hYr0 : (0 : ℚ) ≤ (pYr G A s).card := by positivity
    have hYc0 : (0 : ℚ) ≤ (pYc G A s).card := by positivity
    have m1 : ((pYr G A s).card : ℚ) * (w / 200) ≤ (4 * (w / 10 ^ 27)) * (w / 200) :=
      mul_le_mul_of_nonneg_right hYr (by positivity)
    have m2 : ((pYc G A s).card : ℚ) * (w / 40 + (pYr G A s).card) ≤
        (4 * (w / 10 ^ 27)) * (w / 40 + 4 * (w / 10 ^ 27)) :=
      mul_le_mul hYc (by linarith) (by positivity) (by positivity)
    have m3 : vv ^ 2 ≤ w ^ 2 := pow_le_pow_left₀ hv.le hvw 2
    nlinarith only [e5, e6, e7, hDsum, m1, m2, m3]
  set L := Nat.sqrt D + 1 with hLdef
  have hL : D < L * L := Nat.lt_succ_sqrt D
  have hLq : (L : ℚ) ≤ w / 10 ^ 13 + 1 := by
    have := all_sqrt_le_q D (w / 10 ^ 13) (by positivity) hDq
    rw [hLdef]; push_cast; linarith
  refine ⟨k, q, σ, τ, D, L, hσ, hτ, hΔ, hck, htheta, le_refl _, ?_, hD, hL, hLq, hknUpper, hgap⟩
  have e1 : ((((pCore G A s).card + 1) / 2 : ℕ) : ℚ) ≤ (((pCore G A s).card : ℚ) + 1) / 2 := by
    have := Nat.cast_div_le (α := ℚ) (m := (pCore G A s).card + 1) (n := 2)
    push_cast at this; exact this
  have : (3 * ((((pCore G A s).card + 1) / 2 : ℕ) : ℚ)) + 2 * τ + 4 * q ≤
      (pHost G A s).card + 2 := by nlinarith only [hS2, hwbig, hvw, hwn, hShi, hHlo, hτq, hqq, e1]
  exact_mod_cast this

end A4S1.IndepAll
#print axioms A4S1.IndepAll.AllInput.params_strict
