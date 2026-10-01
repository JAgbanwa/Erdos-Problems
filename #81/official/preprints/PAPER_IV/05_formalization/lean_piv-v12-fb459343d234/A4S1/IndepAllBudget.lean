import A4S1.IndepAllParams

/-!
# E14 (copied from E10 `A4S1.OwnAllBudget`, no forbidden import)
# E10, own terminal for every rooted defect `s`: joint exact accounting

`AllInput.hkey`: the rational budget of `own_final_all`,

  `Σ_t deg t + 2k(L+k) + C(c,2) + C(s+1,2) ≤ e(G[C]) + 2 Σ_t min(u_t, v_t) + s c + k (c+b+s)/3`,

with `k = |pT|`, `u_t = |N(t) ∩ pCore|`, `v_t = |N(t) ∩ pHost|` (step 4 of `TASK_E10.txt`).

Per exceptional vertex `t` the excess over its budget is
`g_t = deg t − 2 min(u_t, v_t) + 2(L+k) − (c+b+s)/3`.
* `t` is *big* if `v_t − u_t > n/3 − w/400`. A vertex that is not big has `g_t ≤ 0`, since
  `u_t < c − w/200`.
* A big vertex has `g_t ≤ |N(t) ∩ pL| − n/3 + e₁`, with `e₁ = 4k + 2L + 4w/10²⁷`.
* There are `j ≤ 2s + 1` big vertices (joint incidence on `2s + 2` of them is impossible).
* The core has `M = C(c,2) − e(G[C]) ≤ νc − C(ν+1,2)` (Erdős–Gallai).
* Cases:
  * `j = 0`: `νc − C(ν+1,2) ≤ sc − C(s+1,2)`;
  * `1 ≤ j ≤ s − ν`: each big vertex costs at most `c − w/40 + o(w)`, since it misses `w/40`
    light vertices;
  * `j ≥ s − ν + 1`: joint incidence `Σ |N(t) ∩ pL| ≤ (s − ν)|pL| + n/9` leaves slack
    `≈ 2n/9`.
-/

namespace A4S1.IndepAll

open Finset PaperIV.FarRounding PaperIV.RootedSimplicialDefect A4S1.TerminalPacking

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {A : Finset V} {s : ℕ}

/-- `deg − 2 min(u, v) ≤ |u − v| + e` when `deg ≤ u + v + e`. -/
theorem all_excess (dg u v e : ℕ) (hdg : dg ≤ u + v + e) :
    (dg : ℚ) - 2 * ((min u v : ℕ) : ℚ) ≤ max ((u : ℚ) - v) ((v : ℚ) - u) + e := by
  have hq : (dg : ℚ) ≤ u + v + e := by exact_mod_cast hdg
  rcases le_total u v with huv | huv
  · rw [min_eq_left huv]
    have := le_max_right ((u : ℚ) - v) ((v : ℚ) - u)
    linarith
  · rw [min_eq_right huv]
    have := le_max_left ((u : ℚ) - v) ((v : ℚ) - u)
    linarith

theorem all_degree_le_uvw (w : V) :
    G.degree w ≤ ((pCore G A s).filter (G.Adj w)).card + ((pHost G A s).filter (G.Adj w)).card +
      (pT G A s).card := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter]
  have hsub : univ.filter (fun z => G.Adj w z) ⊆ ((pCore G A s).filter (G.Adj w) ∪
      (pHost G A s).filter (G.Adj w)) ∪ pT G A s := by
    intro z hz
    have hz' := (mem_filter.1 hz).2
    rcases cover (G := G) (A := A) (s := s) z with h1 | h1 | h1
    · exact mem_union_left _ (mem_union_left _ (mem_filter.2 ⟨h1, hz'⟩))
    · exact mem_union_left _ (mem_union_right _ (mem_filter.2 ⟨h1, hz'⟩))
    · exact mem_union_right _ h1
  have := card_le_card hsub
  have := card_union_le ((pCore G A s).filter (G.Adj w) ∪ (pHost G A s).filter (G.Adj w))
    (pT G A s)
  have := card_union_le ((pCore G A s).filter (G.Adj w)) ((pHost G A s).filter (G.Adj w))
  omega

/-- An exceptional vertex sees at most `c − w/200` core vertices. -/
theorem all_T_core_adj {w : V} (hw : w ∈ pT G A s) :
    (((pCore G A s).filter (G.Adj w)).card : ℚ) < (pCore G A s).card - scW V s / 200 := by
  have hdis : Disjoint ((pCore G A s).filter (G.Adj w))
      ((pA0 G A s).filter fun a => ¬ G.Adj w a) := by
    rw [disjoint_left]
    intro z hz hz'
    exact (mem_filter.1 hz').2 (mem_filter.1 hz).2
  have hsub : (pCore G A s).filter (G.Adj w) ∪ (pA0 G A s).filter (fun a => ¬ G.Adj w a) ⊆
      pCore G A s := union_subset (filter_subset _ _)
    (fun z hz => mem_pCore.2 (Or.inl (mem_filter.1 hz).1))
  have := card_le_card hsub
  rw [card_union_of_disjoint hdis] at this
  have hq : (((pCore G A s).filter (G.Adj w)).card : ℚ) +
      ((pA0 G A s).filter fun a => ¬ G.Adj w a).card ≤ (pCore G A s).card := by
    exact_mod_cast this
  have := pT_miss_A0 hw
  linarith

/-- An exceptional vertex sees fewer than `|pL| − w/40` light vertices. -/
theorem all_T_L_adj {w : V} (hw : w ∈ pT G A s) :
    (((pL G A s).filter (G.Adj w)).card : ℚ) < (pL G A s).card - scW V s / 40 := by
  have := pT_miss_L hw
  have := all_card_filter_not_q (pL G A s) (fun z => G.Adj w z)
  linarith

omit [Fintype V] [DecidableEq V] in
theorem all_choose_two_q (m : ℕ) : 2 * ((m.choose 2 : ℕ) : ℚ) = (m : ℚ) * ((m : ℚ) - 1) := by
  rcases m with _ | m
  · simp
  · have h2 := Nat.div_mul_cancel (Nat.even_mul_pred_self (m + 1)).two_dvd
    rw [Nat.add_sub_cancel] at h2
    rw [Nat.choose_two_right, Nat.add_sub_cancel]
    have : (((m + 1) * m / 2 : ℕ) : ℚ) * 2 = ((m + 1) * m : ℕ) := by exact_mod_cast h2
    push_cast at this ⊢
    linarith

variable (h : AllInput G A s)
include h

theorem AllInput.host_adj_le (w : V) :
    (((pHost G A s).filter (G.Adj w)).card : ℚ) ≤
      ((pL G A s).filter (G.Adj w)).card + 4 * (scW V s / 10 ^ 27) := by
  have := all_filter_union_le (pL G A s) (pYr G A s) (G.Adj w)
  have : (((pHost G A s).filter (G.Adj w)).card : ℚ) ≤
      ((pL G A s).filter (G.Adj w)).card + (pYr G A s).card := by exact_mod_cast this
  have := h.card_Yr
  linarith

set_option maxHeartbeats 4000000 in
/-- **The joint exact accounting.** -/
theorem AllInput.hkey (L : ℕ) (hL : (L : ℚ) ≤ scW V s / 10 ^ 13 + 1) :
    ((∑ w ∈ pT G A s, G.degree w : ℕ) : ℚ) + 2 * ((pT G A s).card : ℕ) * (L + ((pT G A s).card : ℕ)) +
        (((pCore G A s).card.choose 2 : ℕ) : ℚ) + (((s + 1).choose 2 : ℕ) : ℚ) ≤
      ((inEdges G (pCore G A s)).card : ℕ) +
        2 * ((∑ w ∈ pT G A s, min ((pCore G A s).filter (G.Adj w)).card
          ((pHost G A s).filter (G.Adj w)).card : ℕ) : ℚ) + (s : ℚ) * ((pCore G A s).card : ℕ) +
        ((pT G A s).card : ℕ) * ((((pCore G A s).card + (pHost G A s).card + s : ℕ) : ℚ)) / 3 := by
  -- scales
  have hn0 := h.n_pos
  have hv := h.v_pos; have hvw := h.v_le_w; have hwn := h.w_le_n
  have hw0 : 0 < scW V s := hv.trans_le hvw
  have hSS := h.S_le_w
  have hS1 := (S_ge_one (s := s))
  have hS2 : (1 : ℚ) ≤ ((s : ℚ) + 1) ^ 2 := one_le_pow₀ hS1
  have hw50 : (10 : ℚ) ^ 50 ≤ scW V s := by nlinarith only [hSS, hS2]
  have hSw := h.Sw_le_n
  have hSw' := h.S_le_w'
  have hvS : ((s : ℚ) + 1) * scV V s ≤ Fintype.card V := by
    have : ((s : ℚ) + 1) * scV V s ≤ ((s : ℚ) + 1) * scW V s :=
      mul_le_mul_of_nonneg_left hvw (by positivity)
    linarith
  have hWq := h.card_T
  have hSlo := h.card_core_lo
  have hShi := h.card_core_hi
  have hLlo := h.card_L_lo
  have hLhi := h.card_L_hi
  have htot := card_total (G := G) (A := A) (s := s)
  have htotq : ((pCore G A s).card : ℚ) + (pHost G A s).card + (pT G A s).card =
      (Fintype.card V : ℚ) := by exact_mod_cast htot
  set w := scW V s with hwdef
  set vv := scV V s with hvvdef
  set n := (Fintype.card V : ℚ) with hndef
  set c := (pCore G A s).card with hcdef
  set b := (pHost G A s).card with hbdef
  set k := (pT G A s).card with hkdef
  set lL := (pL G A s).card with hlLdef
  have hL0 : (0 : ℚ) ≤ L := by positivity
  have hk0 : (0 : ℚ) ≤ k := by positivity
  have hs0 : (0 : ℚ) ≤ s := by positivity
  -- the core: `ν` and Erdős–Gallai
  obtain ⟨ν, hνs, hHas, hno⟩ := h.exists_nu
  obtain ⟨P, hP, hPc, hPm⟩ := hHas
  have hEG := h.core_eg hνs hno
  have hEGq : ((c.choose 2 : ℕ) : ℚ) + (((ν + 1).choose 2 : ℕ) : ℚ) ≤
      ((inEdges G (pCore G A s)).card : ℚ) + ν * c := by exact_mod_cast hEG
  have hchs := all_choose_two_q (s + 1)
  have hchν := all_choose_two_q (ν + 1)
  push_cast at hchs hchν
  have hνq : (ν : ℚ) ≤ s := by exact_mod_cast hνs
  have hν0 : (0 : ℚ) ≤ ν := by positivity
  -- per-vertex quantities
  set u : V → ℕ := fun t => ((pCore G A s).filter (G.Adj t)).card with hu
  set vh : V → ℕ := fun t => ((pHost G A s).filter (G.Adj t)).card with hvh
  set vl : V → ℕ := fun t => ((pL G A s).filter (G.Adj t)).card with hvl
  set e1 : ℚ := 4 * k + 2 * L + 4 * (w / 10 ^ 27) with he1
  set g : V → ℚ := fun t => (G.degree t : ℚ) - 2 * ((min (u t) (vh t) : ℕ) : ℚ) +
    2 * ((L : ℚ) + k) - ((c + b + s : ℕ) : ℚ) / 3 with hg
  set Big : V → Prop := fun t => n / 3 - w / 400 < (vh t : ℚ) - u t with hBig
  have hcbs : n - k ≤ ((c + b + s : ℕ) : ℚ) := by push_cast; linarith
  have hgw : ∀ t ∈ pT G A s, g t ≤ if Big t then (vl t : ℚ) - n / 3 + e1 else 0 := by
    intro t ht
    have hex : (G.degree t : ℚ) - 2 * ((min (u t) (vh t) : ℕ) : ℚ) ≤
        max ((u t : ℚ) - vh t) ((vh t : ℚ) - u t) + k :=
      all_excess _ (u t) (vh t) k (all_degree_le_uvw (G := G) (A := A) (s := s) t)
    have hu1 : (u t : ℚ) < c - w / 200 := all_T_core_adj ht
    have hu0 : (0 : ℚ) ≤ u t := by positivity
    have hv0 : (0 : ℚ) ≤ vh t := by positivity
    have hvl1 : (vh t : ℚ) ≤ vl t + 4 * (w / 10 ^ 27) := h.host_adj_le t
    have hgdef : g t = (G.degree t : ℚ) - 2 * ((min (u t) (vh t) : ℕ) : ℚ) +
        2 * ((L : ℚ) + k) - ((c + b + s : ℕ) : ℚ) / 3 := rfl
    split_ifs with hB
    · have hB' : n / 3 - w / 400 < (vh t : ℚ) - u t := hB
      have hmax : max ((u t : ℚ) - vh t) ((vh t : ℚ) - u t) ≤ (vh t : ℚ) - u t := by
        apply max_le <;> linarith
      rw [hgdef]
      linarith
    · have hB' : (vh t : ℚ) - u t ≤ n / 3 - w / 400 := by
        by_contra hc; push_neg at hc; exact hB hc
      have hmax : max ((u t : ℚ) - vh t) ((vh t : ℚ) - u t) ≤ n / 3 - w / 400 := by
        apply max_le _ hB'
        linarith
      rw [hgdef]
      linarith
  have hsum1 : ∑ t ∈ pT G A s, g t ≤
      ∑ t ∈ pT G A s, (if Big t then (vl t : ℚ) - n / 3 + e1 else 0) := sum_le_sum hgw
  rw [← sum_filter] at hsum1
  set X := (pT G A s).filter Big with hX
  have hXT : X ⊆ pT G A s := filter_subset _ _
  have hXbig : ∀ t ∈ X, n / 3 - w / 400 - 4 * (w / 10 ^ 27) < (vl t : ℚ) := by
    intro t ht
    obtain ⟨-, hBt⟩ := mem_filter.1 ht
    have hvl1 : (vh t : ℚ) ≤ vl t + 4 * (w / 10 ^ 27) := h.host_adj_le t
    have hu0 : (0 : ℚ) ≤ u t := by positivity
    have hB' : n / 3 - w / 400 < (vh t : ℚ) - u t := hBt
    linarith
  -- at most `2s + 1` big vertices
  have hj : X.card ≤ 2 * s + 1 := by
    by_contra hc
    push_neg at hc
    obtain ⟨X', hX'X, hX'c⟩ := exists_subset_card_eq (show 2 * (s + 1) ≤ X.card by omega)
    have hjt := h.joint hP hPm (by omega) X' (hX'X.trans hXT) hX'c.le
    have hlow : ((2 * (s + 1) : ℕ) : ℚ) * (n / 3 - w / 400 - 4 * (w / 10 ^ 27)) ≤
        ∑ t ∈ X', ((vl t : ℕ) : ℚ) := by
      have := card_nsmul_le_sum X' (fun t => ((vl t : ℕ) : ℚ))
        (n / 3 - w / 400 - 4 * (w / 10 ^ 27)) (fun t ht => (hXbig t (hX'X ht)).le)
      rw [nsmul_eq_mul, hX'c] at this
      exact this
    have hsP : (((s - P.card : ℕ) : ℚ)) ≤ s := by
      have : s - P.card ≤ s := Nat.sub_le _ _
      exact_mod_cast this
    have hlL0 : (0 : ℚ) ≤ lL := by positivity
    have m1 : ((s - P.card : ℕ) : ℚ) * lL ≤ (s : ℚ) * lL := mul_le_mul_of_nonneg_right hsP hlL0
    have m2 : (s : ℚ) * lL ≤ (s : ℚ) * (2 * n / 3 + 2 * (vv / 10 ^ 31)) :=
      mul_le_mul_of_nonneg_left hLhi hs0
    have m3 : (s : ℚ) * vv ≤ ((s : ℚ) + 1) * vv := mul_le_mul_of_nonneg_right (by linarith) hv.le
    push_cast at hlow
    have hjt' : ∑ t ∈ X', ((vl t : ℕ) : ℚ) ≤ ((s - P.card : ℕ) : ℚ) * lL + n / 9 := hjt
    nlinarith only [hS2, hSS, hv, hwn, hSw, hvS, hjt, m1, m2, hlow]
  have hjq : (X.card : ℚ) ≤ 2 * ((s : ℚ) + 1) := by
    have : (X.card : ℚ) ≤ 2 * s + 1 := by exact_mod_cast hj
    linarith
  have hj0 : (0 : ℚ) ≤ X.card := by positivity
  -- the budget reduces to `Σ_T g + C(c,2) − e_C + C(s+1,2) ≤ s c`
  have hsumg : ∑ t ∈ pT G A s, g t = ((∑ w ∈ pT G A s, G.degree w : ℕ) : ℚ) -
      2 * ((∑ w ∈ pT G A s, min (u w) (vh w) : ℕ) : ℚ) + k * (2 * ((L : ℚ) + k)) -
      k * (((c + b + s : ℕ) : ℚ) / 3) := by
    simp only [hg]
    rw [sum_sub_distrib, sum_add_distrib, sum_sub_distrib, ← mul_sum, sum_const, sum_const,
      nsmul_eq_mul, nsmul_eq_mul]
    push_cast
    ring
  -- bounds on `Σ_X`
  have hXsum : ∑ t ∈ X, ((vl t : ℚ) - n / 3 + e1) =
      ∑ t ∈ X, (vl t : ℚ) - X.card * (n / 3 - e1) := by
    rw [sum_add_distrib, sum_sub_distrib, sum_const, sum_const, nsmul_eq_mul, nsmul_eq_mul]
    ring
  have hδ : (lL : ℚ) - n / 3 ≤ c + 4 * (vv / 10 ^ 31) := by linarith
  have he1 : e1 ≤ 16 * (w / 10 ^ 27) + 2 * (w / 10 ^ 13) + 2 + 4 * (w / 10 ^ 27) := by
    simp only [he1]; linarith
  have hsν : ((s - ν : ℕ) : ℚ) = (s : ℚ) - ν := by push_cast [Nat.cast_sub hνs]; ring
  have hcν : (s : ℚ) + ν + 1 ≤ c := by nlinarith only [hS2, hSS, hSw', hvw, hwn, hSlo, hνq]
  set M : ℚ := ((c.choose 2 : ℕ) : ℚ) - ((inEdges G (pCore G A s)).card : ℚ) with hM
  have hMb : M ≤ ν * c - (((ν + 1).choose 2 : ℕ) : ℚ) := by simp only [hM]; linarith
  have hmain : ∑ t ∈ X, ((vl t : ℚ) - n / 3 + e1) + M + (((s + 1).choose 2 : ℕ) : ℚ) ≤ s * c := by
    rcases Nat.eq_zero_or_pos X.card with hj0' | hjpos
    · -- no big vertex
      rw [card_eq_zero.1 hj0', sum_empty]
      have : ((s : ℚ) - ν) * (c - ((s : ℚ) + ν + 1) / 2) ≥ 0 :=
        mul_nonneg (by linarith) (by linarith)
      nlinarith only [hEGq, hchs, hchν, this]
    · by_cases hcase : X.card + ν ≤ s
      · -- each big vertex costs at most `c − w/40 + o(w)`
        have hper : ∀ t ∈ X, (vl t : ℚ) - n / 3 + e1 ≤ lL - w / 40 - n / 3 + e1 := by
          intro t ht
          have := all_T_L_adj (hXT ht)
          linarith
        have hs1 := sum_le_sum hper
        rw [sum_const, nsmul_eq_mul] at hs1
        set K : ℚ := lL - n / 3 - c - w / 40 + e1 with hK
        have hKneg : K ≤ -(w / 80) := by simp only [hK]; linarith
        have hjc : (X.card : ℚ) + ν ≤ s := by exact_mod_cast hcase
        have hj1 : (1 : ℚ) ≤ X.card := by exact_mod_cast hjpos
        have hc0 : (0 : ℚ) ≤ c := by positivity
        have p1 : ((X.card : ℚ) - 1) * K ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
        have p2 : ((s : ℚ) - ν - X.card) * c ≥ 0 := mul_nonneg (by linarith) hc0
        have hid : (X.card : ℚ) * (lL - w / 40 - n / 3 + e1) = X.card * c + X.card * K := by
          simp only [hK]; ring
        have hsq : (s : ℚ) * ((s : ℚ) + 1) ≤ ((s : ℚ) + 1) ^ 2 := by nlinarith only [hjc, hj1]
        nlinarith only [hL, hSS, hSw', hvw, hSlo, hWq, hLhi, hEGq, hchs, he1, hs1, hK, hjc, hj1, p1, p2, hid]
      · -- joint incidence
        push_neg at hcase
        have hjt := h.joint hP hPm (by omega) X hXT (by omega)
        rw [hPc, hsν] at hjt
        have hjs : (s : ℚ) - ν + 1 ≤ X.card := by
          have : s + 1 ≤ X.card + ν := by omega
          have : ((s + 1 : ℕ) : ℚ) ≤ X.card + ν := by exact_mod_cast this
          push_cast at this; linarith
        have hne1 : 0 ≤ n / 3 - e1 := by linarith
        have p1 : ((s : ℚ) - ν + 1) * (n / 3 - e1) ≤ X.card * (n / 3 - e1) :=
          mul_le_mul_of_nonneg_right hjs hne1
        have p2 : ((s : ℚ) - ν) * (lL - n / 3) ≤ ((s : ℚ) - ν) * (c + 4 * (vv / 10 ^ 31)) :=
          mul_le_mul_of_nonneg_left hδ (by linarith)
        have p3 : ((s : ℚ) - ν + 1) * e1 ≤ ((s : ℚ) + 1) * e1 :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        have p4 : ((s : ℚ) - ν) * vv ≤ ((s : ℚ) + 1) * vv :=
          mul_le_mul_of_nonneg_right (by linarith) hv.le
        have p5 : ((s : ℚ) + 1) * e1 ≤ ((s : ℚ) + 1) * (20 * (w / 10 ^ 27) + 2 * (w / 10 ^ 13) + 2) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        have hsq : (s : ℚ) * ((s : ℚ) + 1) ≤ ((s : ℚ) + 1) ^ 2 := by nlinarith only []
        rw [hXsum]
        nlinarith only [hS2, hSS, hSw', hwn, hSw, hvS, hEGq, hchs, hjt, p1, p2, p3, p4, p5]
  have hfin : ∑ t ∈ pT G A s, g t + M + (((s + 1).choose 2 : ℕ) : ℚ) ≤ s * c := by linarith
  rw [hsumg] at hfin
  simp only [hM] at hfin
  have hkcb : ((c + b + s : ℕ) : ℚ) = (c : ℚ) + b + s := by push_cast; ring
  push_cast at hfin ⊢
  nlinarith only [hfin]

end A4S1.IndepAll
