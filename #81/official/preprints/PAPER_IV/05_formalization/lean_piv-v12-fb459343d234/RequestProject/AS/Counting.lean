module

public import RequestProject.AFKS.Corollary42

/-!
# Regular pairs and the induced counting lemma (Lemma 3.2 of Alon–Shapira)

* `IsRegularPair.mono`: `γ`-regularity implies `γ'`-regularity for `γ ≤ γ'`.
* `IsRegularPair.sub` (Claim 5.1 of Alon–Shapira): large subsets of a regular pair form a
  regular pair.
* `counting_lemma` (Lemma 3.2 of Alon–Shapira): if `U₁, …, U_f` are pairwise `γ`-regular and
  their densities are `≥ η` along the edges of `F` and `≤ 1 - η` along the non-edges of `F`, then
  at least `δ ∏ |Uᵢ|` of the tuples `(u₁, …, u_f) ∈ U₁ × ⋯ × U_f` span an induced copy of `F`
  (with `uᵢ` playing the role of vertex `i`).
-/

@[expose] public section

open Finset Fintype AFKS

open scoped Classical

universe u

namespace AlonShapira

variable {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]

theorem IsRegularPair.mono {γ γ' : ℝ} (hγ : γ ≤ γ') {A B : Finset V}
    (h : IsRegularPair G γ A B) : IsRegularPair G γ' A B := by
  intro A' hA' B' hB' hA'c hB'c
  have h0 : (0 : ℝ) ≤ #A := by positivity
  have h1 : (0 : ℝ) ≤ #B := by positivity
  exact (h A' hA' B' hB' (le_trans (by nlinarith) hA'c) (le_trans (by nlinarith) hB'c)).trans hγ

/-- **Claim 5.1 of Alon–Shapira.** If `(A, B)` is `γ`-regular and `A' ⊆ A`, `B' ⊆ B` have
`|A'| ≥ ξ|A|`, `|B'| ≥ ξ|B|` with `ξ ≥ γ`, then `(A', B')` is `max (2γ) (γ/ξ)`-regular. -/
theorem IsRegularPair.sub {γ ξ : ℝ} (hγ : 0 < γ) (hξ : γ ≤ ξ) {A B A' B' : Finset V}
    (h : IsRegularPair G γ A B) (hA : A' ⊆ A) (hB : B' ⊆ B) (hAc : ξ * #A ≤ #A')
    (hBc : ξ * #B ≤ #B') : IsRegularPair G (max (2 * γ) (γ / ξ)) A' B' := by
  intro A'' hA'' B'' hB'' hA''c hB''c
  have hξ0 : 0 < ξ := lt_of_lt_of_le hγ hξ
  have h0 : (0 : ℝ) ≤ #A := by positivity
  have h1 : (0 : ℝ) ≤ #B := by positivity
  have hA2 : γ * #A ≤ #A'' := by
    have : γ / ξ * #A' ≤ #A'' := le_trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
      (by positivity)) hA''c
    calc γ * #A = γ / ξ * (ξ * #A) := by field_simp
      _ ≤ γ / ξ * #A' := mul_le_mul_of_nonneg_left hAc (by positivity)
      _ ≤ _ := this
  have hB2 : γ * #B ≤ #B'' := by
    have : γ / ξ * #B' ≤ #B'' := le_trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
      (by positivity)) hB''c
    calc γ * #B = γ / ξ * (ξ * #B) := by field_simp
      _ ≤ γ / ξ * #B' := mul_le_mul_of_nonneg_left hBc (by positivity)
      _ ≤ _ := this
  have e1 := h A'' (hA''.trans hA) B'' (hB''.trans hB) hA2 hB2
  have e2 := h A' hA B' hB (le_trans (by nlinarith) hAc) (le_trans (by nlinarith) hBc)
  have : |dens G A'' B'' - dens G A' B'| ≤ 2 * γ := by
    calc |dens G A'' B'' - dens G A' B'|
        = |(dens G A'' B'' - dens G A B) - (dens G A' B' - dens G A B)| := by ring_nf
      _ ≤ |dens G A'' B'' - dens G A B| + |dens G A' B' - dens G A B| := abs_sub _ _
      _ ≤ 2 * γ := by linarith
  exact this.trans (le_max_left _ _)


/-- Number of neighbours of `x` in `B`, as a double sum of edge indicators. -/
theorem sum_ind_eq_card (x : V) (B : Finset V) :
    ∑ b ∈ B, ind G x b = #(B.filter (G.Adj x)) := by
  unfold ind
  rw [Finset.card_filter]; push_cast; rfl

/-- In a `γ`-regular pair `(A, B)`, fewer than `γ|A|` vertices of `A` have fewer than
`(d(A,B) - γ)|B|` neighbours in `B`. -/
theorem card_low_degree_lt {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) {A B : Finset V}
    (hA : A.Nonempty) (hB : B.Nonempty) (h : IsRegularPair G γ A B) :
    (#(A.filter fun x => (#(B.filter (G.Adj x)) : ℝ) < (dens G A B - γ) * #B) : ℝ) <
      γ * #A := by
  set A' := A.filter fun x => (#(B.filter (G.Adj x)) : ℝ) < (dens G A B - γ) * #B
  by_contra hc
  push_neg at hc
  have hApos : (0 : ℝ) < #A := by exact_mod_cast hA.card_pos
  have hA'ne : A'.Nonempty := by
    have : (0 : ℝ) < #A' := lt_of_lt_of_le (by positivity) hc
    rw [← Finset.card_pos]; exact_mod_cast this
  have hBpos : (0 : ℝ) < #B := by exact_mod_cast hB.card_pos
  have hd := h A' (Finset.filter_subset _ _) B subset_rfl hc (by nlinarith)
  have he := card_mul_card_mul_dens G hA'ne hB
  have hsum : ∑ a ∈ A', ∑ b ∈ B, ind G a b < ∑ a ∈ A', (dens G A B - γ) * #B := by
    refine Finset.sum_lt_sum_of_nonempty hA'ne fun a ha => ?_
    rw [sum_ind_eq_card]; exact (Finset.mem_filter.1 ha).2
  rw [Finset.sum_const, nsmul_eq_mul, ← he] at hsum
  have hA'pos : (0 : ℝ) < #A' := by exact_mod_cast hA'ne.card_pos
  have : dens G A' B < dens G A B - γ := by
    by_contra hh; push_neg at hh
    have := mul_le_mul_of_nonneg_left hh (by positivity : (0 : ℝ) ≤ #A' * #B)
    nlinarith
  rw [abs_le] at hd
  linarith [hd.1]

/-- In a `γ`-regular pair `(A, B)`, fewer than `γ|A|` vertices of `A` have fewer than
`(1 - d(A,B) - γ)|B|` non-neighbours in `B`. -/
theorem card_low_codegree_lt {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) {A B : Finset V}
    (hA : A.Nonempty) (hB : B.Nonempty) (h : IsRegularPair G γ A B) :
    (#(A.filter fun x => (#(B.filter fun y => ¬ G.Adj x y) : ℝ) <
      (1 - dens G A B - γ) * #B) : ℝ) < γ * #A := by
  set A' := A.filter fun x => (#(B.filter fun y => ¬ G.Adj x y) : ℝ) < (1 - dens G A B - γ) * #B
  by_contra hc
  push_neg at hc
  have hApos : (0 : ℝ) < #A := by exact_mod_cast hA.card_pos
  have hA'ne : A'.Nonempty := by
    have : (0 : ℝ) < #A' := lt_of_lt_of_le (by positivity) hc
    rw [← Finset.card_pos]; exact_mod_cast this
  have hBpos : (0 : ℝ) < #B := by exact_mod_cast hB.card_pos
  have hd := h A' (Finset.filter_subset _ _) B subset_rfl hc (by nlinarith)
  have he := card_mul_card_mul_dens G hA'ne hB
  have hsum : ∑ a ∈ A', (dens G A B + γ) * #B < ∑ a ∈ A', ∑ b ∈ B, ind G a b := by
    refine Finset.sum_lt_sum_of_nonempty hA'ne fun a ha => ?_
    rw [sum_ind_eq_card]
    have h1 := (Finset.mem_filter.1 ha).2
    have h2 : (#(B.filter (G.Adj a)) : ℝ) + #(B.filter fun y => ¬ G.Adj a y) = #B := by
      exact_mod_cast Finset.card_filter_add_card_filter_not (s := B) (p := G.Adj a)
    nlinarith
  rw [Finset.sum_const, nsmul_eq_mul, ← he] at hsum
  have hA'pos : (0 : ℝ) < #A' := by exact_mod_cast hA'ne.card_pos
  have : dens G A B + γ < dens G A' B := by
    by_contra hh; push_neg at hh
    have := mul_le_mul_of_nonneg_left hh (by positivity : (0 : ℝ) ≤ #A' * #B)
    nlinarith
  rw [abs_le] at hd
  linarith [hd.2]


/-- Tuples of `∏ Uᵢ` spanning an induced copy of `F`, with `uᵢ` playing the role of `i`. -/
noncomputable def inducedTuples {V : Type*} (G : SimpleGraph V) {f : ℕ} (F : SimpleGraph (Fin f))
    (U : Fin f → Finset V) : Finset (Fin f → V) :=
  (piFinset U).filter fun u => ∀ i j, F.Adj i j ↔ G.Adj (u i) (u j)

theorem mem_inducedTuples {V : Type*} (G : SimpleGraph V) {f : ℕ} (F : SimpleGraph (Fin f))
    (U : Fin f → Finset V) (u : Fin f → V) :
    u ∈ inducedTuples G F U ↔ (∀ i, u i ∈ U i) ∧ ∀ i j, F.Adj i j ↔ G.Adj (u i) (u j) := by
  unfold inducedTuples
  rw [Finset.mem_filter, Fintype.mem_piFinset]

/-- **Lemma 3.2 of Alon–Shapira (induced counting lemma).** For every `0 < η ≤ 1` and `f` there
are `γ > 0` and `δ > 0` such that: if `U₁, …, U_f` are pairwise `γ`-regular, `d(Uᵢ, Uⱼ) ≥ η` when
`ij ∈ E(F)` and `d(Uᵢ, Uⱼ) ≤ 1 - η` when `ij ∉ E(F)`, then at least `δ ∏ |Uᵢ|` tuples
`(u₁, …, u_f) ∈ U₁ × ⋯ × U_f` span an induced copy of `F` with `uᵢ` playing the role of `i`. -/
theorem counting_lemma (f : ℕ) : ∀ η : ℝ, 0 < η → η ≤ 1 → ∃ γ > (0 : ℝ), ∃ δ > (0 : ℝ),
    ∀ {V : Type u} (G : SimpleGraph V) [DecidableRel G.Adj] (F : SimpleGraph (Fin f))
      (U : Fin f → Finset V),
      (∀ i j, i ≠ j → IsRegularPair G γ (U i) (U j)) →
      (∀ i j, F.Adj i j → η ≤ dens G (U i) (U j)) →
      (∀ i j, i ≠ j → ¬ F.Adj i j → dens G (U i) (U j) ≤ 1 - η) →
      δ * ∏ i, (#(U i) : ℝ) ≤ #(inducedTuples G F U) := by
  induction f with
  | zero =>
    intro η _ _
    refine ⟨1, one_pos, 1, one_pos, fun G _ F U _ _ _ => ?_⟩
    have : inducedTuples G F U = piFinset U := by
      unfold inducedTuples
      exact Finset.filter_true_of_mem fun u _ i => i.elim0
    rw [this, card_piFinset]
    simp
  | succ f ih =>
    intro η hη hη1
    obtain ⟨γ', hγ', δ', hδ', h'⟩ := ih (η / 2) (by positivity) (by linarith)
    set γ : ℝ := min (min (η / 2) (γ' * η / 2)) (1 / (2 * ((f : ℝ) + 1))) with hγdef
    have hγpos : 0 < γ := by positivity
    have hγ1 : γ ≤ η / 2 := le_trans (min_le_left _ _) (min_le_left _ _)
    have hγ2 : γ ≤ γ' * η / 2 := le_trans (min_le_left _ _) (min_le_right _ _)
    have hγ3 : γ ≤ 1 / (2 * ((f : ℝ) + 1)) := min_le_right _ _
    refine ⟨γ, hγpos, δ' * (η / 2) ^ f / 2, by positivity, ?_⟩
    intro V G _ F U hreg hadj hnadj
    by_cases hne : ∀ i, (U i).Nonempty
    swap
    · push_neg at hne
      obtain ⟨i, hi⟩ := hne
      have : ∏ i, (#(U i) : ℝ) = 0 := Finset.prod_eq_zero (mem_univ i) (by simp [hi])
      rw [this, mul_zero]; positivity
    set F' : SimpleGraph (Fin f) := F.comap Fin.succ with hF'
    set T : V → Fin f → Finset V := fun x j =>
      if F.Adj 0 j.succ then (U j.succ).filter (G.Adj x)
      else (U j.succ).filter (fun y => ¬ G.Adj x y) with hT
    have hTsub : ∀ x j, T x j ⊆ U j.succ := fun x j => by
      simp only [hT]; split_ifs <;> exact Finset.filter_subset _ _
    set typ := (U 0).filter (fun x => ∀ j, (η / 2) * #(U j.succ) ≤ #(T x j)) with htyp
    -- bad vertices for coordinate `j`
    set Bad : Fin f → Finset V := fun j =>
      (U 0).filter (fun x => (#(T x j) : ℝ) < (η / 2) * #(U j.succ)) with hBad
    have hBadc : ∀ j, (#(Bad j) : ℝ) < γ * #(U 0) := by
      intro j
      have hr := hreg 0 j.succ (Fin.succ_ne_zero j).symm
      by_cases hj : F.Adj 0 j.succ
      · refine lt_of_le_of_lt ?_ (card_low_degree_lt G hγpos (by linarith) (hne 0) (hne _) hr)
        gcongr
        intro x hx
        simp only [hBad, hT, if_pos hj, Finset.mem_filter] at hx ⊢
        refine ⟨hx.1, lt_of_lt_of_le hx.2 ?_⟩
        have := hadj 0 j.succ hj
        gcongr; linarith
      · refine lt_of_le_of_lt ?_ (card_low_codegree_lt G hγpos (by linarith) (hne 0) (hne _) hr)
        gcongr
        intro x hx
        simp only [hBad, hT, if_neg hj, Finset.mem_filter] at hx ⊢
        refine ⟨hx.1, lt_of_lt_of_le hx.2 ?_⟩
        have := hnadj 0 j.succ (Fin.succ_ne_zero j).symm hj
        gcongr; linarith
    have hU0 : (#(U 0) : ℝ) / 2 ≤ #typ := by
      have hsub : U 0 ⊆ typ ∪ univ.biUnion Bad := by
        intro x hx
        by_cases hxt : ∀ j, (η / 2) * #(U j.succ) ≤ #(T x j)
        · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hx, hxt⟩)
        · push_neg at hxt
          obtain ⟨j, hj⟩ := hxt
          exact Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨j, mem_univ _,
            Finset.mem_filter.2 ⟨hx, hj⟩⟩)
      have h1 : (#(U 0) : ℝ) ≤ #typ + ∑ j, (#(Bad j) : ℝ) := by
        have := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
        have h2 := Finset.card_biUnion_le (s := univ) (t := Bad)
        exact_mod_cast this.trans (Nat.add_le_add_left h2 _)
      have h2 : ∑ j, (#(Bad j) : ℝ) ≤ f * (γ * #(U 0)) := by
        calc ∑ j, (#(Bad j) : ℝ) ≤ ∑ _j : Fin f, γ * #(U 0) :=
              Finset.sum_le_sum fun j _ => (hBadc j).le
          _ = f * (γ * #(U 0)) := by simp
      have h3 : (f : ℝ) * γ ≤ 1 / 2 := by
        calc (f : ℝ) * γ ≤ f * (1 / (2 * ((f : ℝ) + 1))) := by gcongr
          _ ≤ 1 / 2 := by
            rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
      have h4 : (0 : ℝ) ≤ #(U 0) := by positivity
      nlinarith
    -- counting the extensions of each typical vertex
    have hcount : ∀ x ∈ typ, δ' * (η / 2) ^ f * ∏ j : Fin f, (#(U j.succ) : ℝ) ≤
        #(inducedTuples G F' (T x)) := by
      intro x hx
      have hxT : ∀ j, (η / 2) * #(U j.succ) ≤ #(T x j) := (Finset.mem_filter.1 hx).2
      have hγU : ∀ j, γ * #(U j.succ) ≤ #(T x j) := fun j =>
        le_trans (by gcongr) (hxT j)
      have hmain := h' G F' (T x) ?_ ?_ ?_
      · refine le_trans ?_ hmain
        rw [mul_assoc]
        gcongr
        calc (η / 2) ^ f * ∏ j : Fin f, (#(U j.succ) : ℝ)
            = ∏ j : Fin f, ((η / 2) * #(U j.succ)) := by
              rw [Finset.prod_mul_distrib, Finset.prod_const, card_univ, Fintype.card_fin]
          _ ≤ ∏ j : Fin f, (#(T x j) : ℝ) :=
              Finset.prod_le_prod (fun j _ => by positivity) fun j _ => hxT j
      · intro i j hij
        have hr := hreg i.succ j.succ (fun h => hij (Fin.succ_injective _ h))
        have := IsRegularPair.sub G hγpos hγ1 hr (hTsub x i) (hTsub x j) (hxT i) (hxT j)
        refine IsRegularPair.mono G ?_ this
        refine max_le (by nlinarith) ?_
        rw [div_le_iff₀ (by positivity)]; linarith
      · intro i j hij
        have hij' : i ≠ j := hij.ne
        have hr := hreg i.succ j.succ (fun h => hij' (Fin.succ_injective _ h))
        have hd := hr _ (hTsub x i) _ (hTsub x j) (hγU i) (hγU j)
        have := hadj i.succ j.succ hij
        rw [abs_le] at hd; linarith
      · intro i j hij hnij
        have hr := hreg i.succ j.succ (fun h => hij (Fin.succ_injective _ h))
        have hd := hr _ (hTsub x i) _ (hTsub x j) (hγU i) (hγU j)
        have := hnadj i.succ j.succ (fun h => hij (Fin.succ_injective _ h)) hnij
        rw [abs_le] at hd; linarith
    -- the extensions give distinct induced tuples
    have hinj : ∑ x ∈ typ, (#(inducedTuples G F' (T x)) : ℝ) ≤ #(inducedTuples G F U) := by
      have := Finset.card_le_card_of_injOn (s := typ.sigma fun x => inducedTuples G F' (T x))
        (t := inducedTuples G F U) (fun p => (Fin.cons p.1 p.2 : Fin (f + 1) → V)) ?_ ?_
      · rw [Finset.card_sigma] at this
        exact_mod_cast this
      · intro p hp
        rw [Finset.mem_coe, Finset.mem_sigma] at hp
        obtain ⟨hx, hw⟩ := hp
        rw [mem_inducedTuples] at hw
        rw [Finset.mem_coe, mem_inducedTuples]
        have hwT : ∀ j, p.2 j ∈ T p.1 j := hw.1
        have hx0 : p.1 ∈ U 0 := (Finset.mem_filter.1 hx).1
        have key0 : ∀ j, F.Adj 0 j.succ ↔ G.Adj p.1 (p.2 j) := by
          intro j
          have := hwT j
          simp only [hT] at this
          split_ifs at this with hj
          · exact ⟨fun _ => (Finset.mem_filter.1 this).2, fun _ => hj⟩
          · exact ⟨fun h => absurd h hj, fun h => absurd h (Finset.mem_filter.1 this).2⟩
        refine ⟨fun i => ?_, fun i j => ?_⟩
        · refine Fin.cases ?_ (fun j => ?_) i
          · simpa using hx0
          · simpa using hTsub _ _ (hwT j)
        · refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
          · simp
          · simpa using key0 j
          · simpa [F.adj_comm, G.adj_comm] using key0 i
          · simpa [hF'] using hw.2 i j
      · rintro ⟨x, w⟩ _ ⟨y, v⟩ _ hxy
        simp only [Fin.cons_inj] at hxy
        obtain ⟨rfl, rfl⟩ := hxy
        rfl
    calc δ' * (η / 2) ^ f / 2 * ∏ i, (#(U i) : ℝ)
        = (#(U 0) : ℝ) / 2 * (δ' * (η / 2) ^ f * ∏ j : Fin f, (#(U j.succ) : ℝ)) := by
          rw [Fin.prod_univ_succ]; ring
      _ ≤ #typ * (δ' * (η / 2) ^ f * ∏ j : Fin f, (#(U j.succ) : ℝ)) := by
          gcongr
      _ = ∑ x ∈ typ, δ' * (η / 2) ^ f * ∏ j : Fin f, (#(U j.succ) : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ x ∈ typ, (#(inducedTuples G F' (T x)) : ℝ) := Finset.sum_le_sum hcount
      _ ≤ _ := hinj

end AlonShapira
