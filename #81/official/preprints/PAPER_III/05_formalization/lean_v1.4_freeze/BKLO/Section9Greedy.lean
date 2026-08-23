/-
# BKLO §9 for `r = 2`, `F = K₃`: the greedy step

Elementary bookkeeping for building an edge-disjoint triangle family greedily inside a graph with
a `(k, δ)`-partition, `δ ≥ 1/2 + γ`:

* degree and cardinality lemmas for adding one triangle to a family;
* `BKLO.card_high_deg_le` — few vertices have large degree in a sparse graph;
* `BKLO.codeg_ge` — any two vertices have at least `2γ|X|` common neighbours in every part `X`;
* `BKLO.exists_common_nbr` — the greedy step: a common neighbour in a prescribed part which avoids
  a small set of vertices, whose two connecting edges are unused, and which has small degree.

Everything here is `sorry`-free.
-/
import BKLO.Section9Vectors

open Finset

namespace BKLO

variable {V : Type*} [DecidableEq V]

/-! ### Degrees under adding edges -/

theorem edeg_union_le (F E : Finset (Sym2 V)) (v : V) :
    edeg (F ∪ E) v ≤ edeg F v + edeg E v := by
  classical
  have : (F ∪ E).filter (fun e => v ∈ e) ⊆ F.filter (fun e => v ∈ e) ∪ E.filter (fun e => v ∈ e) := by
    intro e he
    rcases Finset.mem_filter.1 he with ⟨heU, hve⟩
    rcases Finset.mem_union.1 heU with h | h
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨h, hve⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨h, hve⟩)
  exact le_trans (Finset.card_le_card this) (Finset.card_union_le _ _)

theorem edeg_union_triangle_le {T : Finset V} (hT : T.card = 3) (F : Finset (Sym2 V)) (v : V) :
    edeg (F ∪ cliqueEdges T) v ≤ edeg F v + 2 := by
  refine le_trans (edeg_union_le _ _ _) ?_
  rw [edeg_cliqueEdges hT]
  split <;> omega

theorem edeg_union_triangle_eq {T : Finset V} (hT : T.card = 3) (F : Finset (Sym2 V)) {v : V}
    (hv : v ∉ T) : edeg (F ∪ cliqueEdges T) v = edeg F v := by
  refine le_antisymm ?_ (edeg_mono Finset.subset_union_left v)
  refine le_trans (edeg_union_le _ _ _) ?_
  rw [edeg_cliqueEdges hT, if_neg hv]
  omega

/-! ### Adding a triangle to a family -/

theorem famEdges_insert (T : Finset V) (𝒯 : Finset (Finset V)) :
    famEdges (insert T 𝒯) = cliqueEdges T ∪ famEdges 𝒯 := by
  simp [famEdges, Finset.biUnion_insert]

theorem cliqueEdges_subset_famEdges {𝒯 : Finset (Finset V)} {T : Finset V} (h : T ∈ 𝒯) :
    cliqueEdges T ⊆ famEdges 𝒯 :=
  Finset.subset_biUnion_of_mem cliqueEdges h

theorem isTriFamily_insert {𝒯 : Finset (Finset V)} {T : Finset V} (h : IsTriFamily 𝒯)
    (hT : T.card = 3) (hd : Disjoint (cliqueEdges T) (famEdges 𝒯)) :
    IsTriFamily (insert T 𝒯) := by
  classical
  refine ⟨?_, ?_⟩
  · intro T' hT'
    rcases Finset.mem_insert.1 hT' with rfl | hT'
    · exact hT
    · exact h.card_three T' hT'
  · intro T₁ h₁ T₂ h₂ hne
    have key : ∀ T' ∈ 𝒯, Disjoint (cliqueEdges T) (cliqueEdges T') := fun T' hT' =>
      Finset.disjoint_of_subset_right (cliqueEdges_subset_famEdges hT') hd
    rcases Finset.mem_insert.1 h₁ with e₁ | m₁
    · rcases Finset.mem_insert.1 h₂ with e₂ | m₂
      · exact absurd (e₁.trans e₂.symm) hne
      · rw [e₁]; exact key T₂ m₂
    · rcases Finset.mem_insert.1 h₂ with e₂ | m₂
      · rw [e₂]; exact (key T₁ m₁).symm
      · exact h.edge_disjoint T₁ m₁ T₂ m₂ hne

theorem famEdges_card_le {𝒯 : Finset (Finset V)} (h : ∀ T ∈ 𝒯, T.card = 3) :
    (famEdges 𝒯).card ≤ 3 * 𝒯.card := by
  classical
  refine le_trans (Finset.card_biUnion_le) ?_
  have hsum : ∑ T ∈ 𝒯, (cliqueEdges T).card = 3 * 𝒯.card := by
    rw [Finset.sum_congr rfl fun T hT => cliqueEdges_card_three (h T hT)]
    simp [Finset.sum_const, Nat.mul_comm]
  exact le_of_eq hsum

/-! ### Counting vertices of large degree -/

theorem sum_edeg_le (F : Finset (Sym2 V)) (X : Finset V) :
    ∑ v ∈ X, edeg F v ≤ 2 * F.card := by
  classical
  have h1 : ∀ v : V, edeg F v = ∑ e ∈ F, if v ∈ e then 1 else 0 := by
    intro v; rw [edeg, Finset.card_filter]
  have h2 : ∑ v ∈ X, edeg F v = ∑ e ∈ F, ∑ v ∈ X, if v ∈ e then 1 else 0 := by
    simp_rw [h1]
    exact Finset.sum_comm
  have h3 : ∀ e ∈ F, (∑ v ∈ X, if v ∈ e then 1 else 0) ≤ 2 := by
    intro e _
    induction e using Sym2.ind with
    | _ p q =>
      have : (∑ v ∈ X, if v ∈ s(p, q) then 1 else 0) = (X.filter (fun v => v ∈ s(p, q))).card := by
        rw [Finset.card_filter]
      rw [this]
      refine le_trans (Finset.card_le_card (?_ : X.filter (fun v => v ∈ s(p, q)) ⊆ {p, q})) ?_
      · intro v hv
        have := (Finset.mem_filter.1 hv).2
        simpa [Sym2.mem_iff] using this
      · exact le_trans (Finset.card_insert_le _ _) (by simp)
  calc ∑ v ∈ X, edeg F v = ∑ e ∈ F, ∑ v ∈ X, (if v ∈ e then 1 else 0) := h2
    _ ≤ ∑ _e ∈ F, 2 := Finset.sum_le_sum h3
    _ = 2 * F.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

/-- Few vertices have degree exceeding `D`. -/
theorem card_high_deg_le (F : Finset (Sym2 V)) (X : Finset V) (D : ℕ) :
    (X.filter (fun z => ¬ edeg F z ≤ D)).card ≤ 2 * F.card / (D + 1) := by
  classical
  set Y := X.filter (fun z => ¬ edeg F z ≤ D) with hY
  have h1 : Y.card * (D + 1) ≤ ∑ v ∈ Y, edeg F v := by
    calc Y.card * (D + 1) = ∑ _v ∈ Y, (D + 1) := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ v ∈ Y, edeg F v := by
          refine Finset.sum_le_sum fun v hv => ?_
          have := (Finset.mem_filter.1 hv).2
          omega
  have h2 : ∑ v ∈ Y, edeg F v ≤ 2 * F.card :=
    le_trans (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)) (sum_edeg_le F X)
  exact Nat.le_div_iff_mul_le (Nat.succ_pos D) |>.2 (le_trans h1 h2)

/-! ### Common neighbourhoods -/

/-- In a `(k, δ)`-partition with `δ ≥ 1/2 + γ`, any two vertices of `S` have at least `2γ|X|`
common neighbours in every part `X`. -/
theorem codeg_ge {G : Finset (Sym2 V)} {S : Finset V} {P : Finset (Finset V)} {γ : ℝ}
    (hdeg : ∀ x ∈ S, ∀ W ∈ P, (1 / 2 + γ) * (W.card : ℝ) ≤ (degTo G x W : ℝ))
    {x y : V} (hx : x ∈ S) (hy : y ∈ S) {X : Finset V} (hX : X ∈ P) :
    2 * γ * (X.card : ℝ) ≤ ((nbhdIn G x X ∩ nbhdIn G y X).card : ℝ) := by
  classical
  have hcard : (nbhdIn G x X ∩ nbhdIn G y X).card + (nbhdIn G x X ∪ nbhdIn G y X).card
      = (nbhdIn G x X).card + (nbhdIn G y X).card := Finset.card_inter_add_card_union _ _
  have hunion : (nbhdIn G x X ∪ nbhdIn G y X).card ≤ X.card :=
    Finset.card_le_card (Finset.union_subset (nbhdIn_subset _ _ _) (nbhdIn_subset _ _ _))
  have hx' := hdeg x hx X hX
  have hy' := hdeg y hy X hX
  have hkey : ((nbhdIn G x X).card : ℝ) + ((nbhdIn G y X).card : ℝ)
      ≤ ((nbhdIn G x X ∩ nbhdIn G y X).card : ℝ) + (X.card : ℝ) := by
    have := hcard
    have h2 : ((nbhdIn G x X ∩ nbhdIn G y X).card : ℝ) + ((nbhdIn G x X ∪ nbhdIn G y X).card : ℝ)
        = ((nbhdIn G x X).card : ℝ) + ((nbhdIn G y X).card : ℝ) := by exact_mod_cast this
    have h3 : ((nbhdIn G x X ∪ nbhdIn G y X).card : ℝ) ≤ (X.card : ℝ) := by exact_mod_cast hunion
    linarith only [h2, h3]
  have hdx : (1 / 2 + γ) * (X.card : ℝ) ≤ ((nbhdIn G x X).card : ℝ) := hx'
  have hdy : (1 / 2 + γ) * (X.card : ℝ) ≤ ((nbhdIn G y X).card : ℝ) := hy'
  nlinarith only [hkey, hdx, hdy]

/-! ### The greedy step -/

/-- **The greedy step.**  Given two vertices `x, y` of `S`, a part `X`, an already-used edge set
`F` of bounded size and maximum degree, and a small set `Av` of forbidden vertices, there is a
common `G`-neighbour `z ∈ X` of `x` and `y` outside `Av` such that neither `xz` nor `yz` is used
and `z` has small degree in `F`. -/
theorem exists_common_nbr {G : Finset (Sym2 V)} {S : Finset V} {P : Finset (Finset V)} {γ : ℝ}
    (hdeg : ∀ x ∈ S, ∀ W ∈ P, (1 / 2 + γ) * (W.card : ℝ) ≤ (degTo G x W : ℝ))
    {x y : V} (hx : x ∈ S) (hy : y ∈ S) {X : Finset V} (hX : X ∈ P)
    (F : Finset (Sym2 V)) {M Ecap D₀ : ℕ}
    (hM : ∀ v : V, edeg F v ≤ M) (hEcap : F.card ≤ Ecap)
    (Av : Finset V) (hAv : Av.card ≤ 6)
    (hnum : ((6 + 2 * M + 2 * Ecap / (D₀ + 1) : ℕ) : ℝ) < 2 * γ * (X.card : ℝ)) :
    ∃ z ∈ X, z ∉ Av ∧ s(x, z) ∈ G ∧ s(y, z) ∈ G ∧ s(x, z) ∉ F ∧ s(y, z) ∉ F ∧
      edeg F z ≤ D₀ := by
  classical
  set N := nbhdIn G x X ∩ nbhdIn G y X with hN
  set Bad := Av ∪ (nbhdIn F x X ∪ nbhdIn F y X) ∪ X.filter (fun z => ¬ edeg F z ≤ D₀) with hBad
  have hcard_bad : Bad.card ≤ 6 + 2 * M + 2 * Ecap / (D₀ + 1) := by
    have h1 : (nbhdIn F x X).card ≤ M := by
      refine le_trans ?_ (hM x)
      refine le_trans (Finset.card_le_card_of_injOn (fun z => s(x, z)) ?_ ?_) le_rfl
      · intro z hz
        exact Finset.mem_filter.2 ⟨(mem_nbhdIn.1 hz).2, by simp⟩
      · intro a _ b _ hab
        simp only [Sym2.eq_iff] at hab
        rcases hab with ⟨_, h⟩ | ⟨h1, h2⟩
        · exact h
        · exact h2.trans h1
    have h2 : (nbhdIn F y X).card ≤ M := by
      refine le_trans ?_ (hM y)
      refine le_trans (Finset.card_le_card_of_injOn (fun z => s(y, z)) ?_ ?_) le_rfl
      · intro z hz
        exact Finset.mem_filter.2 ⟨(mem_nbhdIn.1 hz).2, by simp⟩
      · intro a _ b _ hab
        simp only [Sym2.eq_iff] at hab
        rcases hab with ⟨_, h⟩ | ⟨h1, h2⟩
        · exact h
        · exact h2.trans h1
    have h3 : (X.filter (fun z => ¬ edeg F z ≤ D₀)).card ≤ 2 * Ecap / (D₀ + 1) := by
      refine le_trans (card_high_deg_le F X D₀) ?_
      exact Nat.div_le_div_right (by omega)
    have hu1 : Bad.card ≤ (Av ∪ (nbhdIn F x X ∪ nbhdIn F y X)).card
        + (X.filter (fun z => ¬ edeg F z ≤ D₀)).card := Finset.card_union_le _ _
    have hu2 : (Av ∪ (nbhdIn F x X ∪ nbhdIn F y X)).card
        ≤ Av.card + (nbhdIn F x X ∪ nbhdIn F y X).card := Finset.card_union_le _ _
    have hu3 : (nbhdIn F x X ∪ nbhdIn F y X).card
        ≤ (nbhdIn F x X).card + (nbhdIn F y X).card := Finset.card_union_le _ _
    omega
  have hNcard : ((6 + 2 * M + 2 * Ecap / (D₀ + 1) : ℕ) : ℝ) < (N.card : ℝ) :=
    lt_of_lt_of_le hnum (codeg_ge hdeg hx hy hX)
  have hlt : Bad.card < N.card := by
    have : ((Bad.card : ℕ) : ℝ) < (N.card : ℝ) :=
      lt_of_le_of_lt (by exact_mod_cast hcard_bad) hNcard
    exact_mod_cast this
  have hne : (N \ Bad).Nonempty := by
    rw [← Finset.card_pos]
    have := Finset.card_sdiff_add_card_inter N Bad
    have h2 : (N ∩ Bad).card ≤ Bad.card := Finset.card_le_card Finset.inter_subset_right
    omega
  obtain ⟨z, hz⟩ := hne
  rw [Finset.mem_sdiff] at hz
  obtain ⟨hzN, hzB⟩ := hz
  rw [hN, Finset.mem_inter, mem_nbhdIn, mem_nbhdIn] at hzN
  refine ⟨z, hzN.1.1, ?_, hzN.1.2, hzN.2.2, ?_, ?_, ?_⟩
  · exact fun hc => hzB (Finset.mem_union_left _ (Finset.mem_union_left _ hc))
  · exact fun hc => hzB (Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_union_left _ (mem_nbhdIn.2 ⟨hzN.1.1, hc⟩))))
  · exact fun hc => hzB (Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_union_right _ (mem_nbhdIn.2 ⟨hzN.1.1, hc⟩))))
  · by_contra hc
    exact hzB (Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hzN.1.1, hc⟩))

end BKLO
