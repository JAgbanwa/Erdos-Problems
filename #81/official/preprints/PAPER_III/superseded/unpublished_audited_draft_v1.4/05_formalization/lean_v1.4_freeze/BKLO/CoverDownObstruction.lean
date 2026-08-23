/-
# Two obstructions to the cover-down conclusion.

`BKLO/InputsVortex.lean` states the §10 cover-down input `CoverDownK3`.  This file isolates two
*necessary conditions* for the conclusion of that input, valid for arbitrary vertex sets:

* `cover_counting_obstruction` — a counting condition.  Every triangle has at most two edges
  crossing between `W'` and `W \ W'`, so the crossing edges (all of which have to be covered) are
  at most twice the number of edges inside `W \ W'` plus twice the number of edges inside `W'` that
  the family is allowed to consume.

* `cover_parity_obstruction` — a parity condition.  The edges consumed by an edge-disjoint triangle
  family form an even-degree edge set, so at a vertex `v` all of whose edges inside `W'` in fact lie
  inside `W''` — which the family must not touch — the number of edges of `F` at `v` inside `W''`
  has to be even.

Both are elementary; together they refute `CoverDownK3` (see `BKLO/CoverDownRefutation.lean`).

Everything here is `sorry`-free.
-/
import BKLO.InputsVortexSat

open Finset

namespace BKLO

variable {V : Type*} [DecidableEq V]

/-! ### An arithmetic helper -/

/-- `2·binom(k,2) = k(k-1)`, without truncated division. -/
theorem two_mul_choose_two (k : ℕ) : 2 * k.choose 2 = k * (k - 1) := by
  rw [Nat.choose_two_right]
  rcases k with _ | m
  · simp
  · simp only [Nat.add_sub_cancel]
    obtain ⟨c, hc⟩ : Even ((m + 1) * m) := by
      simpa [Nat.mul_comm] using Nat.even_mul_succ_self m
    rw [hc]
    omega

/-! ### Elementary facts about `edeg` -/

/-- `edeg` is additive along a disjoint union. -/
theorem edeg_union_of_disjoint {E₁ E₂ : Finset (Sym2 V)} (h : Disjoint E₁ E₂) (v : V) :
    edeg (E₁ ∪ E₂) v = edeg E₁ v + edeg E₂ v := by
  classical
  unfold edeg
  rw [Finset.filter_union, Finset.card_union_of_disjoint (Finset.disjoint_filter_filter h)]

theorem edeg_mono {E₁ E₂ : Finset (Sym2 V)} (h : E₁ ⊆ E₂) (v : V) : edeg E₁ v ≤ edeg E₂ v :=
  Finset.card_le_card (Finset.filter_subset_filter _ h)

theorem edeg_congr {E₁ E₂ : Finset (Sym2 V)} {v : V}
    (h : E₁.filter (fun e => v ∈ e) = E₂.filter (fun e => v ∈ e)) : edeg E₁ v = edeg E₂ v := by
  unfold edeg; rw [h]

/-- Splitting an edge set along a subset. -/
theorem edeg_sdiff_add {E C : Finset (Sym2 V)} (h : C ⊆ E) (v : V) :
    edeg C v + edeg (E \ C) v = edeg E v := by
  classical
  have hunion : C ∪ (E \ C) = E := by
    ext e; simp only [Finset.mem_union, Finset.mem_sdiff]
    exact ⟨fun h' => h'.elim (fun h'' => h h'') (fun h'' => h''.1), fun h' => by
      by_cases hc : e ∈ C
      · exact Or.inl hc
      · exact Or.inr ⟨h', hc⟩⟩
  have hdisj : Disjoint C (E \ C) := Finset.disjoint_sdiff
  rw [← edeg_union_of_disjoint hdisj v, hunion]

/-! ### Double counting -/

/-- Double counting incidences between a vertex set and an edge set. -/
theorem sum_edeg_eq_sum_card (S : Finset V) (E : Finset (Sym2 V)) :
    ∑ v ∈ S, edeg E v = ∑ e ∈ E, (S.filter (fun v => v ∈ e)).card := by
  classical
  unfold edeg
  simp only [Finset.card_filter]
  exact Finset.sum_comm

/-- An edge of the clique on `S` meets `S` in exactly two vertices. -/
theorem card_filter_mem_edge {S : Finset V} {e : Sym2 V} (he : e ∈ cliqueEdges S) :
    (S.filter (fun v => v ∈ e)).card = 2 := by
  classical
  obtain ⟨hmem, hnd⟩ := mem_cliqueEdgesV.1 he
  induction e using Sym2.ind with
  | _ x y =>
    have hxy : x ≠ y := by
      intro h; exact hnd (by simp [Sym2.isDiag_iff_proj_eq, h])
    have hfil : S.filter (fun v => v ∈ s(x, y)) = {x, y} := by
      ext v
      simp only [Finset.mem_filter, Sym2.mem_iff, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨-, h⟩; exact h
      · rintro (rfl | rfl)
        exacts [⟨hmem v (by simp), by simp⟩, ⟨hmem v (by simp), by simp⟩]
    rw [hfil, Finset.card_insert_of_notMem (by simpa using hxy), Finset.card_singleton]

/-- **Handshake.**  An edge set spanned by `S` has degree sum `2|E|` over `S`. -/
theorem sum_edeg_of_subset_cliqueEdges {S : Finset V} {E : Finset (Sym2 V)}
    (h : E ⊆ cliqueEdges S) : ∑ v ∈ S, edeg E v = 2 * E.card := by
  classical
  rw [sum_edeg_eq_sum_card]
  rw [Finset.sum_congr rfl (fun e he => card_filter_mem_edge (h he))]
  rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]

/-! ### Triangle families -/

theorem card_famEdges_eq {F : Finset (Sym2 V)} {P : Finset (Finset V)} (hP : TriFamilyIn F P) :
    (famEdges P).card = 3 * P.card := by
  classical
  unfold famEdges
  rw [Finset.card_biUnion (fun x hx y hy hxy => hP.2.2 x hx y hy hxy)]
  rw [Finset.sum_congr rfl (fun t ht => cliqueEdges_card_three (hP.1 t ht))]
  simp [Finset.sum_const, Nat.mul_comm]

theorem even_edeg_famEdges {F : Finset (Sym2 V)} {P : Finset (Finset V)} (hP : TriFamilyIn F P)
    (v : V) : Even (edeg (famEdges P) v) :=
  (hP.triDecomp.triDivisible).1 v

/-- A vertex of a triangle of a family inside `F ⊆ cliqueEdges W` lies in `W`. -/
theorem mem_of_mem_triangle {W : Finset V} {F : Finset (Sym2 V)} (hF : F ⊆ cliqueEdges W)
    {t : Finset V} (h3 : t.card = 3) (ht : cliqueEdges t ⊆ F) {x : V} (hx : x ∈ t) : x ∈ W := by
  classical
  obtain ⟨y, hy, hxy⟩ : ∃ y ∈ t, x ≠ y := by
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.1 h3
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact ⟨b, by simp, hab⟩
    · exact ⟨a, by simp, hab.symm⟩
    · exact ⟨a, by simp, hac.symm⟩
  have he : s(x, y) ∈ cliqueEdges t := by
    refine mem_cliqueEdgesV.2 ⟨?_, by simpa using hxy⟩
    intro z hz
    rcases Sym2.mem_iff.1 hz with rfl | rfl
    exacts [hx, hy]
  exact (mem_cliqueEdgesV.1 (hF (ht he))).1 x (by simp)

/-- **At most two crossing edges in a triangle.**  If the three vertices of `t` are split between
`W'` and `A`, then two of them are on the same side, so at most two of the three edges of `t` cross
between `W'` and `A`. -/
theorem card_triangle_cross_le_two {t W' A : Finset V} (h3 : t.card = 3)
    (hcov : ∀ x ∈ t, x ∈ W' ∨ x ∈ A) :
    (cliqueEdges t \ (cliqueEdges W' ∪ cliqueEdges A)).card ≤ 2 := by
  classical
  have hcard3 : (cliqueEdges t).card = 3 := cliqueEdges_card_three h3
  -- one edge inside `W'` or inside `A` is enough
  have H : ∀ u v : V, u ∈ t → v ∈ t → u ≠ v →
      ((u ∈ W' ∧ v ∈ W') ∨ (u ∈ A ∧ v ∈ A)) →
      (cliqueEdges t \ (cliqueEdges W' ∪ cliqueEdges A)).card ≤ 2 := by
    intro u v hu hv huv hside
    have het : s(u, v) ∈ cliqueEdges t := by
      refine mem_cliqueEdgesV.2 ⟨?_, by simpa using huv⟩
      intro z hz
      rcases Sym2.mem_iff.1 hz with rfl | rfl
      exacts [hu, hv]
    have hin : s(u, v) ∈ cliqueEdges W' ∪ cliqueEdges A := by
      rcases hside with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · refine Finset.mem_union_left _ (mem_cliqueEdgesV.2 ⟨?_, by simpa using huv⟩)
        intro z hz
        rcases Sym2.mem_iff.1 hz with rfl | rfl
        exacts [h1, h2]
      · refine Finset.mem_union_right _ (mem_cliqueEdgesV.2 ⟨?_, by simpa using huv⟩)
        intro z hz
        rcases Sym2.mem_iff.1 hz with rfl | rfl
        exacts [h1, h2]
    have hsub : cliqueEdges t \ (cliqueEdges W' ∪ cliqueEdges A)
        ⊆ (cliqueEdges t).erase s(u, v) := by
      intro e he
      obtain ⟨he1, he2⟩ := Finset.mem_sdiff.1 he
      exact Finset.mem_erase.2 ⟨fun h => he2 (h ▸ hin), he1⟩
    have := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem het, hcard3] at this
    exact this
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.1 h3
  have ha : a ∈ W' ∨ a ∈ A := hcov a (by simp)
  have hb : b ∈ W' ∨ b ∈ A := hcov b (by simp)
  have hc : c ∈ W' ∨ c ∈ A := hcov c (by simp)
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> rcases hc with hc | hc
  · exact H a b (by simp) (by simp) hab (Or.inl ⟨ha, hb⟩)
  · exact H a b (by simp) (by simp) hab (Or.inl ⟨ha, hb⟩)
  · exact H a c (by simp) (by simp) hac (Or.inl ⟨ha, hc⟩)
  · exact H b c (by simp) (by simp) hbc (Or.inr ⟨hb, hc⟩)
  · exact H b c (by simp) (by simp) hbc (Or.inl ⟨hb, hc⟩)
  · exact H a c (by simp) (by simp) hac (Or.inr ⟨ha, hc⟩)
  · exact H a b (by simp) (by simp) hab (Or.inr ⟨ha, hb⟩)
  · exact H a b (by simp) (by simp) hab (Or.inr ⟨ha, hb⟩)

/-- The crossing edges consumed by an edge-disjoint triangle family number at most `2|P|`. -/
theorem card_famEdges_cross_le {W W' A : Finset V} {F : Finset (Sym2 V)} {P : Finset (Finset V)}
    (hF : F ⊆ cliqueEdges W) (hP : TriFamilyIn F P) (hcov : ∀ x ∈ W, x ∈ W' ∨ x ∈ A) :
    (famEdges P \ (cliqueEdges W' ∪ cliqueEdges A)).card ≤ 2 * P.card := by
  classical
  have hsplit : famEdges P \ (cliqueEdges W' ∪ cliqueEdges A)
      = P.biUnion (fun t => cliqueEdges t \ (cliqueEdges W' ∪ cliqueEdges A)) := by
    ext e
    simp only [famEdges, Finset.mem_sdiff, Finset.mem_biUnion]
    tauto
  rw [hsplit]
  calc (P.biUnion (fun t => cliqueEdges t \ (cliqueEdges W' ∪ cliqueEdges A))).card
      ≤ ∑ t ∈ P, (cliqueEdges t \ (cliqueEdges W' ∪ cliqueEdges A)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _t ∈ P, 2 := by
        refine Finset.sum_le_sum ?_
        intro t ht
        exact card_triangle_cross_le_two (hP.1 t ht)
          (fun x hx => hcov x (mem_of_mem_triangle hF (hP.1 t ht) (hP.2.1 t ht) hx))
    _ = 2 * P.card := by rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]

/-! ### The conclusion of `CoverDownK3` at a fixed ratio and threshold -/

/-- The conclusion of `BKLO.CoverDownK3` for a fixed density `c`, damage tolerance `γ`, size ratio
`K` and size threshold `n₀`: this is the body of `CoverDownK3` after its two existential
witnesses have been supplied. -/
def CoverDownK3At (c γ : ℝ) (K n₀ : ℕ) : Prop :=
  ∀ {V : Type} [DecidableEq V] (W W' W'' : Finset V) (F : Finset (Sym2 V)),
    n₀ ≤ W.card → W' ⊆ W → W'' ⊆ W' →
    K * W'.card ≤ W.card → W.card ≤ K * K * W'.card → K * W''.card ≤ W'.card →
    F ⊆ cliqueEdges W → TriDivisible F → (∀ v ∈ W, c * (W.card : ℝ) ≤ (edeg F v : ℝ)) →
    ∃ P : Finset (Finset V), TriFamilyIn F P ∧
      F \ famEdges P ⊆ cliqueEdges W' ∧
      F ∩ cliqueEdges W'' ⊆ F \ famEdges P ∧
      ∀ v ∈ W', (edeg (F ∩ cliqueEdges W') v : ℝ)
        ≤ (edeg (F \ famEdges P) v : ℝ) + γ * (W'.card : ℝ)

/-- `CoverDownK3` is exactly the assertion that some ratio `K ≥ 2` and threshold `n₀` satisfy
`CoverDownK3At`. -/
theorem coverDownK3_iff :
    CoverDownK3 ↔ ∀ c γ : ℝ, 9 / 10 < c → 0 < γ → ∃ K n₀ : ℕ, 2 ≤ K ∧ CoverDownK3At c γ K n₀ :=
  Iff.rfl

/-! ### The two obstructions -/

/-- **The counting obstruction.**  In the situation of the conclusion of `CoverDownK3`, the edges of
`F` crossing between `W'` and `A = W \ W'` — all of which must be covered — are at most twice the
number of edges of `F` inside `A`, plus the total damage `γ|W'|²` allowed inside `W'`. -/
theorem cover_counting_obstruction {γ : ℝ} {W W' A : Finset V} {F : Finset (Sym2 V)}
    {P : Finset (Finset V)} (hF : F ⊆ cliqueEdges W) (hcov : ∀ x ∈ W, x ∈ W' ∨ x ∈ A)
    (hP : TriFamilyIn F P) (hleft : F \ famEdges P ⊆ cliqueEdges W')
    (hdam : ∀ v ∈ W', (edeg (F ∩ cliqueEdges W') v : ℝ)
      ≤ (edeg (F \ famEdges P) v : ℝ) + γ * (W'.card : ℝ)) :
    ((F \ (cliqueEdges W' ∪ cliqueEdges A)).card : ℝ)
      ≤ 2 * ((F ∩ cliqueEdges A).card : ℝ) + γ * (W'.card : ℝ) ^ 2 := by
  classical
  set C : Finset (Sym2 V) := famEdges P with hC
  have hCF : C ⊆ F := famEdges_subset_of_triFamilyIn hP
  set X : Finset (Sym2 V) := F \ (cliqueEdges W' ∪ cliqueEdges A) with hX
  set Y : Finset (Sym2 V) := C ∩ cliqueEdges W' with hY
  -- (1) every crossing edge is covered
  have hXC : X ⊆ C := by
    intro e he
    obtain ⟨heF, henot⟩ := Finset.mem_sdiff.1 he
    by_contra hc
    exact henot (Finset.mem_union_left _ (hleft (Finset.mem_sdiff.2 ⟨heF, hc⟩)))
  -- (2) at most two crossing edges per triangle
  have h2 : X.card ≤ 2 * P.card := by
    refine le_trans (Finset.card_le_card ?_) (card_famEdges_cross_le hF hP hcov)
    intro e he
    obtain ⟨-, henot⟩ := Finset.mem_sdiff.1 he
    exact Finset.mem_sdiff.2 ⟨hXC he, henot⟩
  -- (3) the covered set has `3|P|` edges
  have h3 : C.card = 3 * P.card := card_famEdges_eq hP
  -- (4) it is contained in the three parts
  have h4 : C.card ≤ X.card + (F ∩ cliqueEdges A).card + Y.card := by
    have hsub : C ⊆ X ∪ ((F ∩ cliqueEdges A) ∪ Y) := by
      intro e he
      by_cases h1 : e ∈ cliqueEdges W'
      · exact Finset.mem_union_right _ (Finset.mem_union_right _
          (Finset.mem_inter.2 ⟨he, h1⟩))
      · by_cases h2' : e ∈ cliqueEdges A
        · exact Finset.mem_union_right _ (Finset.mem_union_left _
            (Finset.mem_inter.2 ⟨hCF he, h2'⟩))
        · exact Finset.mem_union_left _ (Finset.mem_sdiff.2 ⟨hCF he, by
            simp only [Finset.mem_union]; tauto⟩)
    calc C.card ≤ (X ∪ ((F ∩ cliqueEdges A) ∪ Y)).card := Finset.card_le_card hsub
      _ ≤ X.card + ((F ∩ cliqueEdges A) ∪ Y).card := Finset.card_union_le _ _
      _ ≤ X.card + ((F ∩ cliqueEdges A).card + Y.card) :=
          Nat.add_le_add_left (Finset.card_union_le _ _) _
      _ = X.card + (F ∩ cliqueEdges A).card + Y.card := by omega
  -- (5) the damage bound, vertex by vertex
  have hdeg : ∀ v ∈ W', (edeg Y v : ℝ) ≤ γ * (W'.card : ℝ) := by
    intro v hv
    have hsplit : edeg (F \ C) v + edeg Y v = edeg (F ∩ cliqueEdges W') v := by
      have hunion : (F \ C) ∪ Y = F ∩ cliqueEdges W' := by
        ext e
        simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter, hY]
        constructor
        · rintro (⟨heF, henC⟩ | ⟨heC, hew⟩)
          · exact ⟨heF, hleft (Finset.mem_sdiff.2 ⟨heF, henC⟩)⟩
          · exact ⟨hCF heC, hew⟩
        · rintro ⟨heF, hew⟩
          by_cases hc : e ∈ C
          · exact Or.inr ⟨hc, hew⟩
          · exact Or.inl ⟨heF, hc⟩
      have hdisj : Disjoint (F \ C) Y := by
        refine Finset.disjoint_left.2 fun e he he' => ?_
        exact (Finset.mem_sdiff.1 he).2 (Finset.mem_inter.1 he').1
      rw [← hunion, edeg_union_of_disjoint hdisj]
    have := hdam v hv
    have hcast : (edeg (F \ C) v : ℝ) + (edeg Y v : ℝ) = (edeg (F ∩ cliqueEdges W') v : ℝ) := by
      exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) hsplit
    linarith only [this, hcast]
  -- (6) sum the damage bound over `W'`
  have hYsum : (2 * Y.card : ℝ) ≤ γ * (W'.card : ℝ) ^ 2 := by
    have hYsub : Y ⊆ cliqueEdges W' := Finset.inter_subset_right
    have hsum : ∑ v ∈ W', edeg Y v = 2 * Y.card := sum_edeg_of_subset_cliqueEdges hYsub
    have hle : ((∑ v ∈ W', edeg Y v : ℕ) : ℝ) ≤ ∑ _v ∈ W', γ * (W'.card : ℝ) := by
      push_cast
      exact Finset.sum_le_sum hdeg
    rw [Finset.sum_const, nsmul_eq_mul] at hle
    rw [hsum] at hle
    calc (2 * Y.card : ℝ) = ((2 * Y.card : ℕ) : ℝ) := by push_cast; ring
      _ ≤ (W'.card : ℝ) * (γ * (W'.card : ℝ)) := hle
      _ = γ * (W'.card : ℝ) ^ 2 := by ring
  -- (7) combine
  have hnat : X.card ≤ 2 * (F ∩ cliqueEdges A).card + 2 * Y.card := by omega
  have : ((X.card : ℝ)) ≤ 2 * ((F ∩ cliqueEdges A).card : ℝ) + (2 * Y.card : ℝ) := by
    exact_mod_cast hnat
  linarith only [hYsum, this]

/-- **The parity obstruction.**  In the situation of the conclusion of `CoverDownK3`, if every edge
of `F` at `v₀` that lies inside `W'` in fact lies inside `W''` — which the family may not touch —
then the number of edges of `F` at `v₀` inside `W''` has the same parity as `edeg F v₀`. -/
theorem cover_parity_obstruction {W' W'' : Finset V} {F : Finset (Sym2 V)}
    {P : Finset (Finset V)} {v₀ : V} (hP : TriFamilyIn F P)
    (hleft : F \ famEdges P ⊆ cliqueEdges W')
    (huntouched : F ∩ cliqueEdges W'' ⊆ F \ famEdges P)
    (hlink : ∀ e ∈ F, v₀ ∈ e → e ∈ cliqueEdges W' → e ∈ cliqueEdges W'')
    (heven : Even (edeg F v₀)) : Even (edeg (F ∩ cliqueEdges W'') v₀) := by
  classical
  set C : Finset (Sym2 V) := famEdges P with hC
  have hCF : C ⊆ F := famEdges_subset_of_triFamilyIn hP
  have hfil : (F \ C).filter (fun e => v₀ ∈ e)
      = (F ∩ cliqueEdges W'').filter (fun e => v₀ ∈ e) := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_inter]
    constructor
    · rintro ⟨⟨heF, henC⟩, hv⟩
      exact ⟨⟨heF, hlink e heF hv (hleft (Finset.mem_sdiff.2 ⟨heF, henC⟩))⟩, hv⟩
    · rintro ⟨⟨heF, hew⟩, hv⟩
      exact ⟨Finset.mem_sdiff.1 (huntouched (Finset.mem_inter.2 ⟨heF, hew⟩)), hv⟩
  have hEq : edeg (F \ C) v₀ = edeg (F ∩ cliqueEdges W'') v₀ := edeg_congr hfil
  have hsum : edeg C v₀ + edeg (F \ C) v₀ = edeg F v₀ := edeg_sdiff_add hCF v₀
  have hCeven : Even (edeg C v₀) := even_edeg_famEdges hP v₀
  rw [hEq] at hsum
  obtain ⟨a, ha⟩ := hCeven
  obtain ⟨b, hb⟩ := heven
  exact ⟨b - a, by omega⟩

end BKLO
