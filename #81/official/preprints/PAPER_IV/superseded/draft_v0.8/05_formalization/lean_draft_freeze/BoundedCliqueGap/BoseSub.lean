import BoundedCliqueGap.Bose
import BoundedCliqueGap.GVizing

/-
`BoundedCliqueGap.BoseSub` — declaration-level extract of the Route B
triangle-packing development.  Only the declarations in the constant cone of
`BoundedCliqueGap.chordal_gap_linear_cliqueFree` were kept (plus the few that
the retained sources need in order to elaborate); the module documentation
below is the original one and may advertise results that were pruned away.
-/

/-
# The regular Bose sub-family and its Cayley port graph

Fix the Bose Steiner triple system on `K = R × Fin 3` (`R` a finite commutative
ring with a half `ih` of `1`; `R = ZMod n`, `n` odd, gives `K_{3n}`).

For a set `D` of "differences" with `0 ∉ D` and `d + d' ≠ 0` for all
`d, d' ∈ D`, consider the sub-family

  `sub = { BT ih i x (x+d) : i : Fin 3, x : R, d ∈ D }`

of Bose blocks.  Its edge set is exactly the Cayley graph on the abelian group
`R × Fin 3` with connection set

  `conn = { (±d, 0), (±d·ih, 1), (±d·ih, 2) : d ∈ D }`,

a **`6|D|`-regular** graph.  That regularity is the whole point: by Vizing the
port graph is properly edge-colourable with `6|D| + 1` colours, so `s = 6|D|`
independent vertices can absorb all but one colour class of it, while the Bose
blocks *outside* `sub` still pack the rest of the clique perfectly.  This is
the mechanism that removes the divisibility constraints of rung C3.
-/

namespace BoundedCliqueGap

namespace BoseSub

open Finset

variable {R : Type*} [CommRing R] [Fintype R] [DecidableEq R] {ih : R} {D : Finset R}

/-! ## The connection set -/

/-- The six connection vectors attached to one difference `d`. -/
def blockOf (ih : R) (d : R) : Finset (R × Fin 3) :=
  {(d, 0), (-d, 0), (d * ih, 1), (-(d * ih), 1), (d * ih, 2), (-(d * ih), 2)}

/-- The connection set of the port graph. -/
def conn (ih : R) (D : Finset R) : Finset (R × Fin 3) := D.biUnion (blockOf ih)

omit [Fintype R] in
lemma mem_blockOf {d : R} {p : R × Fin 3} :
    p ∈ blockOf ih d ↔
      (p.2 = 0 ∧ (p.1 = d ∨ p.1 = -d)) ∨ (p.2 ≠ 0 ∧ (p.1 = d * ih ∨ p.1 = -(d * ih))) := by
  obtain ⟨a, l⟩ := p
  simp only [blockOf, Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]
  constructor
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact Or.inl ⟨rfl, Or.inl rfl⟩
    · exact Or.inl ⟨rfl, Or.inr rfl⟩
    · exact Or.inr ⟨by decide, Or.inl rfl⟩
    · exact Or.inr ⟨by decide, Or.inr rfl⟩
    · exact Or.inr ⟨by decide, Or.inl rfl⟩
    · exact Or.inr ⟨by decide, Or.inr rfl⟩
  · rintro (⟨rfl, rfl | rfl⟩ | ⟨hl, rfl | rfl⟩)
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · revert hl; fin_cases l <;> simp
    · revert hl; fin_cases l <;> simp

omit [Fintype R] in
lemma mem_conn {p : R × Fin 3} : p ∈ conn ih D ↔ ∃ d ∈ D, p ∈ blockOf ih d := by
  simp [conn]

omit [Fintype R] in
lemma neg_mem_conn {p : R × Fin 3} (hp : p ∈ conn ih D) : -p ∈ conn ih D := by
  rw [mem_conn] at hp ⊢
  obtain ⟨d, hd, h⟩ := hp
  refine ⟨d, hd, ?_⟩
  rw [mem_blockOf] at h ⊢
  have hfst : (-p).1 = -p.1 := rfl
  have hsnd : (-p).2 = -p.2 := rfl
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine Or.inl ⟨by rw [hsnd, h1]; decide, ?_⟩
    rcases h2 with h2 | h2
    · exact Or.inr (by rw [hfst, h2])
    · exact Or.inl (by rw [hfst, h2]; ring)
  · refine Or.inr ⟨?_, ?_⟩
    · rw [hsnd]
      revert h1
      generalize p.2 = l
      fin_cases l <;> simp
    · rcases h2 with h2 | h2
      · exact Or.inr (by rw [hfst, h2])
      · exact Or.inl (by rw [hfst, h2]; ring)

/-! ## Arithmetic of halves -/

omit [Fintype R] [DecidableEq R] in
lemma two_mul_half (hih : (2 : R) * ih = 1) (d : R) : 2 * (d * ih) = d := by
  calc 2 * (d * ih) = d * (2 * ih) := by ring
    _ = d := by rw [hih, mul_one]

omit [Fintype R] [DecidableEq R] in
lemma half_inj (hih : (2 : R) * ih = 1) {d d' : R} (h : d * ih = d' * ih) : d = d' := by
  have h2 := congrArg (fun z => 2 * z) h
  simp only at h2
  rwa [two_mul_half hih, two_mul_half hih] at h2

omit [Fintype R] [DecidableEq R] in
lemma half_neg_inj (hih : (2 : R) * ih = 1) {d d' : R} (h : d * ih = -(d' * ih)) : d = -d' := by
  have h2 := congrArg (fun z => 2 * z) h
  simp only at h2
  rw [two_mul_half hih, show (2 : R) * -(d' * ih) = -(2 * (d' * ih)) by ring,
    two_mul_half hih] at h2
  exact h2

omit [Fintype R] [DecidableEq R] in
lemma half_ne_zero (hih : (2 : R) * ih = 1) {d : R} (hd : d ≠ 0) : d * ih ≠ 0 := by
  intro h
  apply hd
  rw [← two_mul_half hih d, h, mul_zero]

/-! ## The size of the connection set -/

omit [Fintype R] [DecidableEq R] in
lemma self_ne_neg (hDsum : ∀ d ∈ D, ∀ d' ∈ D, d + d' ≠ 0) {d : R} (hd : d ∈ D) : d ≠ -d := fun h =>
  hDsum d hd d hd (by linear_combination h)

omit [Fintype R] [DecidableEq R] in
lemma ne_zero_of_mem (hD0 : (0 : R) ∉ D) {d : R} (hd : d ∈ D) : d ≠ 0 := fun h => hD0 (h ▸ hd)

omit [Fintype R] in
lemma zero_notMem_conn (hD0 : (0 : R) ∉ D) : (0 : R × Fin 3) ∉ conn ih D := by
  intro h
  rw [mem_conn] at h
  obtain ⟨d, hd, h⟩ := h
  have hdne : d ≠ 0 := ne_zero_of_mem hD0 hd
  rw [mem_blockOf] at h
  rcases h with ⟨-, h2⟩ | ⟨h1, -⟩
  · rcases h2 with h2 | h2
    · exact hdne h2.symm
    · exact hdne (by simpa using (neg_eq_zero.1 h2.symm))
  · exact h1 rfl

omit [Fintype R] in
lemma card_conn (hih : (2 : R) * ih = 1) (hDsum : ∀ d ∈ D, ∀ d' ∈ D, d + d' ≠ 0) : (conn ih D).card = 6 * D.card := by
  classical
  rw [conn, Finset.card_biUnion]
  · have h6 : ∀ d ∈ D, (blockOf ih d).card = 6 := by
      intro d hd
      have hdd : d ≠ -d := self_ne_neg hDsum hd
      have hhh : d * ih ≠ -(d * ih) := fun h => hdd (half_neg_inj hih h)
      rw [blockOf, Finset.card_insert_of_notMem (by simp [Prod.ext_iff, hdd]),
        Finset.card_insert_of_notMem (by simp [Prod.ext_iff]),
        Finset.card_insert_of_notMem (by simp [Prod.ext_iff, hhh]),
        Finset.card_insert_of_notMem (by simp [Prod.ext_iff]),
        Finset.card_insert_of_notMem (by simp [Prod.ext_iff, hhh]),
        Finset.card_singleton]
    rw [Finset.sum_congr rfl h6, Finset.sum_const, smul_eq_mul, Nat.mul_comm]
  · intro d hd d' hd' hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro p hp hp'
    have hdd' : d ≠ -d' := fun h => hDsum d hd d' hd' (by linear_combination h)
    rw [mem_blockOf] at hp hp'
    rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hp' with ⟨g1, g2⟩ | ⟨g1, g2⟩
    · rcases h2 with h2 | h2 <;> rcases g2 with g2 | g2
      · exact hne (h2.symm.trans g2)
      · exact hdd' (h2.symm.trans g2)
      · exact hdd' (by rw [← h2.symm.trans g2]; ring)
      · exact hne (neg_injective (h2.symm.trans g2))
    · exact g1 h1
    · exact h1 g1
    · rcases h2 with h2 | h2 <;> rcases g2 with g2 | g2
      · exact hne (half_inj hih (h2.symm.trans g2))
      · exact hdd' (half_neg_inj hih (h2.symm.trans g2))
      · have hk : d' * ih = -(d * ih) := (g2.symm.trans h2)
        exact hdd' (by rw [half_neg_inj hih hk]; ring)
      · exact hne (half_inj hih (neg_injective (h2.symm.trans g2)))

omit [Fintype R] in
lemma mem_blockOf' {d : R} {p : R × Fin 3} :
    p ∈ blockOf ih d ↔ p = (d, 0) ∨ p = (-d, 0) ∨ p = (d * ih, 1) ∨
      p = (-(d * ih), 1) ∨ p = (d * ih, 2) ∨ p = (-(d * ih), 2) := by
  simp [blockOf]

lemma fin3_shift (i : Fin 3) : i = i + 2 + 1 := by revert i; decide

/-! ## The port graph -/

/-- The **port graph**: the Cayley graph on `R × Fin 3` with connection set
`conn ih D`.  Its edges are exactly the edges of the Bose blocks in `sub`. -/
def portGraph (ih : R) (D : Finset R) : SimpleGraph (R × Fin 3) where
  Adj u v := u ≠ v ∧ (v - u) ∈ conn ih D
  symm := by
    rintro u v ⟨h1, h2⟩
    refine ⟨h1.symm, ?_⟩
    have := neg_mem_conn h2
    rwa [neg_sub] at this
  loopless := ⟨fun _ h => h.1 rfl⟩

instance instDecidablePortGraph : DecidableRel (portGraph ih D).Adj :=
  fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

omit [Fintype R] in
lemma portGraph_adj {u v : R × Fin 3} :
    (portGraph ih D).Adj u v ↔ u ≠ v ∧ (v - u) ∈ conn ih D := Iff.rfl

lemma portGraph_degree (hih : (2 : R) * ih = 1) (hD0 : (0 : R) ∉ D)
    (hDsum : ∀ d ∈ D, ∀ d' ∈ D, d + d' ≠ 0) (v : R × Fin 3) :
    (portGraph ih D).degree v = 6 * D.card := by
  classical
  have h0 : (0 : R × Fin 3) ∉ conn ih D := zero_notMem_conn hD0
  have hnb : (portGraph ih D).neighborFinset v = (conn ih D).image (fun w => v + w) := by
    ext w
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_image, portGraph_adj]
    constructor
    · rintro ⟨-, hw⟩
      refine ⟨w - v, hw, ?_⟩
      show v + (w - v) = w
      abel
    · rintro ⟨p, hp, rfl⟩
      refine ⟨?_, by simpa using hp⟩
      intro hcon
      apply h0
      have hp0 : p = 0 := by simpa using hcon.symm
      rwa [hp0] at hp
  rw [SimpleGraph.degree, hnb,
    Finset.card_image_of_injective _ (add_right_injective v), card_conn hih hDsum]

lemma portGraph_maxDegree_le (hih : (2 : R) * ih = 1) (hD0 : (0 : R) ∉ D)
    (hDsum : ∀ d ∈ D, ∀ d' ∈ D, d + d' ≠ 0) : (portGraph ih D).maxDegree ≤ 6 * D.card :=
  SimpleGraph.maxDegree_le_of_forall_degree_le _ _
    (fun v => le_of_eq (portGraph_degree hih hD0 hDsum v))

lemma card_edgeFinset_portGraph (hih : (2 : R) * ih = 1) (hD0 : (0 : R) ∉ D)
    (hDsum : ∀ d ∈ D, ∀ d' ∈ D, d + d' ≠ 0) :
    2 * (portGraph ih D).edgeFinset.card = Fintype.card R * (18 * D.card) := by
  classical
  have h := (portGraph ih D).sum_degrees_eq_twice_card_edges
  rw [Finset.sum_congr rfl (fun v _ => portGraph_degree hih hD0 hDsum v),
    Finset.sum_const, smul_eq_mul, Finset.card_univ] at h
  rw [← h, Fintype.card_prod, Fintype.card_fin]
  ring

/-! ## The sub-family of Bose blocks -/

/-- The regular sub-family of Bose blocks selected by the difference set `D`. -/
noncomputable def sub (ih : R) (D : Finset R) : Finset (Finset (R × Fin 3)) := by
  classical
  exact ((Finset.univ : Finset (Fin 3)) ×ˢ (Finset.univ : Finset R) ×ˢ D).image
    fun p : Fin 3 × R × R => Bose.BT ih p.1 p.2.1 (p.2.1 + p.2.2)

lemma mem_sub {T : Finset (R × Fin 3)} :
    T ∈ sub ih D ↔ ∃ (i : Fin 3) (x d : R), d ∈ D ∧ T = Bose.BT ih i x (x + d) := by
  classical
  simp only [sub, Finset.mem_image, Finset.mem_product, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨i, x, d⟩, hd, rfl⟩
    exact ⟨i, x, d, hd, rfl⟩
  · rintro ⟨i, x, d, hd, rfl⟩
    exact ⟨⟨i, x, d⟩, hd, rfl⟩

lemma card_sub_le : (sub ih D).card ≤ 3 * (Fintype.card R * D.card) := by
  classical
  refine le_trans (Finset.card_image_le) ?_
  rw [Finset.card_product, Finset.card_product, Finset.card_univ, Finset.card_univ,
    Fintype.card_fin]

lemma sub_subset_family (hD0 : (0 : R) ∉ D) : sub ih D ⊆ Bose.family ih := by
  intro T hT
  obtain ⟨i, x, d, hd, rfl⟩ := mem_sub.1 hT
  refine Bose.BT_mem_family ?_
  intro h
  exact ne_zero_of_mem hD0 hd (by linear_combination -h)

/-- Every edge of the port graph is an edge of one of the selected Bose blocks. -/
lemma blk_mem_sub_of_adj (hih : (2 : R) * ih = 1) (hD0 : (0 : R) ∉ D) {u v : R × Fin 3} (hadj : (portGraph ih D).Adj u v) :
    Bose.blk ih u v ∈ sub ih D := by
  obtain ⟨x, i⟩ := u
  obtain ⟨y, j⟩ := v
  obtain ⟨hne, hmem⟩ := hadj
  rw [mem_conn] at hmem
  obtain ⟨d, hd, hp⟩ := hmem
  have hdne : d ≠ 0 := ne_zero_of_mem hD0 hd
  have hhne : d * ih ≠ 0 := half_ne_zero hih hdne
  have hstep : ∀ c : R, c ≠ 0 → x ≠ x + c := by
    intro c hc hcon
    exact hc (by linear_combination -hcon)
  have hstep' : ∀ c : R, c ≠ 0 → x ≠ x - c := by
    intro c hc hcon
    exact hc (by linear_combination hcon)
  rw [mem_blockOf'] at hp
  simp only [Prod.mk_sub_mk, Prod.mk.injEq] at hp
  have hlayer : ∀ t : Fin 3, j - i = t → j = i + t := by
    intro t ht
    rw [← ht]
    abel
  have hval : ∀ c : R, y - x = c → y = x + c := by
    intro c hc
    linear_combination hc
  rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · -- same layer, difference `d`
    have hy : y = x + d := hval _ h1
    have hj : j = i := by have := hlayer _ h2; simpa using this
    subst hy
    rw [hj, Bose.blk_same_layer]
    exact mem_sub.2 ⟨i, x, d, hd, rfl⟩
  · -- same layer, difference `-d`
    have hy : y = x + -d := hval _ h1
    have hj : j = i := by have := hlayer _ h2; simpa using this
    subst hy
    rw [hj, Bose.blk_same_layer, Bose.BT_comm]
    refine mem_sub.2 ⟨i, x + -d, d, hd, ?_⟩
    congr 1
    ring
  · -- up a layer, `+d·ih`
    have hy : y = x + d * ih := hval _ h1
    have hj : j = i + 1 := hlayer _ h2
    subst hy; subst hj
    rw [Bose.blk_up rfl (hstep _ hhne)]
    refine mem_sub.2 ⟨i, x, d, hd, ?_⟩
    congr 1
    have := two_mul_half hih d
    linear_combination this
  · -- up a layer, `-d·ih`
    have hy : y = x + -(d * ih) := hval _ h1
    have hj : j = i + 1 := hlayer _ h2
    subst hy; subst hj
    rw [Bose.blk_up rfl (by simpa [sub_eq_add_neg] using hstep' _ hhne)]
    rw [Bose.BT_comm]
    refine mem_sub.2 ⟨i, 2 * (x + -(d * ih)) - x, d, hd, ?_⟩
    congr 1
    have := two_mul_half hih d
    linear_combination this
  · -- down a layer, `+d·ih`
    have hy : y = x + d * ih := hval _ h1
    have hj : j = i + 2 := hlayer _ h2
    subst hy; subst hj
    rw [Bose.blk_down (fin3_shift i) (hstep _ hhne), Bose.BT_comm]
    refine mem_sub.2 ⟨i + 2, 2 * x - (x + d * ih), d, hd, ?_⟩
    congr 1
    have := two_mul_half hih d
    linear_combination this
  · -- down a layer, `-d·ih`
    have hy : y = x + -(d * ih) := hval _ h1
    have hj : j = i + 2 := hlayer _ h2
    subst hy; subst hj
    rw [Bose.blk_down (fin3_shift i) (by simpa [sub_eq_add_neg] using hstep' _ hhne)]
    refine mem_sub.2 ⟨i + 2, x + -(d * ih), d, hd, ?_⟩
    congr 1
    have := two_mul_half hih d
    linear_combination this

end BoseSub

end BoundedCliqueGap
