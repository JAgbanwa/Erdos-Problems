import A4S1.PerVertexAbsorption

/-!
# E14, step 1: absorption matchings for the exceptional vertices (link-usage selection)

For every exceptional vertex `w` we reserve a family `M w` of links `a h` (`a` in the core `S`,
`h` in the rows `H`, `a h` an edge, both adjacent to `w`), a matching on both sides, with the
families of different `w` pairwise disjoint.  The triangles `{w, a, h}` will absorb two edges at
`w` each.

The size of `M w` comes from **our** tools, not from a rectangle lemma:

* `A4S1.PerVertex.exists_balanced_selection` chooses the core vertices `S' ⊆ N_S(w)` that
  receive a host, with cost `e_a = |N_H(w) ∖ N(a)|` and supply `|N_H(w)| − |W|` (the `|W|` pays
  the links already reserved at `a` by the other exceptional vertices, at most one each);
* `A4S1.HostAbsorption.exists_injOn_choice` gives the distinct hosts greedily.

The selection either takes all of `N_S(w)` or satisfies
`(u − |S'|)(v − |W| − |S'|) ≤ Σ e_a ≤ D`, whence
`min(u, v) ≤ |M w| + |W| + ⌊√D⌋` (`min_le_of_selection`).
-/

namespace A4S1.Indep

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The arithmetic of the selection: if `x = u` or `(u − x)(v − W − x) ≤ D` (in `ℤ`), then
`min(u, v) ≤ x + W + ⌊√D⌋`. -/
theorem min_le_of_selection (u v x W D : ℕ)
    (h : x = u ∨ ((u : ℤ) - x) * (((v : ℤ) - W) - x) ≤ D) :
    min u v ≤ x + W + Nat.sqrt D := by
  rcases h with rfl | h
  · have := min_le_left x v
    omega
  · by_contra hc
    push_neg at hc
    have hr := Nat.lt_succ_sqrt D
    set r := Nat.sqrt D
    have hmu := min_le_left u v
    have hmv := min_le_right u v
    have h1 : (r : ℤ) + 1 ≤ (u : ℤ) - x := by omega
    have h2 : (r : ℤ) + 1 ≤ ((v : ℤ) - W) - x := by omega
    have h3 : ((r : ℤ) + 1) * ((r : ℤ) + 1) ≤ ((u : ℤ) - x) * (((v : ℤ) - W) - x) :=
      mul_le_mul h1 h2 (by positivity) (by omega)
    have hr' : (D : ℤ) < ((r : ℤ) + 1) * ((r : ℤ) + 1) := by exact_mod_cast hr
    linarith

omit [Fintype V] [DecidableEq V] in
/-- Missing pairs of a rectangle, counted row by row. -/
theorem card_filter_not_adj_product (X Y : Finset V) :
    ((X ×ˢ Y).filter fun p => ¬ G.Adj p.1 p.2).card =
      ∑ a ∈ X, (Y.filter fun h => ¬ G.Adj a h).card := by
  rw [card_filter, sum_product]
  refine sum_congr rfl fun a _ => ?_
  rw [card_filter]

omit [Fintype V] in
/-- A family of matchings indexed by `W` has at most `|W|` pairs with a given first coordinate. -/
theorem card_filter_fst_biUnion_le (W : Finset V) (M : V → Finset (V × V))
    (hinj : ∀ w ∈ W, ∀ p ∈ M w, ∀ p' ∈ M w, (p.1 = p'.1 ∨ p.2 = p'.2) → p = p') (z : V) :
    ((W.biUnion M).filter fun p => p.1 = z).card ≤ W.card ∧
      ((W.biUnion M).filter fun p => p.2 = z).card ≤ W.card := by
  constructor
  · rw [filter_biUnion]
    refine (card_biUnion_le).trans ?_
    have : ∀ w ∈ W, ((M w).filter fun p => p.1 = z).card ≤ 1 := by
      intro w hw
      rw [card_le_one]
      intro p hp p' hp'
      rw [mem_filter] at hp hp'
      exact hinj w hw p hp.1 p' hp'.1 (Or.inl (hp.2.trans hp'.2.symm))
    calc ∑ w ∈ W, ((M w).filter fun p => p.1 = z).card ≤ ∑ _w ∈ W, 1 := sum_le_sum this
      _ = W.card := by simp
  · rw [filter_biUnion]
    refine (card_biUnion_le).trans ?_
    have : ∀ w ∈ W, ((M w).filter fun p => p.2 = z).card ≤ 1 := by
      intro w hw
      rw [card_le_one]
      intro p hp p' hp'
      rw [mem_filter] at hp hp'
      exact hinj w hw p hp.1 p' hp'.1 (Or.inr (hp.2.trans hp'.2.symm))
    calc ∑ w ∈ W, ((M w).filter fun p => p.2 = z).card ≤ ∑ _w ∈ W, 1 := sum_le_sum this
      _ = W.card := by simp

omit [Fintype V] in
/-- **Absorption matchings** by balanced selection and greedy distinct hosts. -/
theorem exists_absorption_matchings (S H : Finset V) (D : ℕ)
    (hD : ∀ X ⊆ S, ∀ Y ⊆ H, ((X ×ˢ Y).filter fun p => ¬ G.Adj p.1 p.2).card ≤ D) :
    ∀ W : Finset V, ∃ M : V → Finset (V × V),
      (∀ w ∈ W, ∀ p ∈ M w, p.1 ∈ S ∧ p.2 ∈ H ∧ G.Adj w p.1 ∧ G.Adj w p.2 ∧ G.Adj p.1 p.2) ∧
      (∀ w ∈ W, ∀ p ∈ M w, ∀ p' ∈ M w, (p.1 = p'.1 ∨ p.2 = p'.2) → p = p') ∧
      (∀ w ∈ W, ∀ w' ∈ W, w ≠ w' → Disjoint (M w) (M w')) ∧
      (∀ w ∈ W, min (S.filter (G.Adj w)).card (H.filter (G.Adj w)).card ≤
        (M w).card + W.card + Nat.sqrt D) := by
  intro W
  induction W using Finset.induction_on with
  | empty => exact ⟨fun _ => ∅, by simp, by simp, by simp, by simp⟩
  | @insert w W₀ hw ih =>
    obtain ⟨M₀, hM1, hM2, hM3, hM4⟩ := ih
    haveI : Nonempty V := ⟨w⟩
    set Used := W₀.biUnion M₀ with hUsed
    set P := S.filter (G.Adj w) with hP
    set Y := H.filter (G.Adj w) with hY
    set e : V → ℕ := fun a => (Y.filter fun h => ¬ G.Adj a h).card with he
    obtain ⟨S', hS'P, hS'e, halt⟩ :=
      A4S1.PerVertex.exists_balanced_selection P e ((Y.card : ℤ) - W₀.card)
    set Lst : V → Finset V := fun a => Y.filter fun h => G.Adj a h ∧ (a, h) ∉ Used with hLst
    have hLcard : ∀ a ∈ S', S'.card ≤ (Lst a).card := by
      intro a ha
      have h1 : S'.card + (Y.filter fun h => ¬ G.Adj a h).card + W₀.card ≤ Y.card := by
        have := hS'e a ha
        simp only [he] at this
        omega
      have hsplit := card_filter_add_card_filter_not (s := Y) (p := fun h => G.Adj a h)
      have hsub : Y.filter (fun h => G.Adj a h) ⊆
          Lst a ∪ ((Used.filter fun p => p.1 = a).image Prod.snd) := by
        intro h hh
        rw [mem_filter] at hh
        by_cases hu : (a, h) ∈ Used
        · exact mem_union_right _ (mem_image.2 ⟨(a, h), mem_filter.2 ⟨hu, rfl⟩, rfl⟩)
        · exact mem_union_left _ (mem_filter.2 ⟨hh.1, hh.2, hu⟩)
      have h2 := card_le_card hsub
      have h3 := card_union_le (Lst a) ((Used.filter fun p => p.1 = a).image Prod.snd)
      have h4 := card_image_le (s := Used.filter fun p => p.1 = a) (f := Prod.snd)
      have h5 : (Used.filter fun p => p.1 = a).card ≤ W₀.card :=
        (card_filter_fst_biUnion_le W₀ M₀ hM2 a).1
      omega
    obtain ⟨f, hfL, hfinj⟩ := A4S1.HostAbsorption.exists_injOn_choice S' Lst hLcard
    set Mnew := S'.image fun a => (a, f a) with hMnew
    have hMnew_mem : ∀ p ∈ Mnew, p.1 ∈ S' ∧ p.2 = f p.1 := by
      intro p hp
      obtain ⟨a, ha, rfl⟩ := mem_image.1 hp
      exact ⟨ha, rfl⟩
    have hMnew_card : Mnew.card = S'.card := by
      rw [hMnew, card_image_of_injective]
      intro a b hab
      exact (Prod.mk.inj hab).1
    have hfprop : ∀ a ∈ S', a ∈ S ∧ G.Adj w a ∧ f a ∈ H ∧ G.Adj w (f a) ∧ G.Adj a (f a) ∧
        (a, f a) ∉ Used := by
      intro a ha
      have haP := hS'P ha
      rw [hP, mem_filter] at haP
      have hfa := hfL a ha
      rw [hLst, mem_filter, hY, mem_filter] at hfa
      exact ⟨haP.1, haP.2, hfa.1.1, hfa.1.2, hfa.2.1, hfa.2.2⟩
    refine ⟨fun x => if x = w then Mnew else M₀ x, ?_, ?_, ?_, ?_⟩
    · intro x hx p hp
      by_cases hxw : x = w
      · subst hxw
        simp only [if_true] at hp
        obtain ⟨h1, h2⟩ := hMnew_mem p hp
        obtain ⟨a1, a2, a3, a4, a5, -⟩ := hfprop p.1 h1
        rw [h2]
        exact ⟨a1, a3, a2, a4, a5⟩
      · simp only [hxw, if_false] at hp
        exact hM1 x ((mem_insert.1 hx).resolve_left hxw) p hp
    · intro x hx p hp p' hp' hpp
      by_cases hxw : x = w
      · subst hxw
        simp only [if_true] at hp hp'
        obtain ⟨h1, h2⟩ := hMnew_mem p hp
        obtain ⟨h1', h2'⟩ := hMnew_mem p' hp'
        have h11 : p.1 = p'.1 := by
          rcases hpp with h | h
          · exact h
          · rw [h2, h2'] at h
            exact hfinj h1 h1' h
        exact Prod.ext h11 (by rw [h2, h2', h11])
      · simp only [hxw, if_false] at hp hp'
        exact hM2 x ((mem_insert.1 hx).resolve_left hxw) p hp p' hp' hpp
    · intro x hx x' hx' hxx'
      have key : ∀ y ∈ W₀, Disjoint Mnew (M₀ y) := by
        intro y hy
        rw [disjoint_left]
        intro p hp hp'
        obtain ⟨h1, h2⟩ := hMnew_mem p hp
        have := (hfprop p.1 h1).2.2.2.2.2
        apply this
        rw [← h2]
        exact mem_biUnion.2 ⟨y, hy, hp'⟩
      by_cases hxw : x = w
      · subst hxw
        have hx'w : x' ≠ x := fun h => hxx' h.symm
        simp only [if_true, hx'w, if_false]
        exact key x' ((mem_insert.1 hx').resolve_left hx'w)
      · by_cases hx'w : x' = w
        · subst hx'w
          simp only [if_true, hxw, if_false]
          exact (key x ((mem_insert.1 hx).resolve_left hxw)).symm
        · simp only [hxw, hx'w, if_false]
          exact hM3 x ((mem_insert.1 hx).resolve_left hxw) x'
            ((mem_insert.1 hx').resolve_left hx'w) hxx'
    · have hcard : (insert w W₀).card = W₀.card + 1 := card_insert_of_notMem hw
      intro x hx
      by_cases hxw : x = w
      · subst hxw
        simp only [if_true]
        rw [hMnew_card, ← hP, ← hY]
        have hsum : ∑ a ∈ P, (e a : ℤ) ≤ D := by
          have h1 := card_filter_not_adj_product (G := G) P Y
          have h2 := hD P (filter_subset _ _) Y (filter_subset _ _)
          have h3 : ∑ a ∈ P, e a ≤ D := by rw [h1] at h2; exact h2
          exact_mod_cast h3
        have hsel : S'.card = P.card ∨
            ((P.card : ℤ) - S'.card) * (((Y.card : ℤ) - W₀.card) - S'.card) ≤ D := by
          rcases halt with h | h
          · exact Or.inl h
          · exact Or.inr (h.trans hsum)
        have := min_le_of_selection P.card Y.card S'.card W₀.card D hsel
        omega
      · simp only [hxw, if_false]
        have := hM4 x ((mem_insert.1 hx).resolve_left hxw)
        omega

end A4S1.Indep
