/-
# Pairing an **unbalanced** block.

The one-link step of a class-matched sweep pairs the row class `β` of the link of `u` with the
column class `ρ u β`.  At an *unperturbed* link the two traces have exactly the same size `c`, so
the pairing is a bijection between them (`BKLO.exists_class_pair_involution_avoiding`).  At a
**perturbed** link the two traces differ: the adversary may have deleted vertices from one side and
added vertices to the other, so the block `A ∪ B` a step has to pair up is unbalanced.

This file supplies the two purely combinatorial constructions that repair that.

* `BKLO.exists_greedy_pairing` — **peeling pairs off one set**: if every vertex of `A` is related
  to at least `2k` other vertices of `A`, then `A` contains `2k` vertices carrying a
  fixed-point-free involution with related pairs.  Greedy: pick a vertex, pick a partner, delete
  both, recurse — each deletion costs every remaining vertex at most two partners.
* `BKLO.exists_unbalanced_block_involution` — **one unbalanced block**: two disjoint sets, `A` the
  smaller one, with `B.card - A.card` even, carry a fixed-point-free involution of `A ∪ B` which
  sends every vertex of `A` across into `B` and pairs the `B.card - A.card` surplus vertices of `B`
  *inside* `B`.  So the only pairs that break the cross-side discipline are the surplus ones, and
  they stay inside a single class — which is what keeps the used degree of a vertex inside any
  *other* class small.

Everything here is `sorry`-free.
-/
import BKLO.ClassInvolution
import BKLO.BipartiteMatching

open Finset

namespace BKLO

variable {V : Type*} [DecidableEq V]

/-! ### Peeling related pairs off one set -/

/-- **Greedy pairing inside one set.**  If every vertex of `A` is related to at least `2k` other
vertices of `A`, then some `2k` vertices of `A` carry a fixed-point-free involution all of whose
pairs are related.  Pick a vertex, pick a partner, delete both and recurse: a deletion costs every
remaining vertex at most two of its partners. -/
theorem exists_greedy_pairing (r : V → V → Prop) [DecidableRel r]
    (hsymm : ∀ a b, r a b → r b a) :
    ∀ (k : ℕ) (A : Finset V), (∀ a ∈ A, 2 * k ≤ (A.filter (fun b => b ≠ a ∧ r a b)).card) →
      2 * k ≤ A.card →
      ∃ L : Finset V, L ⊆ A ∧ L.card = 2 * k ∧ ∃ p : V → V,
        (∀ z ∈ L, p z ∈ L) ∧ (∀ z ∈ L, p (p z) = z) ∧ (∀ z ∈ L, p z ≠ z) ∧
        (∀ z ∈ L, r z (p z)) := by
  classical
  intro k
  induction k with
  | zero =>
    intro A _ _
    exact ⟨∅, Finset.empty_subset _, by simp, id, by simp, by simp, by simp, by simp⟩
  | succ k ih =>
    intro A hdeg hcard
    -- a first vertex
    have hAne : A.Nonempty := by
      rw [← Finset.card_pos]
      omega
    obtain ⟨a, ha⟩ := hAne
    -- and a partner for it
    have hfil : (A.filter (fun b => b ≠ a ∧ r a b)).Nonempty := by
      rw [← Finset.card_pos]
      have := hdeg a ha
      omega
    obtain ⟨b, hb⟩ := hfil
    obtain ⟨hbA, hba, hrab⟩ := Finset.mem_filter.1 hb
    have hab : a ≠ b := fun h => hba h.symm
    set A' : Finset V := A \ {a, b} with hA'def
    have hpair : ({a, b} : Finset V).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simpa using hab), Finset.card_singleton]
    have hsub : ({a, b} : Finset V) ⊆ A := by
      intro z hz
      rcases Finset.mem_insert.1 hz with rfl | hz'
      · exact ha
      · rw [Finset.mem_singleton.1 hz']; exact hbA
    have hA'card : A'.card = A.card - 2 := by
      rw [hA'def, Finset.card_sdiff_of_subset hsub, hpair]
    -- the degrees inside the smaller set
    have hA'deg : ∀ z ∈ A', 2 * k ≤ (A'.filter (fun w => w ≠ z ∧ r z w)).card := by
      intro z hz
      have hzA : z ∈ A := (Finset.mem_sdiff.1 hz).1
      have hsub2 : A.filter (fun w => w ≠ z ∧ r z w) \ {a, b}
          ⊆ A'.filter (fun w => w ≠ z ∧ r z w) := by
        intro w hw
        obtain ⟨hw1, hw2⟩ := Finset.mem_sdiff.1 hw
        obtain ⟨hwA, hwr⟩ := Finset.mem_filter.1 hw1
        exact Finset.mem_filter.2 ⟨Finset.mem_sdiff.2 ⟨hwA, hw2⟩, hwr⟩
      have h1 := Finset.card_le_card hsub2
      have h2 : (A.filter (fun w => w ≠ z ∧ r z w) \ ({a, b} : Finset V)).card
          = (A.filter (fun w => w ≠ z ∧ r z w)).card
            - (({a, b} : Finset V) ∩ A.filter (fun w => w ≠ z ∧ r z w)).card :=
        Finset.card_sdiff
      have h3 : (({a, b} : Finset V) ∩ A.filter (fun w => w ≠ z ∧ r z w)).card ≤ 2 := by
        refine le_trans (Finset.card_le_card Finset.inter_subset_left) ?_
        omega
      have h5 := hdeg z hzA
      omega
    have hA'size : 2 * k ≤ A'.card := by omega
    obtain ⟨L', hL'A, hL'card, p', hp1, hp2, hp3, hp4⟩ := ih A' hA'deg hA'size
    have haL' : a ∉ L' := by
      intro hcon
      exact (Finset.mem_sdiff.1 (hL'A hcon)).2 (Finset.mem_insert_self a _)
    have hbL' : b ∉ L' := by
      intro hcon
      exact (Finset.mem_sdiff.1 (hL'A hcon)).2
        (Finset.mem_insert_of_mem (Finset.mem_singleton_self b))
    set p : V → V := fun z => if z = a then b else if z = b then a else p' z with hpdef
    have hpa : p a = b := by
      show (if a = a then b else if a = b then a else p' a) = b
      rw [if_pos rfl]
    have hpb : p b = a := by
      show (if b = a then b else if b = b then a else p' b) = a
      rw [if_neg hba, if_pos rfl]
    have hpz : ∀ z, z ≠ a → z ≠ b → p z = p' z := by
      intro z h1 h2
      show (if z = a then b else if z = b then a else p' z) = p' z
      rw [if_neg h1, if_neg h2]
    set L : Finset V := insert a (insert b L') with hLdef
    have hLmem : ∀ z ∈ L, z = a ∨ z = b ∨ z ∈ L' := by
      intro z hz
      rcases Finset.mem_insert.1 hz with rfl | hz1
      · exact Or.inl rfl
      rcases Finset.mem_insert.1 hz1 with rfl | hz2
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr hz2)
    have haL : a ∈ L := Finset.mem_insert_self a _
    have hbL : b ∈ L := Finset.mem_insert_of_mem (Finset.mem_insert_self b _)
    have hL'L : ∀ z ∈ L', z ∈ L :=
      fun z hz => Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hz)
    have hL'ne : ∀ z ∈ L', z ≠ a ∧ z ≠ b := by
      intro z hz
      exact ⟨fun h => haL' (h ▸ hz), fun h => hbL' (h ▸ hz)⟩
    refine ⟨L, ?_, ?_, p, ?_, ?_, ?_, ?_⟩
    · intro z hz
      rcases hLmem z hz with rfl | rfl | hz2
      · exact ha
      · exact hbA
      · exact (Finset.mem_sdiff.1 (hL'A hz2)).1
    · rw [hLdef, Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert]
        push_neg
        exact ⟨hab, haL'⟩), Finset.card_insert_of_notMem hbL', hL'card]
      omega
    · intro z hz
      rcases hLmem z hz with rfl | rfl | hz2
      · rw [hpa]; exact hbL
      · rw [hpb]; exact haL
      · obtain ⟨h1, h2⟩ := hL'ne z hz2
        rw [hpz z h1 h2]
        exact hL'L _ (hp1 z hz2)
    · intro z hz
      rcases hLmem z hz with rfl | rfl | hz2
      · rw [hpa, hpb]
      · rw [hpb, hpa]
      · obtain ⟨h1, h2⟩ := hL'ne z hz2
        obtain ⟨h3, h4⟩ := hL'ne _ (hp1 z hz2)
        rw [hpz z h1 h2, hpz _ h3 h4]
        exact hp2 z hz2
    · intro z hz
      rcases hLmem z hz with rfl | rfl | hz2
      · rw [hpa]; exact fun h => hab h.symm
      · rw [hpb]; exact hab
      · obtain ⟨h1, h2⟩ := hL'ne z hz2
        rw [hpz z h1 h2]
        exact hp3 z hz2
    · intro z hz
      rcases hLmem z hz with rfl | rfl | hz2
      · rw [hpa]; exact hrab
      · rw [hpb]; exact hsymm _ _ hrab
      · obtain ⟨h1, h2⟩ := hL'ne z hz2
        rw [hpz z h1 h2]
        exact hp4 z hz2

/-! ### One unbalanced block -/

/-- **An unbalanced block is paired up, the surplus staying inside one side.**

`A` and `B` are disjoint, `A` is the smaller side and the surplus `B.card - A.card` is even.  If

* every vertex of `B` is related to at least `B.card - A.card` other vertices of `B`,
* every vertex of `A` is related to more than half of `B`, with room for the surplus,
* every vertex of `B` is related to more than half of `A`,

then `A ∪ B` carries a fixed-point-free involution with related pairs which sends every vertex of
`A` into `B`, and which pairs the surplus set `L ⊆ B` — of size exactly `B.card - A.card` — inside
`B`.  Every pair therefore either crosses from `A` to `B` or stays inside `B`. -/
theorem exists_unbalanced_block_involution {A B : Finset V} (hdisj : Disjoint A B)
    (r : V → V → Prop) [DecidableRel r] (hsymm : ∀ a b, r a b → r b a)
    (hle : A.card ≤ B.card)
    (hpar : Even (B.card - A.card))
    (hBdeg : ∀ b ∈ B, B.card - A.card ≤ (B.filter (fun z => z ≠ b ∧ r b z)).card)
    (hABdeg : ∀ a ∈ A, A.card + 2 * (B.card - A.card) < 2 * (B.filter (fun z => r a z)).card)
    (hBAdeg : ∀ b ∈ B, A.card < 2 * (A.filter (fun z => r z b)).card) :
    ∃ (L : Finset V) (p : V → V), L ⊆ B ∧ L.card = B.card - A.card ∧
      (∀ a ∈ A, p a ∈ B) ∧ (∀ z ∈ L, p z ∈ L) ∧ (∀ z ∈ B, z ∉ L → p z ∈ A) ∧
      (∀ z ∈ A ∪ B, p z ∈ A ∪ B) ∧ (∀ z ∈ A ∪ B, p (p z) = z) ∧
      (∀ z ∈ A ∪ B, p z ≠ z) ∧ (∀ z ∈ A ∪ B, r z (p z)) := by
  classical
  obtain ⟨k, hk⟩ := hpar
  have hk2 : B.card - A.card = 2 * k := by omega
  -- peel the surplus off `B`
  obtain ⟨L, hLB, hLcard, pL, hL1, hL2, hL3, hL4⟩ :=
    exists_greedy_pairing r hsymm k B (by
      intro b hb
      have := hBdeg b hb
      omega) (by omega)
  set B' : Finset V := B \ L with hB'def
  have hB'card : B'.card = A.card := by
    rw [hB'def, Finset.card_sdiff_of_subset hLB, hLcard]
    omega
  -- match `A` with the rest of `B`
  have hAB' : ∀ a ∈ A, B'.card < 2 * (B'.filter (fun z => r a z)).card := by
    intro a ha
    have h1 : B.filter (fun z => r a z) \ L ⊆ B'.filter (fun z => r a z) := by
      intro z hz
      obtain ⟨hz1, hz2⟩ := Finset.mem_sdiff.1 hz
      obtain ⟨hzB, hzr⟩ := Finset.mem_filter.1 hz1
      exact Finset.mem_filter.2 ⟨Finset.mem_sdiff.2 ⟨hzB, hz2⟩, hzr⟩
    have h2 : (B.filter (fun z => r a z) \ L).card
        = (B.filter (fun z => r a z)).card - (L ∩ B.filter (fun z => r a z)).card :=
      Finset.card_sdiff
    have h4 : (L ∩ B.filter (fun z => r a z)).card ≤ L.card :=
      Finset.card_le_card Finset.inter_subset_left
    have h5 := Finset.card_le_card h1
    have h6 := hABdeg a ha
    omega
  have hB'A : ∀ b ∈ B', A.card < 2 * (A.filter (fun z => r z b)).card := by
    intro b hb
    exact hBAdeg b (Finset.mem_sdiff.1 hb).1
  obtain ⟨f, hf1, hf2, hf3⟩ :=
    exists_matching_of_half_degree (A := A) (B := B') (r := r)
      hB'card.symm (fun a ha => hAB' a ha) (fun b hb => hB'A b hb)
  -- turn the matching into an involution of `A ∪ B'`
  have hdisj' : Disjoint A B' :=
    Finset.disjoint_of_subset_right Finset.sdiff_subset hdisj
  obtain ⟨p0, hp0A, hp0U, hp0inv, hp0ne, hp0r⟩ :=
    exists_swap_involution hdisj' hf1 hf3 hB'card.symm r hsymm hf2
  -- glue the two involutions
  set p : V → V := fun z => if z ∈ L then pL z else p0 z with hpdef
  have hpL : ∀ z ∈ L, p z = pL z := by
    intro z hz
    show (if z ∈ L then pL z else p0 z) = pL z
    rw [if_pos hz]
  have hpnotL : ∀ z, z ∉ L → p z = p0 z := by
    intro z hz
    show (if z ∈ L then pL z else p0 z) = p0 z
    rw [if_neg hz]
  have hAL : ∀ a ∈ A, a ∉ L := fun a ha h => (Finset.disjoint_left.1 hdisj) ha (hLB h)
  have hmemU : ∀ z ∈ A ∪ B, z ∉ L → z ∈ A ∪ B' := by
    intro z hz hzL
    rcases Finset.mem_union.1 hz with h | h
    · exact Finset.mem_union_left _ h
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.2 ⟨h, hzL⟩)
  -- the matching is onto the rest of `B`
  have himg : A.image f = B' := by
    refine Finset.eq_of_subset_of_card_le (fun b hb => ?_) ?_
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hb
      exact hf1 a ha
    · rw [Finset.card_image_of_injOn hf3, hB'card]
  refine ⟨L, p, hLB, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha
    rw [hpnotL a (hAL a ha), hp0A a ha]
    exact (Finset.mem_sdiff.1 (hf1 a ha)).1
  · intro z hz
    rw [hpL z hz]
    exact hL1 z hz
  · -- the non-surplus vertices of `B` go back into `A`
    intro z hzB hzL
    have hzB' : z ∈ B' := Finset.mem_sdiff.2 ⟨hzB, hzL⟩
    have hzU : z ∈ A ∪ B' := Finset.mem_union_right _ hzB'
    rw [hpnotL z hzL]
    rcases Finset.mem_union.1 (hp0U z hzU) with h | h
    · exact h
    · exfalso
      have hmem : p0 z ∈ A.image f := by rw [himg]; exact h
      obtain ⟨a, ha, hfa⟩ := Finset.mem_image.1 hmem
      have hpa : p0 a = p0 z := by rw [hp0A a ha]; exact hfa
      have h1 : p0 (p0 a) = a := hp0inv a (Finset.mem_union_left _ ha)
      have h2 : p0 (p0 z) = z := hp0inv z hzU
      rw [hpa, h2] at h1
      exact (Finset.disjoint_left.1 hdisj') (h1 ▸ ha) hzB'
  · intro z hz
    by_cases hzL : z ∈ L
    · rw [hpL z hzL]
      exact Finset.mem_union_right _ (hLB (hL1 z hzL))
    · rw [hpnotL z hzL]
      rcases Finset.mem_union.1 (hp0U z (hmemU z hz hzL)) with h | h
      · exact Finset.mem_union_left _ h
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.1 h).1
  · intro z hz
    by_cases hzL : z ∈ L
    · rw [hpL z hzL, hpL _ (hL1 z hzL)]
      exact hL2 z hzL
    · have hzU : z ∈ A ∪ B' := hmemU z hz hzL
      have h1 : p0 z ∈ A ∪ B' := hp0U z hzU
      have h2 : p0 z ∉ L := by
        rcases Finset.mem_union.1 h1 with h | h
        · exact fun hcon => (Finset.disjoint_left.1 hdisj) h (hLB hcon)
        · exact (Finset.mem_sdiff.1 h).2
      rw [hpnotL z hzL, hpnotL _ h2]
      exact hp0inv z hzU
  · intro z hz
    by_cases hzL : z ∈ L
    · rw [hpL z hzL]
      exact hL3 z hzL
    · rw [hpnotL z hzL]
      exact hp0ne z (hmemU z hz hzL)
  · intro z hz
    by_cases hzL : z ∈ L
    · rw [hpL z hzL]
      exact hL4 z hzL
    · rw [hpnotL z hzL]
      exact hp0r z (hmemU z hz hzL)

end BKLO
