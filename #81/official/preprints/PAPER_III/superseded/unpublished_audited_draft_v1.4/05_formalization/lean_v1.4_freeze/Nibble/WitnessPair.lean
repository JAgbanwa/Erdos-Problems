/-
# Nibble — the witness bound of a packing triangle, driven by its own uncovered degrees

`Nibble.witness_triple_le` bounds the total number of witnesses carried by the three edges of a
packing triangle by `D + 2`, where `D` is the *global* maximum uncovered star.  That is wasteful:
by `Nibble.no_double_witness` essentially only one edge `pq` of the triangle carries witnesses at
all, and its witnesses are common uncovered neighbours of `p` and of `q`, so there are at most
`min(d_p, d_q) ≤ (d_p + d_q)/2` of them.

`Nibble.witness_pair_bound` records exactly this: there is a pair `P = {p, q}` of vertices of the
triangle with

  `∑_{(a,b) ∈ V(T) × V(T)} |wit a b| ≤ (d_p + d_q) + 4`.

Combined with the capacity bound `Nibble.two_mul_card_triAt_add_unDeg_le` this replaces the global
maximum `D` by a quantity controlled by the uncovered-degree profile itself.

Sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.TriangleCapacity

open Finset SimpleGraph Hypergraph Nibble.YusterE

namespace Nibble

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ### The witness sum over an ordered triple -/

/-- The ordered witness count over a triple of distinct vertices. -/
theorem sum_witCard_product_triple (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset (EdgeV G))) {x y z : V} (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) :
    ∑ p ∈ ({x, y, z} : Finset V) ×ˢ ({x, y, z} : Finset V), witCard G M p
      = 2 * (witCard G M (x, y) + witCard G M (y, z) + witCard G M (x, z)) := by
  classical
  have hsymm : ∀ a b : V, witCard G M (a, b) = witCard G M (b, a) := by
    intro a b
    by_cases h : G.Adj a b
    · rw [witCard, witCard, if_pos h, if_pos h.symm, Finset.inter_comm]
    · rw [witCard, witCard, if_neg h, if_neg (fun h' => h h'.symm)]
  have hdiag : ∀ a : V, witCard G M (a, a) = 0 := by
    intro a
    rw [witCard, if_neg (SimpleGraph.irrefl G)]
  have htriple : ∀ g : V → ℕ, ∑ t ∈ ({x, y, z} : Finset V), g t = g x + g y + g z := by
    intro g
    rw [Finset.sum_insert (by simp [hxy, hxz]), Finset.sum_insert (by simp [hyz]),
      Finset.sum_singleton, add_assoc]
  rw [Finset.sum_product]
  rw [htriple (fun a => ∑ b ∈ ({x, y, z} : Finset V), witCard G M (a, b))]
  rw [htriple (fun b => witCard G M (x, b)), htriple (fun b => witCard G M (y, b)),
    htriple (fun b => witCard G M (z, b))]
  rw [hdiag x, hdiag y, hdiag z, ← hsymm x y, ← hsymm x z, ← hsymm y z]
  ring

/-! ### The pair bound -/

/-- **The witness bound of a packing triangle.**  Some pair `{p, q}` of its vertices carries the
whole witness count: `∑_{(a,b)} |wit a b| ≤ d_p + d_q + 4`. -/
theorem witness_pair_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    {M : Finset (Finset (EdgeV G))} (hM : IsMatching (triangleHypergraphSub G) M)
    (hmin : ∀ M' : Finset (Finset (EdgeV G)), IsMatching (triangleHypergraphSub G) M' →
      uncoveredTot G M' ≤ uncoveredTot G M → uncoveredPot G M ≤ uncoveredPot G M')
    {T : Finset (EdgeV G)} (hT : T ∈ M) :
    ∃ P : Finset V, P.card = 2 ∧ P ⊆ triOf G T ∧
      ∑ p ∈ (triOf G T) ×ˢ (triOf G T), witCard G M p ≤ (∑ v ∈ P, unDeg G M v) + 4 := by
  classical
  obtain ⟨x, y, z, hxy, hyz, hxz, rfl⟩ := exists_triE_of_mem G (hM.subset hT)
  have htri : triOf G (triE G hxy hyz hxz) = ({x, y, z} : Finset V) := triOf_triE G hxy hyz hxz
  simp only [htri]
  rw [sum_witCard_product_triple G M hxy.ne hyz.ne hxz.ne]
  set A := unNbr G M x ∩ unNbr G M y with hA
  set B := unNbr G M y ∩ unNbr G M z with hB
  set C := unNbr G M x ∩ unNbr G M z with hC
  have hwx : witCard G M (x, y) = A.card := by rw [witCard, if_pos hxy]
  have hwy : witCard G M (y, z) = B.card := by rw [witCard, if_pos hyz]
  have hwz : witCard G M (x, z) = C.card := by rw [witCard, if_pos hxz]
  rw [hwx, hwy, hwz]
  -- the degree bounds on the three witness sets
  have hAx : A.card ≤ unDeg G M x :=
    le_trans (Finset.card_le_card Finset.inter_subset_left) (le_of_eq (card_unNbr G M x))
  have hAy : A.card ≤ unDeg G M y :=
    le_trans (Finset.card_le_card Finset.inter_subset_right) (le_of_eq (card_unNbr G M y))
  have hBy : B.card ≤ unDeg G M y :=
    le_trans (Finset.card_le_card Finset.inter_subset_left) (le_of_eq (card_unNbr G M y))
  have hBz : B.card ≤ unDeg G M z :=
    le_trans (Finset.card_le_card Finset.inter_subset_right) (le_of_eq (card_unNbr G M z))
  have hCx : C.card ≤ unDeg G M x :=
    le_trans (Finset.card_le_card Finset.inter_subset_left) (le_of_eq (card_unNbr G M x))
  have hCz : C.card ≤ unDeg G M z :=
    le_trans (Finset.card_le_card Finset.inter_subset_right) (le_of_eq (card_unNbr G M z))
  -- the three pairwise-collapse statements, from the double swap
  have hAC : ∀ p ∈ A, ∀ r ∈ C, p = r := by
    intro p hp r hr
    by_contra hne
    exact no_double_witness G hM hmin hxy hyz hxz hT hp hr hne
  have hAB : ∀ p ∈ A, ∀ q ∈ B, p = q := by
    intro p hp q hq
    by_contra hne
    have hyx : G.Adj y x := hxy.symm
    have hTyxz : triE G hyx hxz hyz ∈ M := by
      rwa [triE_congr G hxy hyz hxz hyx hxz hyz (by ext t; simp; itauto)]
    refine no_double_witness G hM hmin hyx hxz hyz hTyxz ?_ hq hne
    rw [hA, Finset.mem_inter] at hp
    exact Finset.mem_inter.mpr ⟨hp.2, hp.1⟩
  have hBC : ∀ q ∈ B, ∀ r ∈ C, q = r := by
    intro q hq r hr
    by_contra hne
    have hzy : G.Adj z y := hyz.symm
    have hyx : G.Adj y x := hxy.symm
    have hzx : G.Adj z x := hxz.symm
    have hTzyx : triE G hzy hyx hzx ∈ M := by
      rwa [triE_congr G hxy hyz hxz hzy hyx hzx (by ext t; simp; itauto)]
    refine no_double_witness G hM hmin hzy hyx hzx hTzyx ?_ ?_ hne
    · rw [hB, Finset.mem_inter] at hq
      exact Finset.mem_inter.mpr ⟨hq.2, hq.1⟩
    · rw [hC, Finset.mem_inter] at hr
      exact Finset.mem_inter.mpr ⟨hr.2, hr.1⟩
  -- the sums over the three candidate pairs
  have hsumxy : ∑ v ∈ ({x, y} : Finset V), unDeg G M v = unDeg G M x + unDeg G M y :=
    Finset.sum_pair hxy.ne
  have hsumyz : ∑ v ∈ ({y, z} : Finset V), unDeg G M v = unDeg G M y + unDeg G M z :=
    Finset.sum_pair hyz.ne
  have hsumxz : ∑ v ∈ ({x, z} : Finset V), unDeg G M v = unDeg G M x + unDeg G M z :=
    Finset.sum_pair hxz.ne
  rcases A.eq_empty_or_nonempty with hAe | ⟨p, hp⟩
  · rcases B.eq_empty_or_nonempty with hBe | ⟨q, hq⟩
    · -- only `C` can carry witnesses
      refine ⟨{x, z}, Finset.card_pair hxz.ne, by simp [Finset.insert_subset_iff], ?_⟩
      rw [hsumxz, hAe, hBe]
      simp only [Finset.card_empty]
      omega
    · -- `B` carries witnesses
      refine ⟨{y, z}, Finset.card_pair hyz.ne, by simp, ?_⟩
      rw [hsumyz, hAe]
      simp only [Finset.card_empty]
      rcases C.eq_empty_or_nonempty with hCe | ⟨r, hr⟩
      · rw [hCe]
        simp only [Finset.card_empty]
        omega
      · have h1 : B.card ≤ 1 := Finset.card_le_one.mpr (fun a ha b hb => by
          rw [hBC a ha r hr, hBC b hb r hr])
        have h2 : C.card ≤ 1 := Finset.card_le_one.mpr (fun a ha b hb => by
          rw [← hBC q hq a ha, ← hBC q hq b hb])
        omega
  · -- `A` carries witnesses
    refine ⟨{x, y}, Finset.card_pair hxy.ne, by simp [Finset.insert_subset_iff], ?_⟩
    rw [hsumxy]
    have hdx : 1 ≤ unDeg G M x := by
      rw [← card_unNbr G M x]
      exact Finset.card_pos.mpr ⟨p, (Finset.mem_inter.mp hp).1⟩
    have hdy : 1 ≤ unDeg G M y := by
      rw [← card_unNbr G M y]
      exact Finset.card_pos.mpr ⟨p, (Finset.mem_inter.mp hp).2⟩
    rcases B.eq_empty_or_nonempty with hBe | ⟨q, hq⟩
    · rcases C.eq_empty_or_nonempty with hCe | ⟨r, hr⟩
      · rw [hBe, hCe]
        simp only [Finset.card_empty]
        omega
      · have h1 : A.card ≤ 1 := Finset.card_le_one.mpr (fun a ha b hb => by
          rw [hAC a ha r hr, hAC b hb r hr])
        have h2 : C.card ≤ 1 := Finset.card_le_one.mpr (fun a ha b hb => by
          rw [← hAC p hp a ha, ← hAC p hp b hb])
        rw [hBe]
        simp only [Finset.card_empty]
        omega
    · have h1 : A.card ≤ 1 := Finset.card_le_one.mpr (fun a ha b hb => by
        rw [hAB a ha q hq, hAB b hb q hq])
      have h2 : B.card ≤ 1 := Finset.card_le_one.mpr (fun a ha b hb => by
        rw [← hAB p hp a ha, ← hAB p hp b hb])
      have h3 : C.card ≤ 1 := Finset.card_le_one.mpr (fun a ha b hb => by
        rw [← hAC p hp a ha, ← hAC p hp b hb])
      omega

/-! ### The witness count, fibred over the packing -/

/-- **The witness count, fibred over the packing.**  Only covered edges carry witnesses, and each
covered edge lies in a unique packing triangle. -/
theorem starPairs_le_triOf (G : SimpleGraph V) [DecidableRel G.Adj]
    {M : Finset (Finset (EdgeV G))} (hM : IsMatching (triangleHypergraphSub G) M)
    (hmin : ∀ M' : Finset (Finset (EdgeV G)), IsMatching (triangleHypergraphSub G) M' →
      uncoveredTot G M' ≤ uncoveredTot G M → uncoveredPot G M ≤ uncoveredPot G M') :
    ∑ p : V × V, witCard G M p
      ≤ ∑ T ∈ M, ∑ p ∈ (triOf G T) ×ˢ (triOf G T), witCard G M p := by
  classical
  have hex : ∀ p : V × V, ∃ T : Finset (EdgeV G),
      witCard G M p ≠ 0 → T ∈ M ∧ ∀ h : G.Adj p.1 p.2, edgeE G h ∈ T := by
    intro p
    by_cases hne : witCard G M p ≠ 0
    · have hab : G.Adj p.1 p.2 := by
        by_contra h
        exact hne (by rw [witCard, if_neg h])
      have hcov : ¬ UncE G M (edgeE G hab) := by
        intro hunc
        exact hne (witCard_eq_zero_of_unc G hM hmin hab hunc)
      simp only [UncE, not_forall, not_not] at hcov
      obtain ⟨T, hT, hmem⟩ := hcov
      refine ⟨T, fun _ => ⟨hT, fun h => ?_⟩⟩
      have : h = hab := rfl
      subst this
      exact hmem
    · exact ⟨∅, fun h => absurd h hne⟩
  choose φ hφ using hex
  set Good := (Finset.univ : Finset (V × V)).filter (fun p => witCard G M p ≠ 0) with hGood
  have h1 : ∑ p : V × V, witCard G M p = ∑ p ∈ Good, witCard G M p := by
    rw [hGood]
    exact (Finset.sum_filter_ne_zero _).symm
  have hmaps : ∀ p ∈ Good, φ p ∈ M := by
    intro p hp
    exact (hφ p (Finset.mem_filter.mp hp).2).1
  rw [h1, ← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_le_sum (fun T hT => ?_)
  refine Finset.sum_le_sum_of_subset (fun p hp => ?_)
  rw [Finset.mem_filter] at hp
  obtain ⟨hpG, hpT⟩ := hp
  have hne := (Finset.mem_filter.mp hpG).2
  have hab : G.Adj p.1 p.2 := by
    by_contra h
    exact hne (by rw [witCard, if_neg h])
  have hmem : edgeE G hab ∈ T := by
    have := (hφ p hne).2 hab
    rwa [hpT] at this
  refine Finset.mem_product.mpr ⟨?_, ?_⟩ <;>
    exact Finset.mem_biUnion.mpr ⟨edgeE G hab, hmem, by simp⟩

end Nibble
