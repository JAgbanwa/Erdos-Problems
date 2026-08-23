/-
# Nibble — the double swap move and the witness bound for a packing triangle

This file adds a **new local move** to the swap engine of `Nibble.DenseTriangleNibbleDegProof`.
Where `Nibble.swap_stability` exchanges one packing triangle for one new triangle, the move here
removes one packing triangle `{a, b, z}` and inserts *two* new triangles `{v, a, b}` and
`{w, a, z}`, where `v` is joined by uncovered edges to both `a` and `b`, and `w ≠ v` is joined by
uncovered edges to both `a` and `z`.

The move covers the four uncovered edges `va, vb, wa, wz` and frees only `bz`, so it decreases both
the uncovered incidence count and the potential `∑_u |uncovered star at u|²`; a potential-minimal
matching therefore admits no such configuration (`Nibble.no_double_witness`).

Writing `wit a b = unNbr M a ∩ unNbr M b` for the set of common *uncovered* neighbours of an
adjacent pair (the "witnesses" of the edge `ab`), the consequence used later is
`Nibble.witness_triple_le`: for a packing triangle `{x, y, z}` of a potential-minimal matching,

  `|wit x y| + |wit y z| + |wit x z| ≤ D + 2`,

where `D` bounds the uncovered stars.  In words: essentially only *one* of the three edges of a
packing triangle can carry witnesses at all.

Sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.DenseTriangleNibbleDegHalf

open Finset SimpleGraph Hypergraph Nibble.YusterE

namespace Nibble

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ### Small edge helpers -/

/-- The hypergraph vertex attached to an edge does not depend on the orientation. -/
theorem edgeE_swap (G : SimpleGraph V) [DecidableRel G.Adj] {u w : V} (h : G.Adj u w)
    (h' : G.Adj w u) : edgeE G h' = edgeE G h := by
  apply Subtype.ext
  simp [Finset.pair_comm]

/-- Being joined by an uncovered edge is symmetric. -/
theorem unNbr_symm (G : SimpleGraph V) [DecidableRel G.Adj] {M : Finset (Finset (EdgeV G))}
    {v w : V} (h : w ∈ unNbr G M v) : v ∈ unNbr G M w := by
  obtain ⟨hvw, hunc⟩ := (mem_unNbr G).mp h
  refine (mem_unNbr G).mpr ⟨hvw.symm, ?_⟩
  rw [edgeE_swap G hvw hvw.symm]
  exact hunc

/-- The hyperedge of a triangle only depends on its vertex set. -/
theorem triE_congr (G : SimpleGraph V) [DecidableRel G.Adj] {x y z x' y' z' : V}
    (hxy : G.Adj x y) (hyz : G.Adj y z) (hxz : G.Adj x z)
    (hxy' : G.Adj x' y') (hyz' : G.Adj y' z') (hxz' : G.Adj x' z')
    (hset : ({x', y', z'} : Finset V) = {x, y, z}) :
    triE G hxy' hyz' hxz' = triE G hxy hyz hxz := by
  rw [triE_eq_subtype G hxy' hyz' hxz', triE_eq_subtype G hxy hyz hxz, hset]

/-! ### The double swap move -/

/-- **The double swap.**  A potential-minimal matching admits no packing triangle `{a, b, z}`
carrying two *distinct* witnesses on two different edges: `v` joined to `a` and `b` by uncovered
edges and `w ≠ v` joined to `a` and `z` by uncovered edges.

Removing the triangle and inserting `{v, a, b}` and `{w, a, z}` covers the four uncovered edges
`va, vb, wa, wz` and frees only `bz`. -/
theorem no_double_witness (G : SimpleGraph V) [DecidableRel G.Adj]
    {M : Finset (Finset (EdgeV G))} (hM : IsMatching (triangleHypergraphSub G) M)
    (hmin : ∀ M' : Finset (Finset (EdgeV G)), IsMatching (triangleHypergraphSub G) M' →
      uncoveredTot G M' ≤ uncoveredTot G M → uncoveredPot G M ≤ uncoveredPot G M')
    {a b z v w : V} (hab : G.Adj a b) (hbz : G.Adj b z) (haz : G.Adj a z)
    (hT : triE G hab hbz haz ∈ M)
    (hv : v ∈ unNbr G M a ∩ unNbr G M b) (hw : w ∈ unNbr G M a ∩ unNbr G M z)
    (hvw : v ≠ w) : False := by
  classical
  set T := triE G hab hbz haz with hTdef
  obtain ⟨hav, huav⟩ := (mem_unNbr G).mp (Finset.mem_inter.mp hv).1
  obtain ⟨hbv, hubv⟩ := (mem_unNbr G).mp (Finset.mem_inter.mp hv).2
  obtain ⟨haw, huaw⟩ := (mem_unNbr G).mp (Finset.mem_inter.mp hw).1
  obtain ⟨hzw, huzw⟩ := (mem_unNbr G).mp (Finset.mem_inter.mp hw).2
  have hvb : G.Adj v b := hbv.symm
  have hwz : G.Adj w z := hzw.symm
  -- distinctness
  have hva : v ≠ a := fun h => (hav.ne) h.symm
  have hvbne : v ≠ b := fun h => (hbv.ne) h.symm
  have habz : edgeE G haz ∈ T := by rw [hTdef, mem_triE]; exact Or.inr (Or.inr rfl)
  have hvz : v ≠ z := by
    rintro rfl
    exact huav T hT (by rw [show edgeE G hav = edgeE G haz from rfl]; exact habz)
  have hwa : w ≠ a := fun h => (haw.ne) h.symm
  have hwzne : w ≠ z := fun h => (hzw.ne) h.symm
  have habT : edgeE G hab ∈ T := by rw [hTdef, mem_triE]; exact Or.inl rfl
  have hwb : w ≠ b := by
    rintro rfl
    exact huaw T hT (by rw [show edgeE G haw = edgeE G hab from rfl]; exact habT)
  -- the two new triangles
  set P1 := triE G hav hvb hab with hP1
  set P2 := triE G haw hwz haz with hP2
  have hP1H : P1 ∈ triangleHypergraphSub G := triE_mem_hypergraph G hav hvb hab
  have hP2H : P2 ∈ triangleHypergraphSub G := triE_mem_hypergraph G haw hwz haz
  -- `insert P2 (M.erase T)` is a matching
  have hfree2 : ∀ E ∈ P2, E ∈ T ∨ UncE G M E := by
    intro E hE
    rw [hP2, mem_triE] at hE
    rcases hE with rfl | rfl | rfl
    · exact Or.inr huaw
    · exact Or.inr (by rw [edgeE_swap G hzw hwz]; exact huzw)
    · exact Or.inl habz
  have hM2 : IsMatching (triangleHypergraphSub G) (insert P2 (M.erase T)) :=
    isMatching_swap G hM hT hP2H hfree2
  -- `insert P1 (insert P2 (M.erase T))` is a matching
  have hnotP2 : ∀ E ∈ P1, E ∉ P2 := by
    intro E hE hE2
    rw [hP1, mem_triE] at hE
    rw [hP2, mem_triE] at hE2
    rcases hE with rfl | rfl | rfl <;> rcases hE2 with h | h | h <;>
      [ (have := (edgeE_eq_iff G hav haw).mp h);
        (have := (edgeE_eq_iff G hav hwz).mp h);
        (have := (edgeE_eq_iff G hav haz).mp h);
        (have := (edgeE_eq_iff G hvb haw).mp h);
        (have := (edgeE_eq_iff G hvb hwz).mp h);
        (have := (edgeE_eq_iff G hvb haz).mp h);
        (have := (edgeE_eq_iff G hab haw).mp h);
        (have := (edgeE_eq_iff G hab hwz).mp h);
        (have := (edgeE_eq_iff G hab haz).mp h) ] <;>
    · revert this
      simp only [Finset.ext_iff, Finset.mem_insert, Finset.mem_singleton]
      intro hEq
      first
        | (exact absurd ((hEq v).mp (Or.inr rfl)) (by simp [hva, hvw, hvz]))
        | (exact absurd ((hEq b).mp (Or.inr rfl)) (by simp [hwb.symm, hbz.ne, hab.ne']))
  have hfree1 : ∀ E ∈ P1, UncE G (insert P2 (M.erase T)) E := by
    intro E hE T' hT' hmem
    rw [Finset.mem_insert] at hT'
    rcases hT' with rfl | hT'
    · exact hnotP2 E hE hmem
    · have hT'M : T' ∈ M := Finset.mem_of_mem_erase hT'
      have hT'ne : T' ≠ T := (Finset.mem_erase.mp hT').1
      rw [hP1, mem_triE] at hE
      rcases hE with rfl | rfl | rfl
      · exact huav T' hT'M hmem
      · exact (by rw [edgeE_swap G hbv hvb] at hmem; exact hubv T' hT'M hmem)
      · exact Finset.disjoint_left.mp (hM.disjoint T hT T' hT'M (fun h => hT'ne h.symm))
          habT hmem
  have hM' : IsMatching (triangleHypergraphSub G) (insert P1 (insert P2 (M.erase T))) :=
    isMatching_insert G hM2 hP1H hfree1
  set M' := insert P1 (insert P2 (M.erase T)) with hM'def
  -- the uncovered stars of `M'`
  set Q : Finset (EdgeV G) := P1 ∪ P2 with hQ
  have hstar : ∀ u : V, uncoveredAt G M' u
      = (uncoveredAt G M u ∪ T.filter (fun E => u ∈ E.val)) \ Q := by
    intro u
    rw [hM'def, uncoveredAt_insert, uncoveredAt_insert, uncoveredAt_erase G hM.disjoint hT]
    ext E
    simp only [hQ, Finset.mem_sdiff, Finset.mem_union]
    constructor
    · rintro ⟨⟨h, h2⟩, h1⟩
      exact ⟨h, fun hc => hc.elim h1 h2⟩
    · rintro ⟨h, hn⟩
      exact ⟨⟨h, fun hc => hn (Or.inr hc)⟩, fun hc => hn (Or.inl hc)⟩
  have key : ∀ u : V, unDeg G M' u + (uncoveredAt G M u ∩ Q).card
      ≤ unDeg G M u + ((T.filter (fun E => u ∈ E.val)) \ Q).card := by
    intro u
    set X := uncoveredAt G M u with hX
    set Y := T.filter (fun E => u ∈ E.val) with hY
    have h1 : unDeg G M' u = ((X ∪ Y) \ Q).card := by rw [unDeg, hstar u]
    have h2 : (X ∪ Y) \ Q ⊆ (X \ Q) ∪ (Y \ Q) := by
      intro E hE
      rw [Finset.mem_sdiff, Finset.mem_union] at hE
      rcases hE.1 with h | h
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨h, hE.2⟩)
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨h, hE.2⟩)
    have h3 : ((X ∪ Y) \ Q).card ≤ (X \ Q).card + (Y \ Q).card :=
      le_trans (Finset.card_le_card h2) (Finset.card_union_le _ _)
    have h4 : (X \ Q).card + (X ∩ Q).card = X.card := Finset.card_sdiff_add_card_inter _ _
    have h5 : unDeg G M u = X.card := rfl
    omega
  -- the fibres of `T` outside the new triangles reduce to the single edge `bz`
  have hYsub : ∀ u : V, (T.filter (fun E => u ∈ E.val)) \ Q ⊆ {edgeE G hbz} := by
    intro u E hE
    rw [Finset.mem_sdiff, Finset.mem_filter] at hE
    have hET : E ∈ T := hE.1.1
    rw [hTdef, mem_triE] at hET
    rcases hET with rfl | rfl | rfl
    · exact absurd (Finset.mem_union_left _ (by rw [hP1, mem_triE]; exact Or.inr (Or.inr rfl)))
        hE.2
    · exact Finset.mem_singleton_self _
    · exact absurd (Finset.mem_union_right _ (by rw [hP2, mem_triE]; exact Or.inr (Or.inr rfl)))
        hE.2
  have hYcard : ∀ u : V, ((T.filter (fun E => u ∈ E.val)) \ Q).card ≤ 1 := by
    intro u
    have := Finset.card_le_card (hYsub u)
    simpa using this
  have hY0 : ∀ u : V, u ≠ b → u ≠ z → ((T.filter (fun E => u ∈ E.val)) \ Q).card = 0 := by
    intro u hub huz
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro E hE
    have hEs := hYsub u hE
    rw [Finset.mem_singleton] at hEs
    rw [Finset.mem_sdiff, Finset.mem_filter] at hE
    have := hE.1.2
    rw [hEs] at this
    simp only [edgeE_val, Finset.mem_insert, Finset.mem_singleton] at this
    tauto
  -- three uncovered edges killed by the new triangles
  have hXb : 1 ≤ (uncoveredAt G M b ∩ Q).card := by
    refine Finset.card_pos.mpr ⟨edgeE G hvb, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
    · rw [mem_uncoveredAt]
      refine ⟨by simp, ?_⟩
      rw [edgeE_swap G hbv hvb]; exact hubv
    · exact Finset.mem_union_left _ (by rw [hP1, mem_triE]; exact Or.inr (Or.inl rfl))
  have hXz : 1 ≤ (uncoveredAt G M z ∩ Q).card := by
    refine Finset.card_pos.mpr ⟨edgeE G hwz, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
    · rw [mem_uncoveredAt]
      refine ⟨by simp, ?_⟩
      rw [edgeE_swap G hzw hwz]; exact huzw
    · exact Finset.mem_union_right _ (by rw [hP2, mem_triE]; exact Or.inr (Or.inl rfl))
  have hXv : 1 ≤ (uncoveredAt G M v ∩ Q).card := by
    refine Finset.card_pos.mpr ⟨edgeE G hav, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
    · rw [mem_uncoveredAt]
      exact ⟨by simp, huav⟩
    · exact Finset.mem_union_left _ (by rw [hP1, mem_triE]; exact Or.inl rfl)
  -- monotonicity of all uncovered stars, with a strict drop at `v`
  have hle : ∀ u : V, unDeg G M' u ≤ unDeg G M u := by
    intro u
    by_cases hub : u = b
    · subst hub
      have := key u
      have := hYcard u
      omega
    · by_cases huz : u = z
      · subst huz
        have := key u
        have := hYcard u
        omega
      · have := key u
        have := hY0 u hub huz
        omega
  have hlt : unDeg G M' v < unDeg G M v := by
    have h1 := key v
    have h2 := hY0 v hvbne hvz
    omega
  have htot : uncoveredTot G M' ≤ uncoveredTot G M :=
    Finset.sum_le_sum (fun i _ => hle i)
  have hpot : uncoveredPot G M' < uncoveredPot G M :=
    Finset.sum_lt_sum (fun i _ => Nat.pow_le_pow_left (hle i) 2)
      ⟨v, Finset.mem_univ v, Nat.pow_lt_pow_left hlt (by norm_num)⟩
  exact absurd (hmin _ hM' htot) (by omega)

/-! ### Witnesses of the three edges of a packing triangle -/

/-- **Only one edge of a packing triangle carries witnesses.**  For a potential-minimal matching,
the three edges of a packing triangle `{x, y, z}` have, in total, at most `D + 2` common uncovered
neighbours, where `D` bounds all uncovered stars. -/
theorem witness_triple_le (G : SimpleGraph V) [DecidableRel G.Adj]
    {M : Finset (Finset (EdgeV G))} (hM : IsMatching (triangleHypergraphSub G) M)
    (hmin : ∀ M' : Finset (Finset (EdgeV G)), IsMatching (triangleHypergraphSub G) M' →
      uncoveredTot G M' ≤ uncoveredTot G M → uncoveredPot G M ≤ uncoveredPot G M')
    {x y z : V} (hxy : G.Adj x y) (hyz : G.Adj y z) (hxz : G.Adj x z)
    (hT : triE G hxy hyz hxz ∈ M) {D : ℕ} (hD : ∀ u : V, unDeg G M u ≤ D) :
    (unNbr G M x ∩ unNbr G M y).card + (unNbr G M y ∩ unNbr G M z).card
      + (unNbr G M x ∩ unNbr G M z).card ≤ D + 2 := by
  classical
  set A := unNbr G M x ∩ unNbr G M y with hA
  set B := unNbr G M y ∩ unNbr G M z with hB
  set C := unNbr G M x ∩ unNbr G M z with hC
  -- cardinal bounds
  have hAD : A.card ≤ D :=
    le_trans (le_trans (Finset.card_le_card Finset.inter_subset_left)
      (le_of_eq (card_unNbr G M x))) (hD x)
  have hBD : B.card ≤ D :=
    le_trans (le_trans (Finset.card_le_card Finset.inter_subset_left)
      (le_of_eq (card_unNbr G M y))) (hD y)
  have hCD : C.card ≤ D :=
    le_trans (le_trans (Finset.card_le_card Finset.inter_subset_left)
      (le_of_eq (card_unNbr G M x))) (hD x)
  -- the three pairwise-equality statements, from the double swap
  have hAC : ∀ p ∈ A, ∀ r ∈ C, p = r := by
    intro p hp r hr
    by_contra hne
    exact no_double_witness G hM hmin hxy hyz hxz hT hp hr hne
  have hAB : ∀ p ∈ A, ∀ q ∈ B, p = q := by
    intro p hp q hq
    by_contra hne
    have hyx : G.Adj y x := hxy.symm
    have hTyxz : triE G hyx hxz hyz ∈ M := by
      rwa [triE_congr G hxy hyz hxz hyx hxz hyz (by ext t; simp; tauto)]
    refine no_double_witness G hM hmin hyx hxz hyz hTyxz ?_ hq hne
    rw [Finset.mem_inter] at hp ⊢
    exact ⟨hp.2, hp.1⟩
  have hBC : ∀ q ∈ B, ∀ r ∈ C, q = r := by
    intro q hq r hr
    by_contra hne
    have hzy : G.Adj z y := hyz.symm
    have hyx : G.Adj y x := hxy.symm
    have hzx : G.Adj z x := hxz.symm
    have hTzyx : triE G hzy hyx hzx ∈ M := by
      rwa [triE_congr G hxy hyz hxz hzy hyx hzx (by ext t; simp; tauto)]
    refine no_double_witness G hM hmin hzy hyx hzx hTzyx ?_ ?_ hne
    · rw [Finset.mem_inter] at hq ⊢
      exact ⟨hq.2, hq.1⟩
    · rw [Finset.mem_inter] at hr ⊢
      exact ⟨hr.2, hr.1⟩
  -- either at most one of the three sets is non-empty, or they are all the same singleton
  rcases A.eq_empty_or_nonempty with hAe | ⟨p, hp⟩
  · rcases B.eq_empty_or_nonempty with hBe | ⟨q, hq⟩
    · simp [hAe, hBe]; omega
    · rcases C.eq_empty_or_nonempty with hCe | ⟨r, hr⟩
      · simp [hAe, hCe]; omega
      · have h1 : B.card ≤ 1 := Finset.card_le_one.mpr (fun a ha b hb => by
          rw [hBC a ha r hr, hBC b hb r hr])
        have h2 : C.card ≤ 1 := Finset.card_le_one.mpr (fun a ha b hb => by
          rw [← hBC q hq a ha, ← hBC q hq b hb])
        simp only [hAe, Finset.card_empty]
        omega
  · rcases B.eq_empty_or_nonempty with hBe | ⟨q, hq⟩
    · rcases C.eq_empty_or_nonempty with hCe | ⟨r, hr⟩
      · simp [hBe, hCe]; omega
      · have h1 : A.card ≤ 1 := Finset.card_le_one.mpr (fun a ha b hb => by
          rw [hAC a ha r hr, hAC b hb r hr])
        have h2 : C.card ≤ 1 := Finset.card_le_one.mpr (fun a ha b hb => by
          rw [← hAC p hp a ha, ← hAC p hp b hb])
        simp only [hBe, Finset.card_empty]
        omega
    · have h1 : A.card ≤ 1 := Finset.card_le_one.mpr (fun a ha b hb => by
        rw [hAB a ha q hq, hAB b hb q hq])
      have h2 : B.card ≤ 1 := Finset.card_le_one.mpr (fun a ha b hb => by
        rw [← hAB p hp a ha, ← hAB p hp b hb])
      have h3 : C.card ≤ 1 := Finset.card_le_one.mpr (fun a ha b hb => by
        rw [← hAC p hp a ha, ← hAC p hp b hb])
      omega

end Nibble
