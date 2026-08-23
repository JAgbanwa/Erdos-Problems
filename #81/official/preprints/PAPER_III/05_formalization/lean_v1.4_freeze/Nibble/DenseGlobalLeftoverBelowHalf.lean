/-
# Nibble — a leftover constant strictly below the `1/2` wall

`Nibble.denseGlobalLeftoverConst_half` certifies the leftover constant `c` for every `c > 1/2`, by
summing the unconditional per-vertex bound `2|uncovered star| ≤ |V| + 4`.  This file certifies a
constant strictly below `1/2`, by a *global* double count that uses the new local move of
`Nibble.DoubleSwap`.

The count.  Fix a potential-minimal matching `M`, write `d_v` for the uncovered star size at `v`,
`A_v` for the uncovered neighbourhood, `Tot = ∑_v d_v`, `S = ∑_v d_v²`, `m = |M|` and `n = |V|`.

* Every `G`-edge inside `A_v` is covered (the leftover is triangle-free) and carries `v` as a
  *witness*.  Counting ordered adjacent pairs inside the uncovered stars,
  `starPairs = ∑_v #{(a,b) : a,b ∈ A_v, ab ∈ E(G)}`, the Dross density gives
  `10·starPairs + n·Tot ≥ 10·S` (`Nibble.starPairs_lower`).
* Re-summing the same count by pairs, `starPairs = ∑_{(a,b)} |A_a ∩ A_b|`
  (`Nibble.starPairs_eq`), and an uncovered pair has no common uncovered neighbour, so only covered
  edges contribute.  Each covered edge lies in exactly one packing triangle, and by
  `Nibble.witness_triple_le` the three edges of a packing triangle carry at most `D + 2` witnesses
  in total.  Hence `starPairs ≤ 2m(D + 2)` (`Nibble.starPairs_le`).
* The packing triangles are edge-disjoint and avoid the uncovered edges, so
  `6m + Tot ≤ n²` (`Nibble.six_card_add_uncoveredTot_le`), while `2D ≤ n + 4`
  (`Nibble.dense_uncoveredAt_le_half`) and `Tot² ≤ n·S` (Cauchy–Schwarz).

Together: `60·Tot² + 10n(n + 8)·Tot ≤ 10n³(n + 8) + 6n²·Tot`
(`Nibble.dense_uncoveredTot_master`), which forces `Tot ≤ c|V|²` for large `|V|` for every constant
`c` above the root `(-1 + √151)/30 ≈ 0.376268` of `30c² + 2c − 5`, in particular for `c = 377/1000`:

* `Nibble.denseGlobalLeftoverConst_377_over_1000` — `DenseGlobalLeftoverConst (377/1000)`;
* `Nibble.leftoverConst_below_half` — a concrete `c < 1/2` with `DenseGlobalLeftoverConst c`.

`Nibble.DenseGlobalLeftoverThird` sharpens this to `17/50 = 0.34`, by replacing the global maximum
`D` with the per-vertex capacity bound `2 t_v + d_v ≤ deg_G v` and the pair witness bound
`Nibble.witness_pair_bound`.

Sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.DoubleSwap
import Nibble.DenseGlobalLeftoverConst

open Finset SimpleGraph Hypergraph Nibble.YusterE

namespace Nibble

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ### The two counting functions -/

/-- The number of ordered adjacent pairs inside the uncovered stars, summed over all vertices. -/
noncomputable def starPairs (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset (EdgeV G))) : ℕ :=
  ∑ v : V, ∑ a ∈ unNbr G M v, (unNbr G M v ∩ G.neighborFinset a).card

/-- The number of common uncovered neighbours ("witnesses") of an ordered adjacent pair. -/
noncomputable def witCard (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset (EdgeV G))) (p : V × V) : ℕ :=
  if G.Adj p.1 p.2 then (unNbr G M p.1 ∩ unNbr G M p.2).card else 0

/-! ### The lower bound: dense uncovered stars span many edges -/

/-- At the Dross density, the uncovered star at `v` meets the neighbourhood of any vertex in almost
all of itself. -/
theorem unNbr_inter_neighbor_lower (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdense : 9 * Fintype.card V ≤ 10 * G.minDegree) (M : Finset (Finset (EdgeV G))) (v a : V) :
    10 * unDeg G M v ≤ 10 * (unNbr G M v ∩ G.neighborFinset a).card + Fintype.card V := by
  classical
  have hunion := Finset.card_inter_add_card_union (unNbr G M v) (G.neighborFinset a)
  have hun_le : (unNbr G M v ∪ G.neighborFinset a).card ≤ Fintype.card V := by
    rw [← Finset.card_univ]
    exact Finset.card_le_card (Finset.subset_univ _)
  have hdeg : 9 * Fintype.card V ≤ 10 * G.degree a :=
    le_trans hdense (Nat.mul_le_mul_left 10 (SimpleGraph.minDegree_le_degree G a))
  have hnb : (G.neighborFinset a).card = G.degree a := rfl
  have hA : (unNbr G M v).card = unDeg G M v := card_unNbr G M v
  omega

/-- **The lower bound.**  `10·starPairs + n·Tot ≥ 10·S`. -/
theorem starPairs_lower (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdense : 9 * Fintype.card V ≤ 10 * G.minDegree) (M : Finset (Finset (EdgeV G))) :
    10 * ∑ v : V, (unDeg G M v) ^ 2
      ≤ 10 * starPairs G M + Fintype.card V * uncoveredTot G M := by
  classical
  have hv : ∀ v : V, 10 * (unDeg G M v) ^ 2
      ≤ 10 * (∑ a ∈ unNbr G M v, (unNbr G M v ∩ G.neighborFinset a).card)
        + Fintype.card V * unDeg G M v := by
    intro v
    have h1 : ∑ _a ∈ unNbr G M v, (10 * unDeg G M v)
        ≤ ∑ a ∈ unNbr G M v, (10 * (unNbr G M v ∩ G.neighborFinset a).card + Fintype.card V) :=
      Finset.sum_le_sum (fun a _ => unNbr_inter_neighbor_lower G hdense M v a)
    rw [Finset.sum_const, card_unNbr, smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_const, card_unNbr, smul_eq_mul] at h1
    calc 10 * (unDeg G M v) ^ 2 = unDeg G M v * (10 * unDeg G M v) := by ring
      _ ≤ 10 * (∑ a ∈ unNbr G M v, (unNbr G M v ∩ G.neighborFinset a).card)
            + unDeg G M v * Fintype.card V := h1
      _ = 10 * (∑ a ∈ unNbr G M v, (unNbr G M v ∩ G.neighborFinset a).card)
            + Fintype.card V * unDeg G M v := by ring
  calc 10 * ∑ v : V, (unDeg G M v) ^ 2 = ∑ v : V, 10 * (unDeg G M v) ^ 2 := by
        rw [Finset.mul_sum]
    _ ≤ ∑ v : V, (10 * (∑ a ∈ unNbr G M v, (unNbr G M v ∩ G.neighborFinset a).card)
            + Fintype.card V * unDeg G M v) := Finset.sum_le_sum (fun v _ => hv v)
    _ = 10 * starPairs G M + Fintype.card V * uncoveredTot G M := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        rfl

/-! ### Re-summing by pairs -/

/-- **The double count.**  The ordered adjacent pairs inside uncovered stars, counted by pairs. -/
theorem starPairs_eq (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset (EdgeV G))) :
    starPairs G M = ∑ p : V × V, witCard G M p := by
  classical
  have hinner : ∀ v a : V, a ∈ unNbr G M v → (unNbr G M v ∩ G.neighborFinset a).card
      = ∑ b : V, (if a ∈ unNbr G M v ∧ b ∈ unNbr G M v ∧ G.Adj a b then 1 else 0) := by
    intro v a ha
    simp only [ha, true_and]
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const]
    simp only [smul_eq_mul, mul_one, mul_zero, add_zero]
    congr 1
    ext b
    simp [SimpleGraph.mem_neighborFinset]
  have houter : ∀ v : V, ∑ a ∈ unNbr G M v, (unNbr G M v ∩ G.neighborFinset a).card
      = ∑ a : V, ∑ b : V, (if a ∈ unNbr G M v ∧ b ∈ unNbr G M v ∧ G.Adj a b then 1 else 0) := by
    intro v
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun a => a ∈ unNbr G M v)]
    have h2 : ∑ a ∈ Finset.univ.filter (fun a => ¬ a ∈ unNbr G M v),
        ∑ b : V, (if a ∈ unNbr G M v ∧ b ∈ unNbr G M v ∧ G.Adj a b then 1 else 0) = 0 := by
      refine Finset.sum_eq_zero (fun a ha => ?_)
      have := (Finset.mem_filter.mp ha).2
      simp [this]
    rw [h2, add_zero]
    have h3 : Finset.univ.filter (fun a => a ∈ unNbr G M v) = unNbr G M v := by
      ext a; simp
    rw [h3]
    exact Finset.sum_congr rfl (fun a ha => hinner v a ha)
  rw [starPairs]
  simp_rw [houter]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  by_cases hab : G.Adj a b
  · have : ∀ v : V, (if a ∈ unNbr G M v ∧ b ∈ unNbr G M v ∧ G.Adj a b then 1 else 0)
        = (if v ∈ unNbr G M a ∩ unNbr G M b then 1 else 0) := by
      intro v
      by_cases h1 : v ∈ unNbr G M a ∩ unNbr G M b
      · rw [Finset.mem_inter] at h1
        rw [if_pos ⟨unNbr_symm G h1.1, unNbr_symm G h1.2, hab⟩, if_pos (Finset.mem_inter.mpr h1)]
      · rw [if_neg, if_neg h1]
        rintro ⟨h2, h3, -⟩
        exact h1 (Finset.mem_inter.mpr ⟨unNbr_symm G h2, unNbr_symm G h3⟩)
    simp_rw [this]
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, smul_eq_mul, mul_one, witCard,
      if_pos hab]
  · simp [witCard, hab]

/-! ### The upper bound: at most one edge of each packing triangle carries witnesses -/

/-- Every hyperedge of the triangle hypergraph is the triangle over three distinct vertices. -/
theorem exists_triE_of_mem (G : SimpleGraph V) [DecidableRel G.Adj] {T : Finset (EdgeV G)}
    (hT : T ∈ triangleHypergraphSub G) :
    ∃ (x y z : V) (hxy : G.Adj x y) (hyz : G.Adj y z) (hxz : G.Adj x z),
      T = triE G hxy hyz hxz := by
  classical
  obtain ⟨t, ht, rfl⟩ := (mem_triangleHypergraphSub_iff G).mp hT
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.mp ht.card_eq
  have hax : G.Adj x y := ht.isClique (by simp) (by simp) hxy
  have hay : G.Adj y z := ht.isClique (by simp) (by simp) hyz
  have haz : G.Adj x z := ht.isClique (by simp) (by simp) hxz
  exact ⟨x, y, z, hax, hay, haz, (triE_eq_subtype G hax hay haz).symm⟩

/-- A pair joined by an *uncovered* edge has no common uncovered neighbour. -/
theorem witCard_eq_zero_of_unc (G : SimpleGraph V) [DecidableRel G.Adj]
    {M : Finset (Finset (EdgeV G))} (hM : IsMatching (triangleHypergraphSub G) M)
    (hmin : ∀ M' : Finset (Finset (EdgeV G)), IsMatching (triangleHypergraphSub G) M' →
      uncoveredTot G M' ≤ uncoveredTot G M → uncoveredPot G M ≤ uncoveredPot G M')
    {a b : V} (hab : G.Adj a b) (hunc : UncE G M (edgeE G hab)) :
    witCard G M (a, b) = 0 := by
  classical
  rw [witCard, if_pos hab, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro v hv
  rw [Finset.mem_inter] at hv
  obtain ⟨hav, huav⟩ := (mem_unNbr G).mp hv.1
  obtain ⟨hbv, hubv⟩ := (mem_unNbr G).mp hv.2
  exact no_free_triangle G hM hmin hab hbv hav hunc hubv huav

/-- **The upper bound.**  `∑_p |witnesses of p| ≤ 2m(D + 2)`. -/
theorem starPairs_le (G : SimpleGraph V) [DecidableRel G.Adj]
    {M : Finset (Finset (EdgeV G))} (hM : IsMatching (triangleHypergraphSub G) M)
    (hmin : ∀ M' : Finset (Finset (EdgeV G)), IsMatching (triangleHypergraphSub G) M' →
      uncoveredTot G M' ≤ uncoveredTot G M → uncoveredPot G M ≤ uncoveredPot G M')
    {D : ℕ} (hD : ∀ u : V, unDeg G M u ≤ D) :
    ∑ p : V × V, witCard G M p ≤ 2 * M.card * (D + 2) := by
  classical
  -- a pair with a witness has a covered edge
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
  have hfib : ∀ T ∈ M, ∑ p ∈ Good.filter (fun p => φ p = T), witCard G M p ≤ 2 * (D + 2) := by
    intro T hT
    obtain ⟨x, y, z, hxy, hyz, hxz, rfl⟩ := exists_triE_of_mem G (hM.subset hT)
    have hsub : Good.filter (fun p => φ p = triE G hxy hyz hxz)
        ⊆ ({x, y, z} : Finset V) ×ˢ ({x, y, z} : Finset V) := by
      intro p hp
      rw [Finset.mem_filter] at hp
      obtain ⟨hpG, hpT⟩ := hp
      have hne := (Finset.mem_filter.mp hpG).2
      have hab : G.Adj p.1 p.2 := by
        by_contra h
        exact hne (by rw [witCard, if_neg h])
      have hmem : edgeE G hab ∈ triE G hxy hyz hxz := by
        have := (hφ p hne).2 hab
        rwa [hpT] at this
      rw [mem_triE] at hmem
      have hpair : ({p.1, p.2} : Finset V) = {x, y} ∨ ({p.1, p.2} : Finset V) = {y, z}
          ∨ ({p.1, p.2} : Finset V) = {x, z} := by
        rcases hmem with h | h | h
        · exact Or.inl ((edgeE_eq_iff G hab hxy).mp h)
        · exact Or.inr (Or.inl ((edgeE_eq_iff G hab hyz).mp h))
        · exact Or.inr (Or.inr ((edgeE_eq_iff G hab hxz).mp h))
      have h1' : p.1 ∈ ({x, y, z} : Finset V) ∧ p.2 ∈ ({x, y, z} : Finset V) := by
        rcases hpair with h | h | h <;>
        · constructor
          · have : p.1 ∈ ({p.1, p.2} : Finset V) := by simp
            rw [h] at this
            simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
            tauto
          · have : p.2 ∈ ({p.1, p.2} : Finset V) := by simp
            rw [h] at this
            simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
            tauto
      exact Finset.mem_product.mpr h1'
    have hbig : ∑ p ∈ Good.filter (fun p => φ p = triE G hxy hyz hxz), witCard G M p
        ≤ ∑ p ∈ ({x, y, z} : Finset V) ×ˢ ({x, y, z} : Finset V), witCard G M p :=
      Finset.sum_le_sum_of_subset hsub
    have hsymm : ∀ a b : V, witCard G M (a, b) = witCard G M (b, a) := by
      intro a b
      by_cases h : G.Adj a b
      · rw [witCard, witCard, if_pos h, if_pos h.symm, Finset.inter_comm]
      · rw [witCard, witCard, if_neg h, if_neg (fun h' => h h'.symm)]
    have hdiag : ∀ a : V, witCard G M (a, a) = 0 := by
      intro a
      rw [witCard, if_neg (SimpleGraph.irrefl G)]
    have hxyne : x ≠ y := hxy.ne
    have hyzne : y ≠ z := hyz.ne
    have hxzne : x ≠ z := hxz.ne
    have htriple : ∀ g : V → ℕ, ∑ t ∈ ({x, y, z} : Finset V), g t = g x + g y + g z := by
      intro g
      rw [Finset.sum_insert (by simp [hxyne, hxzne]), Finset.sum_insert (by simp [hyzne]),
        Finset.sum_singleton, add_assoc]
    have hprod : ∑ p ∈ ({x, y, z} : Finset V) ×ˢ ({x, y, z} : Finset V), witCard G M p
        = 2 * (witCard G M (x, y) + witCard G M (y, z) + witCard G M (x, z)) := by
      rw [Finset.sum_product]
      rw [htriple (fun a => ∑ b ∈ ({x, y, z} : Finset V), witCard G M (a, b))]
      rw [htriple (fun b => witCard G M (x, b)), htriple (fun b => witCard G M (y, b)),
        htriple (fun b => witCard G M (z, b))]
      rw [hdiag x, hdiag y, hdiag z, ← hsymm x y, ← hsymm x z, ← hsymm y z]
      ring
    have hwit : witCard G M (x, y) + witCard G M (y, z) + witCard G M (x, z) ≤ D + 2 := by
      rw [witCard, witCard, witCard, if_pos hxy, if_pos hyz, if_pos hxz]
      exact witness_triple_le G hM hmin hxy hyz hxz hT hD
    omega
  calc ∑ T ∈ M, ∑ p ∈ Good.filter (fun p => φ p = T), witCard G M p
      ≤ ∑ _T ∈ M, 2 * (D + 2) := Finset.sum_le_sum hfib
    _ = 2 * M.card * (D + 2) := by rw [Finset.sum_const, smul_eq_mul]; ring

/-! ### Counting the packing triangles -/

/-- Twice the number of uncovered edges is the number of uncovered incidences. -/
theorem two_mul_card_uncovered (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset (EdgeV G))) :
    2 * (uncovered G M).card = uncoveredTot G M := by
  classical
  have hcard : ∀ E : EdgeV G, (E.val).card = 2 := fun E =>
    (SimpleGraph.mem_cliqueFinset_iff.mp E.property).card_eq
  have hstar : ∀ v : V, uncoveredAt G M v
      = (uncovered G M).filter (fun E => v ∈ E.val) := by
    intro v
    ext E
    simp only [uncoveredAt, uncovered, Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  have h1 : uncoveredTot G M
      = ∑ v : V, ∑ E ∈ uncovered G M, (if v ∈ E.val then 1 else 0) := by
    rw [uncoveredTot]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    rw [unDeg, hstar v, Finset.card_filter]
  rw [h1, Finset.sum_comm]
  have h2 : ∀ E ∈ uncovered G M, ∑ v : V, (if v ∈ E.val then 1 else 0) = 2 := by
    intro E _
    rw [← Finset.card_filter]
    have : Finset.univ.filter (fun v => v ∈ E.val) = E.val := by ext v; simp
    rw [this, hcard E]
  rw [Finset.sum_congr rfl h2, Finset.sum_const, smul_eq_mul, mul_comm]

/-- **Counting the packing.**  Edge-disjoint triangles avoid the uncovered edges, so
`6m + Tot ≤ n²`. -/
theorem six_card_add_uncoveredTot_le (G : SimpleGraph V) [DecidableRel G.Adj]
    {M : Finset (Finset (EdgeV G))} (hM : IsMatching (triangleHypergraphSub G) M) :
    6 * M.card + uncoveredTot G M ≤ Fintype.card V * Fintype.card V := by
  classical
  -- the covered edges
  set Cov : Finset (EdgeV G) := M.biUnion (fun T => T) with hCov
  have hcardCov : Cov.card = 3 * M.card := by
    rw [hCov, Finset.card_biUnion (fun T hT T' hT' hne => hM.disjoint T hT T' hT' hne)]
    rw [Finset.sum_congr rfl (fun T hT => triangleHypergraphSub_uniform G T (hM.subset hT)),
      Finset.sum_const, smul_eq_mul, mul_comm]
  have hdisj : Disjoint Cov (uncovered G M) := by
    rw [Finset.disjoint_left]
    intro E hE hE'
    rw [hCov, Finset.mem_biUnion] at hE
    obtain ⟨T, hT, hmem⟩ := hE
    exact (Finset.mem_filter.mp hE').2 T hT hmem
  have hle : Cov.card + (uncovered G M).card ≤ Fintype.card (EdgeV G) := by
    rw [← Finset.card_union_of_disjoint hdisj, ← Finset.card_univ]
    exact Finset.card_le_card (Finset.subset_univ _)
  have hEdge : 2 * Fintype.card (EdgeV G) ≤ Fintype.card V * Fintype.card V := by
    have h1 : Fintype.card (EdgeV G) = (G.cliqueFinset 2).card := card_EdgeV G
    have h2 : G.cliqueFinset 2 ⊆ (Finset.univ : Finset V).powersetCard 2 := by
      intro s hs
      rw [Finset.mem_powersetCard]
      exact ⟨Finset.subset_univ _, (SimpleGraph.mem_cliqueFinset_iff.mp hs).card_eq⟩
    have h3 : (G.cliqueFinset 2).card ≤ (Fintype.card V).choose 2 := by
      have := Finset.card_le_card h2
      rwa [Finset.card_powersetCard, Finset.card_univ] at this
    have h4 : 2 * (Fintype.card V).choose 2 ≤ Fintype.card V * Fintype.card V := by
      rcases Nat.eq_zero_or_pos (Fintype.card V) with h | h
      · simp [h]
      · rw [Nat.choose_two_right]
        have : Fintype.card V * (Fintype.card V - 1) ≤ Fintype.card V * Fintype.card V :=
          Nat.mul_le_mul_left _ (by omega)
        omega
    omega
  have h2u := two_mul_card_uncovered G M
  omega

/-! ### The master inequality -/

/-- **The master inequality** at the Dross density: a potential-minimal matching satisfies
`60·Tot² + 10n(n+8)·Tot ≤ 10n³(n+8) + 6n²·Tot`. -/
theorem dense_uncoveredTot_master (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdense : 9 * Fintype.card V ≤ 10 * G.minDegree) :
    ∃ M : Finset (Finset (EdgeV G)), IsMatching (triangleHypergraphSub G) M ∧
      60 * (uncoveredTot G M) ^ 2
          + 10 * Fintype.card V * (Fintype.card V + 8) * uncoveredTot G M
        ≤ 10 * Fintype.card V ^ 3 * (Fintype.card V + 8)
          + 6 * Fintype.card V ^ 2 * uncoveredTot G M := by
  classical
  obtain ⟨M, hM, hmin⟩ := exists_min_pot G
  refine ⟨M, hM, ?_⟩
  set n := Fintype.card V with hn
  set Tot := uncoveredTot G M with hTot
  set S := ∑ v : V, (unDeg G M v) ^ 2 with hS
  set m := M.card with hm
  -- the maximal uncovered star
  obtain ⟨D, hD, hDle⟩ : ∃ D : ℕ, (∀ u : V, unDeg G M u ≤ D) ∧ 2 * D ≤ n + 4 := by
    rcases isEmpty_or_nonempty V with hV | hV
    · exact ⟨0, fun u => (hV.false u).elim, by omega⟩
    · obtain ⟨v₀, -, hmax⟩ :=
        Finset.exists_max_image (Finset.univ : Finset V) (unDeg G M) ⟨Classical.arbitrary V, by simp⟩
      refine ⟨unDeg G M v₀, fun u => hmax u (Finset.mem_univ u), ?_⟩
      by_contra hcon
      exact star_counting_contradiction G hdense hM hmin v₀ (by omega)
  -- the three counting inputs
  have hlow : 10 * S ≤ 10 * starPairs G M + n * Tot := starPairs_lower G hdense M
  have hup : starPairs G M ≤ 2 * m * (D + 2) := by
    rw [starPairs_eq G M]
    exact starPairs_le G hM hmin hD
  have hcount : 6 * m + Tot ≤ n * n := six_card_add_uncoveredTot_le G hM
  have hcs : Tot ^ 2 ≤ n * S := by
    have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset V))
      (f := fun v => ((unDeg G M v : ℤ)))
    have hcast : ((Tot : ℤ)) ^ 2 ≤ (n : ℤ) * (S : ℤ) := by
      simpa [hTot, hS, hn, uncoveredTot, Finset.card_univ] using this
    exact_mod_cast hcast
  -- assemble
  have h1 : (10 : ℤ) * S ≤ 10 * (starPairs G M) + n * Tot := by exact_mod_cast hlow
  have h2 : (starPairs G M : ℤ) ≤ 2 * m * (D + 2) := by exact_mod_cast hup
  have h3 : (6 : ℤ) * m + Tot ≤ n * n := by exact_mod_cast hcount
  have h4 : ((Tot : ℤ)) ^ 2 ≤ (n : ℤ) * S := by exact_mod_cast hcs
  have h5 : (2 : ℤ) * D ≤ n + 4 := by exact_mod_cast hDle
  have hm0 : (0 : ℤ) ≤ m := Int.natCast_nonneg _
  have hD0 : (0 : ℤ) ≤ D := Int.natCast_nonneg _
  have hn0 : (0 : ℤ) ≤ n := Int.natCast_nonneg _
  have hT0 : (0 : ℤ) ≤ Tot := Int.natCast_nonneg _
  have hgoal : (60 : ℤ) * (Tot : ℤ) ^ 2 + 10 * n * (n + 8) * Tot
      ≤ 10 * (n : ℤ) ^ 3 * (n + 8) + 6 * (n : ℤ) ^ 2 * Tot := by
    -- `6·starPairs ≤ (n² − Tot)(n + 8)`
    have hkey : (6 : ℤ) * starPairs G M ≤ ((n : ℤ) * n - Tot) * (n + 8) := by
      have hA : (12 : ℤ) * m * (D + 2) ≤ (6 * m) * (2 * D + 4) := by ring_nf; omega
      have hB : (6 : ℤ) * m * (2 * (D : ℤ) + 4) ≤ ((n : ℤ) * n - Tot) * (n + 8) := by
        have hmm : (6 : ℤ) * m ≤ (n : ℤ) * n - Tot := by linarith
        have hDD : (2 : ℤ) * D + 4 ≤ (n : ℤ) + 8 := by linarith
        have h6m : (0 : ℤ) ≤ 6 * (m : ℤ) := by linarith
        have hpos : (0 : ℤ) ≤ 2 * (D : ℤ) + 4 := by linarith
        nlinarith
      nlinarith [h2]
    nlinarith only [h1, h4, hkey, hn0, hT0]
  exact_mod_cast hgoal

/-! ### The leftover constant -/

/-- **A leftover constant strictly below the wall.**  At the Dross density, some triangle packing
leaves at most `(377/1000)|V|²` uncovered incidences.

The master inequality supports every constant above the root `(-1 + √151)/30 ≈ 0.376268` of
`30c² + 2c − 5`, so `377/1000` is essentially the sharpest constant *this* count delivers
(`Nibble.master_threshold_between`); `Nibble.denseGlobalLeftoverConst_17_over_50` improves it to
`0.34` with a sharper count. -/
theorem denseGlobalLeftoverConst_377_over_1000 :
    DenseGlobalLeftoverConst (377 / 1000) := by
  refine ⟨1500, ?_⟩
  intro V _ _ G _ hV hdense
  obtain ⟨M, hM, hmaster⟩ := dense_uncoveredTot_master G hdense
  refine ⟨M, hM, ?_⟩
  have hmasterR : 60 * (uncoveredTot G M : ℝ) ^ 2
        + 10 * (Fintype.card V : ℝ) * ((Fintype.card V : ℝ) + 8) * (uncoveredTot G M : ℝ)
      ≤ 10 * (Fintype.card V : ℝ) ^ 3 * ((Fintype.card V : ℝ) + 8)
        + 6 * (Fintype.card V : ℝ) ^ 2 * (uncoveredTot G M : ℝ) := by
    exact_mod_cast hmaster
  set n : ℝ := (Fintype.card V : ℝ) with hn
  set Tot : ℝ := (uncoveredTot G M : ℝ) with hTot
  have hn300 : (1500 : ℝ) ≤ n := by rw [hn]; exact_mod_cast hV
  have hT0 : 0 ≤ Tot := by positivity
  by_contra hcon
  push_neg at hcon
  nlinarith only [hcon, hmasterR, hn300, hT0, sq_nonneg (Tot - 377 / 1000 * n ^ 2), sq_nonneg n]

/-- **The `1/2` wall is not the truth**: a concrete leftover constant below `1/2`. -/
theorem leftoverConst_below_half : ∃ c : ℝ, c < 1 / 2 ∧ DenseGlobalLeftoverConst c :=
  ⟨377 / 1000, by norm_num, denseGlobalLeftoverConst_377_over_1000⟩

/-- **Where the count stalls.**  The threshold of the master inequality
`Nibble.dense_uncoveredTot_master` is the positive root of `30c² + 2c − 5`; it lies strictly between
`1/5` and the constant `377/1000` certified above.  So the present double count — even used with no
further loss — cannot reach the `1/5` needed by `Nibble.beats_half_of_leftoverConst`. -/
theorem master_threshold_between :
    1 / 5 < (-1 + Real.sqrt 151) / 30 ∧ (-1 + Real.sqrt 151) / 30 < 377 / 1000 := by
  have hsq : Real.sqrt 151 ^ 2 = 151 := Real.sq_sqrt (by norm_num)
  have hnn : 0 ≤ Real.sqrt 151 := Real.sqrt_nonneg _
  constructor
  · nlinarith
  · nlinarith

end Nibble
