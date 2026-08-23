/-
# Nibble — the star-exchange engine

This file provides the *generic* bookkeeping for an exchange move on a triangle packing: remove a
set `R ⊆ M` of packing triangles, then insert new ones.  The two facts needed downstream are

* `Nibble.unDeg_sdiff` — deleting `R` raises the uncovered star at `u` by exactly the number of
  edges of `⋃ R` at `u`;
* `Nibble.unDeg_insert_add` — inserting a free triangle lowers the uncovered star at `u` by the
  number of its edges at `u`;
* `Nibble.pot_lt_of_exchange` — the potential `∑_v |uncoveredAt v|²` strictly drops if the move
  gains `2` at a vertex `v` with a large uncovered star, loses at most a bounded amount at a
  bounded set `S` of vertices with *small* uncovered stars, and changes nothing elsewhere.

Sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.DenseTriangleNibbleDegProof

open Finset SimpleGraph Hypergraph Nibble.YusterE

namespace Nibble

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ### Removing a set of hyperedges -/

/-- Deleting hyperedges from a matching leaves a matching. -/
theorem isMatching_sdiff (G : SimpleGraph V) [DecidableRel G.Adj]
    {M : Finset (Finset (EdgeV G))} (hM : IsMatching (triangleHypergraphSub G) M)
    (R : Finset (Finset (EdgeV G))) :
    IsMatching (triangleHypergraphSub G) (M \ R) :=
  ⟨(Finset.sdiff_subset).trans hM.subset, fun T hT T' hT' hne =>
    hM.disjoint T (Finset.mem_sdiff.mp hT).1 T' (Finset.mem_sdiff.mp hT').1 hne⟩

/-- The uncovered star of `M \ R` at `u` is that of `M` together with the edges of `⋃ R` at `u`. -/
theorem uncoveredAt_sdiff (G : SimpleGraph V) [DecidableRel G.Adj]
    {M : Finset (Finset (EdgeV G))} (hM : IsMatching (triangleHypergraphSub G) M)
    {R : Finset (Finset (EdgeV G))} (hR : R ⊆ M) (u : V) :
    uncoveredAt G (M \ R) u
      = uncoveredAt G M u ∪ (R.biUnion id).filter (fun E => u ∈ E.val) := by
  classical
  ext E
  simp only [mem_uncoveredAt, Finset.mem_union, Finset.mem_filter, Finset.mem_biUnion, UncE,
    Finset.mem_sdiff, id_eq]
  constructor
  · rintro ⟨hu, h⟩
    by_cases hcov : ∀ T ∈ M, E ∉ T
    · exact Or.inl ⟨hu, hcov⟩
    · push_neg at hcov
      obtain ⟨T, hTM, hET⟩ := hcov
      by_cases hTR : T ∈ R
      · exact Or.inr ⟨⟨T, hTR, hET⟩, hu⟩
      · exact absurd hET (h T ⟨hTM, hTR⟩)
  · rintro (⟨hu, h⟩ | ⟨⟨T, hTR, hET⟩, hu⟩)
    · exact ⟨hu, fun T hT => h T hT.1⟩
    · refine ⟨hu, fun T' hT' hET' => ?_⟩
      have hne : T' ≠ T := fun h => hT'.2 (h ▸ hTR)
      exact Finset.disjoint_left.mp (hM.disjoint T' hT'.1 T (hR hTR) hne) hET' hET

/-- The uncovered star size after deleting `R`. -/
theorem unDeg_sdiff (G : SimpleGraph V) [DecidableRel G.Adj]
    {M : Finset (Finset (EdgeV G))} (hM : IsMatching (triangleHypergraphSub G) M)
    {R : Finset (Finset (EdgeV G))} (hR : R ⊆ M) (u : V) :
    unDeg G (M \ R) u
      = unDeg G M u + ((R.biUnion id).filter (fun E => u ∈ E.val)).card := by
  classical
  have hdisj : Disjoint (uncoveredAt G M u) ((R.biUnion id).filter (fun E => u ∈ E.val)) := by
    rw [Finset.disjoint_left]
    intro E hE hE'
    rw [mem_uncoveredAt] at hE
    rw [Finset.mem_filter, Finset.mem_biUnion] at hE'
    obtain ⟨T, hTR, hET⟩ := hE'.1
    exact hE.2 T (hR hTR) hET
  rw [unDeg, uncoveredAt_sdiff G hM hR u, Finset.card_union_of_disjoint hdisj, unDeg]

/-- If no hyperedge of `R` has an edge at `u`, deleting `R` does not change the star at `u`. -/
theorem unDeg_sdiff_eq (G : SimpleGraph V) [DecidableRel G.Adj]
    {M : Finset (Finset (EdgeV G))} (hM : IsMatching (triangleHypergraphSub G) M)
    {R : Finset (Finset (EdgeV G))} (hR : R ⊆ M) {u : V}
    (hu : ∀ T ∈ R, ∀ E ∈ T, u ∉ E.val) :
    unDeg G (M \ R) u = unDeg G M u := by
  classical
  rw [unDeg_sdiff G hM hR u]
  have : ((R.biUnion id).filter (fun E => u ∈ E.val)) = ∅ := by
    refine Finset.filter_eq_empty_iff.mpr ?_
    intro E hE
    rw [Finset.mem_biUnion] at hE
    obtain ⟨T, hTR, hET⟩ := hE
    exact hu T hTR E hET
  rw [this, Finset.card_empty]
  omega

/-- Deleting `R` raises every uncovered star by at most `3|R|`. -/
theorem unDeg_sdiff_le (G : SimpleGraph V) [DecidableRel G.Adj]
    {M : Finset (Finset (EdgeV G))} (hM : IsMatching (triangleHypergraphSub G) M)
    {R : Finset (Finset (EdgeV G))} (hR : R ⊆ M) (u : V) :
    unDeg G (M \ R) u ≤ unDeg G M u + 3 * R.card := by
  classical
  rw [unDeg_sdiff G hM hR u]
  have h1 : ((R.biUnion id).filter (fun E => u ∈ E.val)).card ≤ (R.biUnion id).card :=
    Finset.card_filter_le _ _
  have h2 : (R.biUnion id).card ≤ ∑ T ∈ R, (id T).card := Finset.card_biUnion_le
  have h3 : ∑ T ∈ R, (id T).card = ∑ _T ∈ R, 3 := by
    refine Finset.sum_congr rfl (fun T hT => ?_)
    exact triangleHypergraphSub_uniform G T (hM.subset (hR hT))
  have h4 : ∑ _T ∈ R, 3 = 3 * R.card := by
    rw [Finset.sum_const, smul_eq_mul, mul_comm]
  omega

/-! ### Inserting a free hyperedge -/

/-- Inserting a hyperedge all of whose edges are uncovered lowers the star at `u` by the number of
its edges at `u`. -/
theorem unDeg_insert_add (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset (EdgeV G))) {P : Finset (EdgeV G)} (hfree : ∀ E ∈ P, UncE G M E) (u : V) :
    unDeg G (insert P M) u + (P.filter (fun E => u ∈ E.val)).card = unDeg G M u := by
  classical
  have hsub : P.filter (fun E => u ∈ E.val) ⊆ uncoveredAt G M u := by
    intro E hE
    rw [Finset.mem_filter] at hE
    exact (mem_uncoveredAt G).mpr ⟨hE.2, hfree E hE.1⟩
  have hinter : uncoveredAt G M u ∩ P = P.filter (fun E => u ∈ E.val) := by
    ext E
    simp only [Finset.mem_inter, Finset.mem_filter, mem_uncoveredAt]
    constructor
    · rintro ⟨⟨hu, -⟩, hP⟩; exact ⟨hP, hu⟩
    · rintro ⟨hP, hu⟩; exact ⟨⟨hu, hfree E hP⟩, hP⟩
  have hcard : (uncoveredAt G M u \ P).card + (uncoveredAt G M u ∩ P).card
      = (uncoveredAt G M u).card := Finset.card_sdiff_add_card_inter _ _
  rw [unDeg, uncoveredAt_insert, unDeg, ← hinter]
  omega

/-! ### The potential drop -/

/-- **The potential drops.**  If a move gains `2` at `v`, changes nothing outside `S ∪ {v}`, loses
at most `9` at each vertex of the small set `S`, and every vertex of `S` has an uncovered star at
most `d/64` where `d = |uncoveredAt v| ≥ 300`, then the potential strictly decreases. -/
theorem pot_lt_of_exchange (G : SimpleGraph V) [DecidableRel G.Adj]
    {M M' : Finset (Finset (EdgeV G))} {v : V} {S : Finset V}
    (hvS : v ∉ S) (hScard : S.card ≤ 13)
    (hv : unDeg G M' v + 2 = unDeg G M v)
    (hout : ∀ u : V, u ≠ v → u ∉ S → unDeg G M' u = unDeg G M u)
    (hin : ∀ u ∈ S, unDeg G M' u ≤ unDeg G M u + 9)
    (hcheap : ∀ u ∈ S, 64 * unDeg G M u ≤ unDeg G M v)
    (hbig : 4000 ≤ unDeg G M v) :
    uncoveredPot G M' < uncoveredPot G M := by
  classical
  set d := unDeg G M v with hd
  set T : Finset V := insert v S with hT
  have hsplit : ∀ f : V → ℕ, ∑ u : V, f u = ∑ u ∈ (Finset.univ \ T), f u + ∑ u ∈ T, f u :=
    fun f => (Finset.sum_sdiff (Finset.subset_univ _)).symm
  have heq : ∑ u ∈ (Finset.univ \ T), (unDeg G M' u) ^ 2
      = ∑ u ∈ (Finset.univ \ T), (unDeg G M u) ^ 2 := by
    refine Finset.sum_congr rfl (fun u hu => ?_)
    have hu' := Finset.mem_sdiff.mp hu
    rw [hT, Finset.mem_insert] at hu'
    push_neg at hu'
    rw [hout u hu'.2.1 hu'.2.2]
  -- the sum over `S`
  have hSsum : ∑ u ∈ S, (unDeg G M' u) ^ 2
      ≤ ∑ u ∈ S, ((unDeg G M u) ^ 2 + 18 * unDeg G M u + 81) := by
    refine Finset.sum_le_sum (fun u hu => ?_)
    have h := hin u hu
    nlinarith only [h]
  have hexp : ∑ u ∈ S, ((unDeg G M u) ^ 2 + 18 * unDeg G M u + 81)
      = ∑ u ∈ S, (unDeg G M u) ^ 2 + 18 * (∑ u ∈ S, unDeg G M u) + 81 * S.card := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const,
      smul_eq_mul, mul_comm S.card 81]
  have hcheapsum : 64 * (∑ u ∈ S, unDeg G M u) ≤ S.card * d := by
    calc 64 * (∑ u ∈ S, unDeg G M u) = ∑ u ∈ S, 64 * unDeg G M u := by rw [Finset.mul_sum]
      _ ≤ ∑ _u ∈ S, d := Finset.sum_le_sum (fun u hu => hcheap u hu)
      _ = S.card * d := by rw [Finset.sum_const, smul_eq_mul]
  have hTsum : ∀ f : V → ℕ, ∑ u ∈ T, f u = f v + ∑ u ∈ S, f u := by
    intro f
    rw [hT, Finset.sum_insert hvS]
  have hvsq : (unDeg G M' v) ^ 2 + 4 * d = d ^ 2 + 4 := by
    have h : unDeg G M' v + 2 = d := hv
    nlinarith only [h]
  -- assemble
  rw [uncoveredPot, uncoveredPot, hsplit (fun u => (unDeg G M' u) ^ 2),
    hsplit (fun u => (unDeg G M u) ^ 2), heq, hTsum, hTsum]
  have hkey : (unDeg G M' v) ^ 2 + ∑ u ∈ S, (unDeg G M' u) ^ 2
      < (unDeg G M v) ^ 2 + ∑ u ∈ S, (unDeg G M u) ^ 2 := by
    have h1 : ∑ u ∈ S, (unDeg G M' u) ^ 2
        ≤ ∑ u ∈ S, (unDeg G M u) ^ 2 + 18 * (∑ u ∈ S, unDeg G M u) + 81 * S.card :=
      le_trans hSsum (le_of_eq hexp)
    have h2 : 64 * (18 * (∑ u ∈ S, unDeg G M u)) ≤ 18 * (S.card * d) := by
      have := Nat.mul_le_mul_left 18 hcheapsum
      omega
    have h3 : 18 * (S.card * d) ≤ 18 * (13 * d) := by
      have : S.card * d ≤ 13 * d := Nat.mul_le_mul_right d hScard
      omega
    have h4 : 81 * S.card ≤ 81 * 13 := Nat.mul_le_mul_left 81 hScard
    -- linear arithmetic in the three sums and the two squares
    generalize hX : (unDeg G M' v) ^ 2 = X at hvsq ⊢
    generalize hY : (unDeg G M v) ^ 2 = Y at hvsq ⊢
    generalize hA : ∑ u ∈ S, (unDeg G M' u) ^ 2 = A at h1 ⊢
    generalize hB : ∑ u ∈ S, (unDeg G M u) ^ 2 = B at h1 ⊢
    generalize hC : ∑ u ∈ S, unDeg G M u = C at h1 h2
    omega
  omega

end Nibble
