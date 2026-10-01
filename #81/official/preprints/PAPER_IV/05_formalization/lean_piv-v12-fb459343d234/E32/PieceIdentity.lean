import E32.Transfer

/-!
# E32 — the piece identity relative to a fixed root (analogue of (6.7a)–(6.7b))

Fix a root `(C, D, H)` of `G` (`IsDefectRoot`), write `X = C ∪ D`, and for a piece `K` put
`a = |K ∩ X|`, `b = |K ∩ H|`. The piece defect is

`d(K) = 1 + C(a,2) + 3·C(b,2) − a·b = ((a−b)(a−b−1))/2 + (b−1)² ≥ 0`,

and `d(K) = 0` exactly for `b = 1`, `a ∈ {1,2}`. Summing over any clique partition `Q` of `G`
(no restriction on piece order):

`∑ d(K) = |Q| − B + x + 3·m_H + A`,

where `B = rootBaseline`, `x` = edges of `G` inside `X` not inside `C`, `m_H = e(G[H])`, and `A` =
missing `X`–`H` links. Each of `x, m_H, A` is part of the edit distance to `defSplitGraph C D H`.
A zero-defect piece that is not canonical is a triangle using one of the `x` extra edges, so

`#noncanonical(Q) ≤ |Q| − B + 3·rootEdit`.
-/

namespace E32

open Finset PaperIV.FarRounding PaperIV.DefectComparatorGraph PaperIV.SplitEdgeCount
open scoped symmDiff

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The piece defect, as an integer. -/
def pieceDefect (a b : ℕ) : ℤ := 1 + (a.choose 2 : ℤ) + 3 * (b.choose 2 : ℤ) - (a : ℤ) * b

theorem two_mul_choose_two_int (a : ℕ) : 2 * (a.choose 2 : ℤ) = (a : ℤ) * ((a : ℤ) - 1) := by
  have h := PaperIV.SplitUniformIncidence.mul_pred_eq_two_mul_choose_two a
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp
  · have : ((a - 1 : ℕ) : ℤ) = (a : ℤ) - 1 := by push_cast [Nat.cast_sub ha]; ring
    have h' : ((a * (a - 1) : ℕ) : ℤ) = ((2 * a.choose 2 : ℕ) : ℤ) := by rw [h]
    push_cast [Nat.cast_sub ha] at h'
    linarith

theorem pieceDefect_eq (a b : ℕ) :
    2 * pieceDefect a b = ((a : ℤ) - b) * ((a : ℤ) - b - 1) + 2 * ((b : ℤ) - 1) ^ 2 := by
  unfold pieceDefect
  have ha := two_mul_choose_two_int a
  have hb := two_mul_choose_two_int b
  nlinarith

theorem pieceDefect_nonneg (a b : ℕ) : 0 ≤ pieceDefect a b := by
  have h := pieceDefect_eq a b
  have h1 : 0 ≤ ((a : ℤ) - b) * ((a : ℤ) - b - 1) := by
    rcases le_or_gt ((a : ℤ) - b) 0 with h' | h'
    · nlinarith
    · nlinarith
  nlinarith [sq_nonneg ((b : ℤ) - 1)]

theorem pieceDefect_eq_zero {a b : ℕ} (h : pieceDefect a b = 0) : b = 1 ∧ (a = 1 ∨ a = 2) := by
  have h2 := pieceDefect_eq a b
  rw [h] at h2
  have h1 : 0 ≤ ((a : ℤ) - b) * ((a : ℤ) - b - 1) := by
    rcases le_or_gt ((a : ℤ) - b) 0 with h' | h'
    · nlinarith
    · nlinarith
  have hsq : ((b : ℤ) - 1) ^ 2 = 0 := by nlinarith [sq_nonneg ((b : ℤ) - 1)]
  have hb : (b : ℤ) = 1 := by nlinarith [pow_eq_zero_iff (n := 2) (a := (b : ℤ) - 1) two_ne_zero]
  have hb' : b = 1 := by exact_mod_cast hb
  refine ⟨hb', ?_⟩
  subst hb'
  have hprod : ((a : ℤ) - 1) * ((a : ℤ) - 1 - 1) = 0 := by push_cast at h2; nlinarith
  rcases mul_eq_zero.1 hprod with h' | h'
  · left; omega
  · right; omega

omit [Fintype V] in
theorem pairs_inter_pairs (K X : Finset V) : pairs K ∩ pairs X = pairs (K ∩ X) := by
  ext e
  induction e using Sym2.ind with
  | _ a b => simp only [mem_inter, mk_mem_pairs]; tauto

omit [Fintype V] in
theorem card_pairs (K : Finset V) : (pairs K).card = K.card.choose 2 :=
  PaperIV.Model.card_pieceEdges K

omit [Fintype V] in
theorem pairs_inter_cross {X H : Finset V} (hXH : Disjoint X H) (K : Finset V) :
    pairs K ∩ crossEdges X H = crossEdges (K ∩ X) (K ∩ H) := by
  ext e
  induction e using Sym2.ind with
  | _ a b =>
    simp only [mem_inter, mk_mem_pairs, mem_crossEdges, Sym2.eq_iff]
    constructor
    · rintro ⟨⟨ha, hb, hab⟩, x, hx, z, hz, h⟩
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨a, ⟨ha, hx⟩, b, ⟨hb, hz⟩, Or.inl ⟨rfl, rfl⟩⟩
      · exact ⟨b, ⟨hb, hx⟩, a, ⟨ha, hz⟩, Or.inr ⟨rfl, rfl⟩⟩
    · rintro ⟨x, ⟨hxK, hx⟩, z, ⟨hzK, hz⟩, h⟩
      have hxz : x ≠ z := fun hxz => disjoint_left.1 hXH hx (hxz ▸ hz)
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨⟨hxK, hzK, hxz⟩, a, hx, b, hz, Or.inl ⟨rfl, rfl⟩⟩
      · exact ⟨⟨hzK, hxK, hxz.symm⟩, b, hx, a, hz, Or.inr ⟨rfl, rfl⟩⟩

/-- Summing an edge statistic over the pieces of a partition. -/
theorem sum_card_pairs_inter (G : SimpleGraph V) [DecidableRel G.Adj] (Q : CliquePartition G)
    (S : Finset (Sym2 V)) :
    ∑ K ∈ Q.pieces, (pairs K ∩ S).card = (G.edgeFinset ∩ S).card := by
  have hU : G.edgeFinset ∩ S = Q.pieces.biUnion (fun K => pairs K ∩ S) := by
    rw [← Q.covers, biUnion_inter]
  rw [hU, card_biUnion]
  intro K hK L hL hKL
  exact Disjoint.mono inter_subset_left inter_subset_left (Q.edgeDisjoint K hK L hL hKL)

section Root

variable {G : SimpleGraph V} [DecidableRel G.Adj] {s : ℕ} {C D H : Finset V}

omit [Fintype V] [DecidableRel G.Adj] in
theorem IsDefectRoot.disjXH (hR : IsDefectRoot G s C D H) : Disjoint (C ∪ D) H :=
  disjoint_union_left.2 ⟨hR.disjCH, hR.disjDH⟩

omit [Fintype V] [DecidableRel G.Adj] in
theorem IsDefectRoot.piece_eq (hR : IsDefectRoot G s C D H) (K : Finset V) :
    K = (K ∩ (C ∪ D)) ∪ (K ∩ H) := by
  ext z
  simp only [mem_union, mem_inter]
  constructor
  · intro hz
    rcases hR.cover z with h | h | h
    · exact Or.inl ⟨hz, Or.inl h⟩
    · exact Or.inl ⟨hz, Or.inr h⟩
    · exact Or.inr ⟨hz, h⟩
  · rintro (⟨hz, _⟩ | ⟨hz, _⟩) <;> exact hz

/-- The three edit families: extra edges inside the root, edges inside the exterior, and missing
root–exterior links. Their sizes add up to at most the edit distance. -/
theorem IsDefectRoot.edit_ge (hR : IsDefectRoot G s C D H) :
    ((G.edgeFinset ∩ pairs (C ∪ D)) \ pairs C).card + (G.edgeFinset ∩ pairs H).card +
      (crossEdges (C ∪ D) H \ G.edgeFinset).card ≤ rootEdit G C D H := by
  classical
  have hXH := hR.disjXH
  set E := defSplitGraph C D H
  have h1 : (G.edgeFinset ∩ pairs (C ∪ D)) \ pairs C ⊆ G.edgeFinset \ E.edgeFinset := by
    intro e he
    induction e using Sym2.ind with
    | _ a b =>
      simp only [mem_sdiff, mem_inter, mk_mem_pairs] at he
      obtain ⟨⟨hG, ha, hb, hab⟩, hnC⟩ := he
      refine mem_sdiff.2 ⟨hG, ?_⟩
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      rintro ⟨-, hcase | ⟨-, hbH⟩ | ⟨haH, -⟩⟩
      · exact hnC ⟨hcase.1, hcase.2, hab⟩
      · exact disjoint_left.1 hXH hb hbH
      · exact disjoint_left.1 hXH ha haH
  have h2 : G.edgeFinset ∩ pairs H ⊆ G.edgeFinset \ E.edgeFinset := by
    intro e he
    induction e using Sym2.ind with
    | _ a b =>
      simp only [mem_inter, mk_mem_pairs] at he
      obtain ⟨hG, ha, hb, -⟩ := he
      refine mem_sdiff.2 ⟨hG, ?_⟩
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      exact not_adj_of_mem_hosts hXH ha hb
  have h3 : crossEdges (C ∪ D) H \ G.edgeFinset ⊆ E.edgeFinset \ G.edgeFinset := by
    intro e he
    obtain ⟨he1, he2⟩ := mem_sdiff.1 he
    have := crossEdges_subset_graphEdges_def hXH he1
    rw [PaperIV.Model.mem_graphEdges] at this
    exact mem_sdiff.2 ⟨SimpleGraph.mem_edgeFinset.2 this, he2⟩
  have hd12 : Disjoint ((G.edgeFinset ∩ pairs (C ∪ D)) \ pairs C) (G.edgeFinset ∩ pairs H) := by
    rw [disjoint_left]
    intro e he he'
    induction e using Sym2.ind with
    | _ a b =>
      simp only [mem_sdiff, mem_inter, mk_mem_pairs] at he he'
      exact disjoint_left.1 hXH he.1.2.1 he'.2.1
  have hsub12 := union_subset h1 h2
  have hc12 := card_union_of_disjoint hd12
  have hdisjSD : Disjoint (G.edgeFinset \ E.edgeFinset) (E.edgeFinset \ G.edgeFinset) :=
    disjoint_sdiff_sdiff
  have hSD : (G.edgeFinset ∆ E.edgeFinset) = (G.edgeFinset \ E.edgeFinset) ∪
      (E.edgeFinset \ G.edgeFinset) := rfl
  have hA := card_le_card hsub12
  have hB := card_le_card h3
  have hC := card_union_of_disjoint hdisjSD
  unfold rootEdit PaperIV.EditMetric.editDist
  change _ ≤ (G.edgeFinset ∆ E.edgeFinset).card
  rw [hSD]
  omega

end Root

open Classical in
/-- **Piece count relative to the root (analogue of (6.7b)).** For any clique partition `Q` of
`G`, without restriction on the order of its pieces, the number of pieces that are not canonical
for `E_s` is at most `|Q| − rootBaseline + 3·rootEdit`. -/
theorem noncanonical_card_le {G : SimpleGraph V} [DecidableRel G.Adj] {s : ℕ}
    {C D H : Finset V} (hR : IsDefectRoot G s C D H) (Q : CliquePartition G) :
    ((Q.pieces.filter fun K => ¬ IsCanonicalPiece C D H K).card : ℤ) ≤
      (Q.size : ℤ) - (rootBaseline C D H : ℤ) + 3 * (rootEdit G C D H : ℤ) := by
  set X := C ∪ D with hX
  have hXH : Disjoint X H := hR.disjXH
  set a : Finset V → ℕ := fun K => (K ∩ X).card with ha
  set b : Finset V → ℕ := fun K => (K ∩ H).card with hb
  set d : Finset V → ℤ := fun K => pieceDefect (a K) (b K) with hd
  set x := ((G.edgeFinset ∩ pairs X) \ pairs C).card with hx
  set mH := (G.edgeFinset ∩ pairs H).card with hmH
  set A := (crossEdges X H \ G.edgeFinset).card with hA
  -- the three sums
  have sa : ∑ K ∈ Q.pieces, (a K).choose 2 = (G.edgeFinset ∩ pairs X).card := by
    rw [← sum_card_pairs_inter G Q]
    refine sum_congr rfl fun K _ => ?_
    rw [pairs_inter_pairs, card_pairs]
  have sb : ∑ K ∈ Q.pieces, (b K).choose 2 = mH := by
    rw [hmH, ← sum_card_pairs_inter G Q]
    refine sum_congr rfl fun K _ => ?_
    rw [pairs_inter_pairs, card_pairs]
  have sab : ∑ K ∈ Q.pieces, a K * b K = (G.edgeFinset ∩ crossEdges X H).card := by
    rw [← sum_card_pairs_inter G Q]
    refine sum_congr rfl fun K _ => ?_
    rw [pairs_inter_cross hXH, card_crossEdges (disjoint_of_subset_left inter_subset_right
      (disjoint_of_subset_right inter_subset_right hXH))]
  -- inside the root
  have hCsub : pairs C ⊆ G.edgeFinset ∩ pairs X := by
    intro e he
    induction e using Sym2.ind with
    | _ u w =>
      rw [mk_mem_pairs] at he
      refine mem_inter.2 ⟨?_, mk_mem_pairs.2 ⟨mem_union_left _ he.1, mem_union_left _ he.2.1,
        he.2.2⟩⟩
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      exact hR.clique he.1 he.2.1 he.2.2
  have hin : (G.edgeFinset ∩ pairs X).card = C.card.choose 2 + x := by
    rw [hx, card_sdiff_of_subset hCsub, card_pairs]
    have := card_le_card hCsub
    rw [card_pairs] at this
    omega
  -- across the cut
  have hcross : (G.edgeFinset ∩ crossEdges X H).card + A = X.card * H.card := by
    rw [hA, ← card_crossEdges hXH, inter_comm]
    exact card_inter_add_card_sdiff _ _
  have hXc : X.card = C.card + s := by rw [hX, card_union_of_disjoint hR.disjCD, hR.card_def]
  -- the sum of the piece defects
  have hsum : ∑ K ∈ Q.pieces, d K =
      (Q.size : ℤ) - (rootBaseline C D H : ℤ) + x + 3 * mH + A := by
    have hB : (rootBaseline C D H : ℤ) = ((C.card + s) * H.card : ℕ) - (C.card.choose 2 : ℕ) := by
      unfold rootBaseline
      rw [hR.card_def]
      have := choose_two_le_mul hR.core_le_hosts
      have h2 : C.card * H.card ≤ (C.card + s) * H.card := Nat.mul_le_mul_right _ (by omega)
      push_cast [Nat.cast_sub (le_trans this h2)]
      ring
    simp only [hd, pieceDefect, sum_add_distrib, sum_sub_distrib, sum_const, ← mul_sum]
    have sa' : ∑ K ∈ Q.pieces, ((a K).choose 2 : ℤ) = ((G.edgeFinset ∩ pairs X).card : ℤ) := by
      exact_mod_cast sa
    have sb' : ∑ K ∈ Q.pieces, ((b K).choose 2 : ℤ) = (mH : ℤ) := by exact_mod_cast sb
    have sab' : ∑ K ∈ Q.pieces, ((a K : ℤ) * (b K : ℤ)) =
        ((G.edgeFinset ∩ crossEdges X H).card : ℤ) := by exact_mod_cast sab
    rw [sa', sb', sab', hB]
    have hin' : ((G.edgeFinset ∩ pairs X).card : ℤ) = (C.card.choose 2 : ℕ) + x := by
      exact_mod_cast hin
    have hcross' : ((G.edgeFinset ∩ crossEdges X H).card : ℤ) + A = (X.card * H.card : ℕ) := by
      exact_mod_cast hcross
    rw [hXc] at hcross'
    simp only [CliquePartition.size, nsmul_eq_mul, mul_one]
    push_cast at hcross' ⊢
    linarith
  have hd0 : ∀ K ∈ Q.pieces, 0 ≤ d K := fun K _ => pieceDefect_nonneg _ _
  -- split the noncanonical pieces
  set Nc := Q.pieces.filter fun K => ¬ IsCanonicalPiece C D H K with hNc
  set N1 := Nc.filter fun K => d K ≠ 0 with hN1
  set N0 := Nc.filter fun K => d K = 0 with hN0
  have hsplit : N1.card + N0.card = Nc.card := by
    rw [hN1, hN0, add_comm]
    exact card_filter_add_card_filter_not _
  have hNcQ : Nc ⊆ Q.pieces := filter_subset _ _
  have hN1le : (N1.card : ℤ) ≤ ∑ K ∈ Q.pieces, d K := by
    calc (N1.card : ℤ) = ∑ _K ∈ N1, (1 : ℤ) := by simp
      _ ≤ ∑ K ∈ N1, d K := by
          apply sum_le_sum
          intro K hK
          obtain ⟨hKc, hne⟩ := mem_filter.1 hK
          have := hd0 K (hNcQ hKc)
          omega
      _ ≤ ∑ K ∈ Q.pieces, d K := by
          apply sum_le_sum_of_subset_of_nonneg (subset_trans (filter_subset _ _) hNcQ)
          intro K hK _; exact hd0 K hK
  -- zero-defect noncanonical pieces own an extra root edge
  set Ex := (G.edgeFinset ∩ pairs X) \ pairs C with hEx
  have hown : ∀ K ∈ N0, 1 ≤ (pairs K ∩ Ex).card := by
    intro K hK
    obtain ⟨hKc, hK0⟩ := mem_filter.1 hK
    obtain ⟨hKQ, hncan⟩ := mem_filter.1 hKc
    obtain ⟨hb1, ha12⟩ := pieceDefect_eq_zero hK0
    obtain ⟨h, hh⟩ := card_eq_one.1 hb1
    have hKeq := hR.piece_eq K
    have hhH : h ∈ H := (mem_inter.1 (hh ▸ mem_singleton_self h)).2
    rcases ha12 with ha1 | ha2
    · obtain ⟨u, hu⟩ := card_eq_one.1 ha1
      have huX : u ∈ X := (mem_inter.1 (hu ▸ mem_singleton_self u)).2
      exfalso
      apply hncan
      refine Or.inl ⟨u, huX, h, hhH, fun heq => disjoint_left.1 hXH huX (heq ▸ hhH), ?_⟩
      change K = (K ∩ X) ∪ (K ∩ H) at hKeq
      rw [hKeq, hu, hh]; rfl
    · obtain ⟨u, w, huw, huw'⟩ := card_eq_two.1 ha2
      have huK : u ∈ K ∩ X := huw' ▸ mem_insert_self u {w}
      have hwK : w ∈ K ∩ X := huw' ▸ mem_insert_of_mem (mem_singleton_self w)
      by_cases hCC : u ∈ C ∧ w ∈ C
      · exfalso
        apply hncan
        refine Or.inr ⟨u, hCC.1, w, hCC.2, h, hhH, huw, ?_⟩
        change K = (K ∩ X) ∪ (K ∩ H) at hKeq
        rw [hKeq, huw', hh]; ext z; simp only [mem_union, mem_insert, mem_singleton]; tauto
      · rw [Nat.one_le_iff_ne_zero, Ne, card_eq_zero, ← not_nonempty_iff_eq_empty, not_not]
        refine ⟨s(u, w), mem_inter.2 ⟨mk_mem_pairs.2 ⟨(mem_inter.1 huK).1, (mem_inter.1 hwK).1,
          huw⟩, mem_sdiff.2 ⟨mem_inter.2 ⟨?_, mk_mem_pairs.2 ⟨(mem_inter.1 huK).2,
          (mem_inter.1 hwK).2, huw⟩⟩, fun hp => hCC ?_⟩⟩⟩
        · rw [← Q.covers, mem_biUnion]
          exact ⟨K, hKQ, mk_mem_pairs.2 ⟨(mem_inter.1 huK).1, (mem_inter.1 hwK).1, huw⟩⟩
        · rw [mk_mem_pairs] at hp; exact ⟨hp.1, hp.2.1⟩
  have hN0le : N0.card ≤ x := by
    have hdisj : ∀ K ∈ N0, ∀ L ∈ N0, K ≠ L → Disjoint (pairs K ∩ Ex) (pairs L ∩ Ex) := by
      intro K hK L hL hKL
      exact Disjoint.mono inter_subset_left inter_subset_left
        (Q.edgeDisjoint K (hNcQ (mem_filter.1 hK).1) L (hNcQ (mem_filter.1 hL).1) hKL)
    have hU : N0.biUnion (fun K => pairs K ∩ Ex) ⊆ Ex := biUnion_subset.2 fun _ _ =>
      inter_subset_right
    calc N0.card = ∑ _K ∈ N0, 1 := by rw [sum_const, smul_eq_mul, mul_one]
      _ ≤ ∑ K ∈ N0, (pairs K ∩ Ex).card := sum_le_sum hown
      _ = (N0.biUnion (fun K => pairs K ∩ Ex)).card := (card_biUnion hdisj).symm
      _ ≤ Ex.card := card_le_card hU
  have hedit := hR.edit_ge
  change x + mH + A ≤ rootEdit G C D H at hedit
  have hsplitZ : (Nc.card : ℤ) = N1.card + N0.card := by exact_mod_cast hsplit.symm
  have hN0Z : (N0.card : ℤ) ≤ x := by exact_mod_cast hN0le
  have heditZ : (x : ℤ) + mH + A ≤ rootEdit G C D H := by exact_mod_cast hedit
  change (Nc.card : ℤ) ≤ _
  linarith

end E32
