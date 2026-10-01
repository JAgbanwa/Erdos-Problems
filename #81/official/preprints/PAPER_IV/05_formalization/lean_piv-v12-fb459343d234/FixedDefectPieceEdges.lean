import PieceEdgeStability
import ExplicitFixedStability

/-! Edge-weighted refinement of E32's partition-defect accounting. The counting
argument is adapted from E32.PieceIdentity without changing that audited file.
Zero-defect exceptional triangles are charged to their extra root edges. -/
namespace E32
open Finset PaperIV.FarRounding PaperIV.DefectComparatorGraph PaperIV.SplitEdgeCount
open scoped symmDiff
variable {V : Type*} [Fintype V] [DecidableEq V]

open Classical in
theorem noncanonical_edge_mass_le {G : SimpleGraph V} [DecidableRel G.Adj] {s : ℕ}
    {C D H : Finset V} (hR : IsDefectRoot G s C D H) (Q : CliquePartition G) :
    (∑ K ∈ Q.pieces.filter (fun K => ¬ IsCanonicalPiece C D H K), (K.card.choose 2 : ℤ)) ≤
      10*((Q.size : ℤ) - (rootBaseline C D H : ℤ) + 3 * (rootEdit G C D H : ℤ)) := by
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
  have hNcQ : Nc ⊆ Q.pieces := filter_subset _ _
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
  have hKcard (K : Finset V) : K.card = a K+b K := by
    have heq := hR.piece_eq K
    exact (congrArg card heq).trans (card_union_of_disjoint
      (Disjoint.mono inter_subset_right inter_subset_right hXH))
  have hN1edges : (∑ K ∈ N1, (K.card.choose 2 : ℤ)) ≤ 10*∑ K ∈ Q.pieces, d K := by
    calc
      _ ≤ ∑ K ∈ N1, 10*d K := by
        apply sum_le_sum
        intro K hK
        have hne := (mem_filter.mp hK).2
        have hidq : PaperIV.RootPartitionStability.numericDefect (a K) (b K) = (d K : ℚ) := by
          simp only [hd,pieceDefect,PaperIV.RootPartitionStability.numericDefect]
          push_cast
          rfl
        have he := PaperIV.SublinearResearch.piece_edges_le_ten_defect (a K) (b K)
          (by rw [hidq]; exact_mod_cast hne)
        rw [hidq,← hKcard K] at he
        exact_mod_cast he
      _ ≤ ∑ K ∈ Q.pieces, 10*d K :=
        sum_le_sum_of_subset_of_nonneg (subset_trans (filter_subset _ _) hNcQ)
          (fun K hK _ => mul_nonneg (by norm_num) (hd0 K hK))
      _ = _ := by rw [mul_sum]
  have hN0edges : (∑ K ∈ N0, (K.card.choose 2 : ℤ)) ≤ 3*(N0.card : ℤ) := by
    calc
      _ ≤ ∑ _K ∈ N0, (3 : ℤ) := by
        apply sum_le_sum
        intro K hK
        obtain ⟨hb1,ha12⟩ := pieceDefect_eq_zero (mem_filter.mp hK).2
        rw [hKcard K,hb1]
        rcases ha12 with ha1 | ha2
        · norm_num [ha1]
        · norm_num [ha2]
      _ = _ := by simp; ring
  have hedgeSplit : (∑ K ∈ Nc, (K.card.choose 2 : ℤ)) =
      (∑ K ∈ N1, (K.card.choose 2 : ℤ)) + ∑ K ∈ N0, (K.card.choose 2 : ℤ) := by
    simpa only [hN1,hN0,ne_eq,not_not] using
      (sum_filter_add_sum_filter_not Nc (fun K => d K ≠ 0) (fun K => (K.card.choose 2 : ℤ))).symm
  have hN0Z : (N0.card : ℤ) ≤ x := by exact_mod_cast hN0le
  have heditZ : (x : ℤ)+mH+A ≤ rootEdit G C D H := by exact_mod_cast hedit
  have hx0 : (0 : ℤ) ≤ x := Int.natCast_nonneg _
  have hA0 : (0 : ℤ) ≤ A := Int.natCast_nonneg _
  change (∑ K ∈ Nc, (K.card.choose 2 : ℤ)) ≤ _
  linarith

end E32

namespace PaperIV.SublinearResearch
open Finset PaperIV.FarRounding PaperIV.RootedSimplicialDefect PaperIV.DefectTargetArithmetic

noncomputable def defectNoncanonicalEdgeMass {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (C D H : Finset V) (Q : CliquePartition G) : ℕ := by
  classical
  exact ∑ K ∈ Q.pieces.filter (fun K => ¬ E32.IsCanonicalPiece C D H K), K.card.choose 2

theorem fixed_defect_partition_edge_stability (s n : ℕ)
    (hn : FixedExplicit.stabilityThreshold s ≤ n)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : RootedDefectAt G s)
    (δ : ℚ) (hδ0 : 0 ≤ δ) (hδ : δ ≤ FixedExplicit.stabilityGamma s*(n : ℚ)^2)
    (hlow : ∀ Q : CliquePartition G, Q.OrderAtMost 4 → (defectTarget s n : ℚ)-δ ≤ Q.size) :
    ∃ C D H : Finset (Fin n), E32.IsDefectRoot G s C D H ∧
      (E32.rootEdit G C D H : ℚ) ≤ FixedExplicit.stabilityConstant s*δ ∧
      ∀ (Q : CliquePartition G) (τ : ℚ), (Q.size : ℚ) ≤ defectTarget s n+τ →
        (defectNoncanonicalEdgeMass C D H Q : ℚ) ≤
          10*τ+10*(1+7*FixedExplicit.stabilityConstant s)*δ := by
  classical
  obtain ⟨C,D,H,hR,he,hlo,hhi⟩ :=
    FixedExplicit.fixed_defect_edit_and_size_explicit s n hn G hG δ hδ0 hδ hlow
  refine ⟨C,D,H,hR,he,?_⟩
  intro Q τ hQ
  have hb := E32.noncanonical_edge_mass_le hR Q
  have hbQ : (defectNoncanonicalEdgeMass C D H Q : ℚ) ≤
      10*((Q.size : ℚ)-E32.rootBaseline C D H+3*E32.rootEdit G C D H) := by
    unfold defectNoncanonicalEdgeMass
    push_cast
    exact_mod_cast hb
  nlinarith only [hbQ,hQ,he,hhi]

end PaperIV.SublinearResearch
