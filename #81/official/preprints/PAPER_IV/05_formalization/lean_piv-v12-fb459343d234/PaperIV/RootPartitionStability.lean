import PaperIV.IntegralStability
import PaperIV.SplitCompleteDefect
import PaperIV.RootEdgeSplit

/-!
# Stability of clique partitions relative to a clique root

This module extends the complete-split defect identity to an arbitrary finite
graph equipped with a clique root.  The identity is purely combinatorial and
applies to clique partitions with pieces of unrestricted order.
-/

namespace PaperIV.RootPartitionStability

open Finset
open PaperIV.FarRounding PaperIV.Model PaperIV.RootVocab

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The numerical defect of a piece having `a` vertices in the root and `b`
vertices outside it. -/
def numericDefect (a b : ℕ) : ℚ :=
  1 + (a.choose 2 : ℚ) + 3 * (b.choose 2 : ℚ) - (a : ℚ) * b

/-- The defect is the sum of two visibly nonnegative terms. -/
theorem numericDefect_closed (a b : ℕ) :
    numericDefect a b =
      (((a : ℚ) - b) * ((a : ℚ) - b - 1)) / 2 + ((b : ℚ) - 1) ^ 2 := by
  simp only [numericDefect, Nat.cast_choose_two]
  ring

theorem numericDefect_nonneg (a b : ℕ) : 0 ≤ numericDefect a b := by
  rw [numericDefect_closed]
  have hz : 0 ≤ ((a : ℚ) - b) * ((a : ℚ) - b - 1) := by
    by_cases h : a ≤ b
    · have hq : (a : ℚ) ≤ b := by exact_mod_cast h
      nlinarith
    · have hab' : b < a := Nat.lt_of_not_ge h
      have hq : (b : ℚ) + 1 ≤ a := by
        exact_mod_cast (Nat.add_one_le_iff.mpr hab')
      nlinarith
  nlinarith [sq_nonneg ((b : ℚ) - 1)]

/-- Zero defect characterizes the two canonical piece profiles. -/
theorem numericDefect_eq_zero_iff (a b : ℕ) :
    numericDefect a b = 0 ↔ b = 1 ∧ (a = 1 ∨ a = 2) := by
  rw [numericDefect_closed]
  constructor
  · intro h
    have hz : 0 ≤ ((a : ℚ) - b) * ((a : ℚ) - b - 1) := by
      by_cases hab : a ≤ b
      · have hq : (a : ℚ) ≤ b := by exact_mod_cast hab
        nlinarith
      · have hq : (b : ℚ) + 1 ≤ a := by
          have hab' : b < a := Nat.lt_of_not_ge hab
          exact_mod_cast (Nat.add_one_le_iff.mpr hab')
        nlinarith
    have hbSq : ((b : ℚ) - 1) ^ 2 = 0 := by
      nlinarith [sq_nonneg ((b : ℚ) - 1)]
    have hbQ : (b : ℚ) = 1 := by
      have := sq_eq_zero_iff.mp hbSq
      linarith
    have hb : b = 1 := by exact_mod_cast hbQ
    subst b
    have hprod : ((a : ℚ) - 1) * ((a : ℚ) - 2) = 0 := by
      nlinarith
    constructor
    · rfl
    · rcases mul_eq_zero.mp hprod with h1 | h2
      · left
        exact_mod_cast (sub_eq_zero.mp h1)
      · right
        have : (a : ℚ) = 2 := by linarith
        exact_mod_cast this
  · rintro ⟨rfl, rfl | rfl⟩ <;> norm_num [numericDefect]

/-- Defect of a literal piece relative to a distinguished root. -/
def rootPieceDefect (R K : Finset V) : ℚ :=
  numericDefect (K ∩ R).card (K ∩ outsideVertices R).card

theorem rootPieceDefect_nonneg (R K : Finset V) : 0 ≤ rootPieceDefect R K :=
  numericDefect_nonneg _ _

/-- A piece is canonical relative to `R` when it is a root--outside edge or a
triangle with two root vertices and one outside vertex. -/
def IsCanonicalAt (R K : Finset V) : Prop :=
  (K ∩ outsideVertices R).card = 1 ∧
    ((K ∩ R).card = 1 ∨ (K ∩ R).card = 2)

theorem rootPieceDefect_eq_zero_iff (R K : Finset V) :
    rootPieceDefect R K = 0 ↔ IsCanonicalAt R K :=
  numericDefect_eq_zero_iff _ _

private theorem filter_pairs_root_eq (R K : Finset V)
    (hK : G.IsClique (K : Set V)) :
    (pairs K).filter (fun e => e ∈ rootEdges G R) = pairs (K ∩ R) := by
  ext e
  induction e using Sym2.ind with
  | _ x y =>
      simp only [Finset.mem_filter, mk_mem_pairs, rootEdges,
        SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
        Sym2.toFinset_mk_eq, Finset.insert_subset_iff, Finset.singleton_subset_iff,
        Finset.mem_inter]
      constructor
      · rintro ⟨⟨hxK, hyK, hxy⟩, -, hxR, hyR⟩
        exact ⟨⟨hxK, hxR⟩, ⟨hyK, hyR⟩, hxy⟩
      · rintro ⟨⟨hxK, hxR⟩, ⟨hyK, hyR⟩, hxy⟩
        exact ⟨⟨hxK, hyK, hxy⟩,
          hK (by simpa using hxK) (by simpa using hyK) hxy, hxR, hyR⟩

private theorem filter_pairs_outside_eq (R K : Finset V)
    (hK : G.IsClique (K : Set V)) :
    (pairs K).filter (fun e => e ∈ outsideEdges G R) =
      pairs (K ∩ outsideVertices R) := by
  ext e
  induction e using Sym2.ind with
  | _ x y =>
      simp only [Finset.mem_filter, mk_mem_pairs, outsideEdges,
        SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
        Sym2.toFinset_mk_eq, Finset.insert_subset_iff, Finset.singleton_subset_iff,
        Finset.mem_inter]
      constructor
      · rintro ⟨⟨hxK, hyK, hxy⟩, -, hxO, hyO⟩
        exact ⟨⟨hxK, hxO⟩, ⟨hyK, hyO⟩, hxy⟩
      · rintro ⟨⟨hxK, hxO⟩, ⟨hyK, hyO⟩, hxy⟩
        exact ⟨⟨hxK, hyK, hxy⟩,
          hK (by simpa using hxK) (by simpa using hyK) hxy, hxO, hyO⟩

private theorem sum_choose_root (R : Finset V) (Q : CliquePartition G) :
    ∑ K ∈ Q.pieces, (K ∩ R).card.choose 2 = (rootEdges G R).card := by
  have h := PaperIV.SplitCompleteSharpLower.sum_card_filter_pairs Q
    (fun e => e ∈ rootEdges G R)
  have hf : G.edgeFinset.filter (fun e => e ∈ rootEdges G R) = rootEdges G R := by
    ext e
    simp only [Finset.mem_filter]
    constructor
    · exact fun he => he.2
    · intro he
      exact ⟨(Finset.mem_filter.1 he).1, he⟩
  rw [hf] at h
  calc
    ∑ K ∈ Q.pieces, (K ∩ R).card.choose 2 =
        ∑ K ∈ Q.pieces, ((pairs K).filter (fun e => e ∈ rootEdges G R)).card := by
          apply Finset.sum_congr rfl
          intro K hK
          rw [filter_pairs_root_eq R K (Q.isClique K hK), card_pairs]
    _ = (rootEdges G R).card := h

private theorem sum_choose_outside (R : Finset V) (Q : CliquePartition G) :
    ∑ K ∈ Q.pieces, (K ∩ outsideVertices R).card.choose 2 =
      (outsideEdges G R).card := by
  have h := PaperIV.SplitCompleteSharpLower.sum_card_filter_pairs Q
    (fun e => e ∈ outsideEdges G R)
  have hf : G.edgeFinset.filter (fun e => e ∈ outsideEdges G R) = outsideEdges G R := by
    ext e
    simp only [Finset.mem_filter]
    constructor
    · exact fun he => he.2
    · intro he
      exact ⟨(Finset.mem_filter.1 he).1, he⟩
  rw [hf] at h
  calc
    ∑ K ∈ Q.pieces, (K ∩ outsideVertices R).card.choose 2 =
        ∑ K ∈ Q.pieces,
          ((pairs K).filter (fun e => e ∈ outsideEdges G R)).card := by
          apply Finset.sum_congr rfl
          intro K hK
          rw [filter_pairs_outside_eq R K (Q.isClique K hK), card_pairs]
    _ = (outsideEdges G R).card := h

private theorem card_eq_root_add_outside (R K : Finset V) :
    K.card = (K ∩ R).card + (K ∩ outsideVertices R).card := by
  have hu : (K ∩ R) ∪ (K ∩ outsideVertices R) = K := by
    ext x
    simp [outsideVertices]
    tauto
  have hd : Disjoint (K ∩ R) (K ∩ outsideVertices R) := by
    exact (root_disjoint_outside R).mono inter_subset_right inter_subset_right
  calc
    K.card = ((K ∩ R) ∪ (K ∩ outsideVertices R)).card :=
      congrArg Finset.card hu.symm
    _ = (K ∩ R).card + (K ∩ outsideVertices R).card :=
      Finset.card_union_of_disjoint hd

private theorem numericDefect_rearranged (a b c : ℕ) (hc : c = a + b) :
    numericDefect a b =
      1 + 2 * (a.choose 2 : ℚ) + 4 * (b.choose 2 : ℚ) - (c.choose 2 : ℚ) := by
  subst c
  simp only [numericDefect, Nat.cast_choose_two]
  push_cast
  ring

/-- Exact partition-defect identity relative to an arbitrary clique root.

The sum on the left is over all physical pieces, with no order restriction.
The four terms on the right are respectively the number of pieces, the
complete-split baseline, the missing root--outside incidences, and three times
the number of exterior edges. -/
theorem sum_rootPieceDefect_eq (R : Finset V)
    (hR : G.IsClique (R : Set V)) (Q : CliquePartition G) :
    ∑ K ∈ Q.pieces, rootPieceDefect R K =
      (Q.size : ℚ) - splitBaseline (Fintype.card V) R.card
        + missingIncidences G R + 3 * (outsideEdges G R).card := by
  have hrootN := sum_choose_root (G := G) R Q
  have houtN := sum_choose_outside (G := G) R Q
  have htotalN : ∑ K ∈ Q.pieces, K.card.choose 2 = G.edgeFinset.card := by
    have h := PaperIV.SplitCompleteSharpLower.sum_card_filter_pairs Q (fun _ => True)
    simpa only [Finset.filter_true, card_pairs] using h
  have hroot : ∑ K ∈ Q.pieces, ((K ∩ R).card.choose 2 : ℚ) =
      ((rootEdges G R).card : ℚ) := by exact_mod_cast hrootN
  have hout : ∑ K ∈ Q.pieces, ((K ∩ outsideVertices R).card.choose 2 : ℚ) =
      ((outsideEdges G R).card : ℚ) := by exact_mod_cast houtN
  have htotal : ∑ K ∈ Q.pieces, (K.card.choose 2 : ℚ) =
      (G.edgeFinset.card : ℚ) := by exact_mod_cast htotalN
  have hedge := card_edgeFinset_add_missingIncidences G R
  have hrootCard := card_rootEdges G R hR
  have houtCard := card_outsideVertices R
  have hRle : R.card ≤ Fintype.card V := by
    simpa only [Finset.card_univ] using Finset.card_le_card (Finset.subset_univ R)
  have hedgeQ : (G.edgeFinset.card : ℚ) + missingIncidences G R =
      (rootEdges G R).card + (outsideEdges G R).card +
        (R.card : ℚ) * (outsideVertices R).card := by
    exact_mod_cast hedge
  have hrootQ : ((rootEdges G R).card : ℚ) =
      (R.card : ℚ) * (R.card - 1) / 2 := by
    have hq : ((rootEdges G R).card : ℚ) = (R.card.choose 2 : ℚ) := by
      exact_mod_cast hrootCard
    simpa only [Nat.cast_choose_two] using hq
  have houtQ : ((outsideVertices R).card : ℚ) =
      (Fintype.card V : ℚ) - R.card := by
    rw [houtCard, Nat.cast_sub hRle]
  rw [show (∑ K ∈ Q.pieces, rootPieceDefect R K) =
      ∑ K ∈ Q.pieces,
        (1 + 2 * ((K ∩ R).card.choose 2 : ℚ)
          + 4 * ((K ∩ outsideVertices R).card.choose 2 : ℚ)
          - (K.card.choose 2 : ℚ)) by
        apply Finset.sum_congr rfl
        intro K hK
        exact numericDefect_rearranged _ _ _ (card_eq_root_add_outside R K)]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_mul, Finset.sum_const, nsmul_eq_mul]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  rw [hroot, hout, htotal]
  simp only [CliquePartition.size, splitBaseline, Nat.cast_choose_two]
  nlinarith [hedgeQ, hrootQ, houtQ]

theorem numericDefect_one_le_of_ne_zero (a b : ℕ)
    (h : numericDefect a b ≠ 0) : 1 ≤ numericDefect a b := by
  by_cases hb0 : b = 0
  · subst b
    simp [numericDefect]
  by_cases hb1 : b = 1
  · subst b
    have ha : a ≠ 1 ∧ a ≠ 2 := by
      constructor
      · intro ha1
        apply h
        exact (numericDefect_eq_zero_iff a 1).2 ⟨rfl, Or.inl ha1⟩
      · intro ha2
        apply h
        exact (numericDefect_eq_zero_iff a 1).2 ⟨rfl, Or.inr ha2⟩
    by_cases ha2 : a ≤ 2
    · have ha0 : a = 0 := by omega
      subst a
      norm_num [numericDefect]
    · have ha3 : 3 ≤ a := by omega
      simp only [numericDefect, Nat.cast_choose_two]
      have haq : (3 : ℚ) ≤ a := by exact_mod_cast ha3
      nlinarith
  · have hb2 : 2 ≤ b := by omega
    rw [numericDefect_closed]
    have hz : 0 ≤ ((a : ℚ) - b) * ((a : ℚ) - b - 1) := by
      by_cases hab : a ≤ b
      · have hq : (a : ℚ) ≤ b := by exact_mod_cast hab
        nlinarith
      · have hab' : b < a := Nat.lt_of_not_ge hab
        have hq : (b : ℚ) + 1 ≤ a := by
          exact_mod_cast (Nat.add_one_le_iff.mpr hab')
        nlinarith
    have hbq : (2 : ℚ) ≤ b := by exact_mod_cast hb2
    nlinarith [sq_nonneg ((b : ℚ) - 1)]

theorem rootPieceDefect_one_le_of_noncanonical (R K : Finset V)
    (h : ¬ IsCanonicalAt R K) : 1 ≤ rootPieceDefect R K := by
  apply numericDefect_one_le_of_ne_zero
  exact fun hz => h ((rootPieceDefect_eq_zero_iff R K).1 hz)

/-- The literal family of pieces that are neither root--outside edges nor
root-root--outside triangles. -/
noncomputable def noncanonicalPieces (R : Finset V)
    (Q : CliquePartition G) : Finset (Finset V) := by
  classical
  exact Q.pieces.filter fun K => ¬ IsCanonicalAt R K

/-- Each noncanonical physical piece consumes at least one unit of the exact
partition-defect budget. -/
theorem card_noncanonicalPieces_le_sum_defect (R : Finset V)
    (Q : CliquePartition G) :
    ((noncanonicalPieces R Q).card : ℚ) ≤
      ∑ K ∈ Q.pieces, rootPieceDefect R K := by
  classical
  calc
    ((noncanonicalPieces R Q).card : ℚ) =
        ∑ K ∈ noncanonicalPieces R Q, (1 : ℚ) := by simp
    _ ≤ ∑ K ∈ noncanonicalPieces R Q, rootPieceDefect R K := by
      apply Finset.sum_le_sum
      intro K hK
      exact rootPieceDefect_one_le_of_noncanonical R K
        (Finset.mem_filter.1 hK).2
    _ ≤ ∑ K ∈ Q.pieces, rootPieceDefect R K := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun K _ _ => rootPieceDefect_nonneg R K)

/-- Quantitative rigidity around any clique root.  If a partition exceeds the
complete-split baseline by at most `τ`, then only the displayed defect budget
can be spent on noncanonical pieces. -/
theorem card_noncanonicalPieces_le (R : Finset V)
    (hR : G.IsClique (R : Set V)) (Q : CliquePartition G) (τ : ℚ)
    (hQ : (Q.size : ℚ) ≤ splitBaseline (Fintype.card V) R.card + τ) :
    ((noncanonicalPieces R Q).card : ℚ) ≤
      τ + missingIncidences G R + 3 * (outsideEdges G R).card := by
  have hcard := card_noncanonicalPieces_le_sum_defect R Q
  have hid := sum_rootPieceDefect_eq R hR Q
  linarith

/-- **Partition stability at the chordal extremum.**

For every sufficiently large chordal graph whose order-at-most-four clique
partitions stay within deficit `δ` of the sharp target, one clique root works
simultaneously for every (unrestricted-order) clique partition `Q`.  If `Q`
has at most `targetSize n + τ` pieces, then all but at most `τ + 48 δ` of its
pieces are canonical root--outside edges or root-root--outside triangles.

The coefficient `48` is the literal consequence of the same physical witness
that yields the `16 δ` edit-distance theorem: exterior edges have coefficient
`1/16` in its retained budget, while the exact partition identity charges
three units per exterior edge. -/
theorem chordal_partition_stability :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        PaperIV.FarRounding.IsChordal G →
        ∀ δ : ℚ, 0 ≤ δ →
          δ ≤ PaperIV.IntegralStability.gamma * (n : ℚ) ^ 2 →
          (∀ Q : CliquePartition G, Q.OrderAtMost 4 →
              (PaperIV.targetSize n : ℚ) - δ ≤ (Q.size : ℚ)) →
          ∃ R : Finset (Fin n), G.IsClique (R : Set (Fin n)) ∧
            2 ≤ R.card ∧ R.card ≤ (Finset.univ \ R).card ∧
            ∀ (Q : CliquePartition G) (τ : ℚ),
              (Q.size : ℚ) ≤ PaperIV.targetSize n + τ →
              ((noncanonicalPieces R Q).card : ℚ) ≤ τ + 48 * δ := by
  obtain ⟨N, hN⟩ := PaperIV.IntegralStability.chordal_linear_stability_sixteen
  refine ⟨N, ?_⟩
  intro n hn G _ hG δ hδ0 hδ hmin
  obtain ⟨R, hR, hRtwo, hRout, hbase, _haccounts, hreserve, _hdist⟩ :=
    hN n hn G hG δ hδ0 hδ hmin
  refine ⟨R, hR, hRtwo, hRout, ?_⟩
  intro Q τ hQ
  have hQbase : (Q.size : ℚ) ≤
      splitBaseline (n : ℚ) R.card +
        (τ + ((PaperIV.targetSize n : ℚ) - splitBaseline (n : ℚ) R.card)) := by
    linarith
  have hcard := card_noncanonicalPieces_le R hR Q
    (τ + ((PaperIV.targetSize n : ℚ) - splitBaseline (n : ℚ) R.card))
    (by simpa using hQbase)
  have hr : 0 ≤ (PaperIV.targetSize n : ℚ) - splitBaseline (n : ℚ) R.card := by
    linarith
  have hm : (0 : ℚ) ≤ ((outsideEdges G R).card : ℚ) := by positivity
  have hA : (0 : ℚ) ≤ (missingIncidences G R : ℚ) := by positivity
  nlinarith

end PaperIV.RootPartitionStability

