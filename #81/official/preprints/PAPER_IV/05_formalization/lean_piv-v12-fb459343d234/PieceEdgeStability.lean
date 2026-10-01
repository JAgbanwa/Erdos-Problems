import RootScore

/-! Edge mass, rather than just the number, of noncanonical partition pieces.
The partition may contain cliques of arbitrary order. -/
namespace PaperIV.SublinearResearch
open Finset PaperIV.FarRounding PaperIV.RootVocab PaperIV.RootPartitionStability

/-- Ten is the best coefficient in this numerical inequality (profile (3,2)). -/
theorem piece_edges_le_ten_defect (a b : ℕ) (h : numericDefect a b ≠ 0) :
    ((a+b).choose 2 : ℚ) ≤ 10*numericDefect a b := by
  by_cases hb0 : b = 0
  · subst b
    have hn := Nat.cast_nonneg (a.choose 2) (α := ℚ)
    simp only [Nat.add_zero, numericDefect, Nat.choose_eq_zero_of_lt (by decide : 0 < 2)]
    norm_num at *
    linarith
  by_cases hb1 : b = 1
  · subst b
    have ha : a = 0 ∨ 3 ≤ a := by
      have hx : ¬ (a = 1 ∨ a = 2) := fun ha =>
        h ((numericDefect_eq_zero_iff a 1).mpr ⟨rfl,ha⟩)
      omega
    rcases ha with rfl | ha
    · norm_num [numericDefect]
    · have haq : (3 : ℚ) ≤ a := by exact_mod_cast ha
      simp only [numericDefect, Nat.cast_choose_two, Nat.cast_add, Nat.cast_one]
      nlinarith [mul_nonneg (show 0 ≤ (a : ℚ)-3 by linarith)
        (show 0 ≤ 9*(a : ℚ)-4 by linarith)]
  by_cases hb2 : b = 2
  · subst b
    simp only [numericDefect, Nat.cast_choose_two, Nat.cast_add, Nat.cast_ofNat]
    rcases le_or_gt a 2 with ha | ha
    · have haq : (a : ℚ) ≤ 2 := by exact_mod_cast ha
      nlinarith [mul_nonneg (show 0 ≤ 3-(a : ℚ) by linarith)
        (show 0 ≤ 26-9*(a : ℚ) by linarith)]
    · have haq : (3 : ℚ) ≤ a := by exact_mod_cast (show 3 ≤ a by omega)
      nlinarith [mul_nonneg (show 0 ≤ (a : ℚ)-3 by linarith)
        (show 0 ≤ 9*(a : ℚ)-26 by linarith)]
  have hbq : (3 : ℚ) ≤ b := by exact_mod_cast (show 3 ≤ b by omega)
  simp only [numericDefect, Nat.cast_choose_two, Nat.cast_add]
  nlinarith [sq_nonneg (18*(a : ℚ)-22*b-9),
    mul_nonneg (show 0 ≤ (b : ℚ)-3 by linarith)
      (show 0 ≤ 560*(b : ℚ)+240 by linarith)]

theorem piece_edges_coefficient_sharp (c : ℚ)
    (h : ∀ a b : ℕ, numericDefect a b ≠ 0 → ((a+b).choose 2 : ℚ) ≤ c*numericDefect a b) :
    10 ≤ c := by
  have hh := h 3 2 (by norm_num [numericDefect])
  norm_num [numericDefect] at hh
  exact hh

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Total number of edges carried by the noncanonical pieces; there is no
overcount because the input is an edge partition. -/
noncomputable def noncanonicalEdgeMass (R : Finset V) (Q : CliquePartition G) : ℕ :=
  ∑ K ∈ noncanonicalPieces R Q, K.card.choose 2

theorem noncanonicalEdgeMass_le_sum_defect (R : Finset V) (Q : CliquePartition G) :
    (noncanonicalEdgeMass R Q : ℚ) ≤ 10*∑ K ∈ Q.pieces, rootPieceDefect R K := by
  classical
  have hcard (K : Finset V) : K.card = (K ∩ R).card+(K ∩ outsideVertices R).card := by
    have hd : Disjoint (K ∩ R) (K ∩ outsideVertices R) := by
      apply disjoint_left.mpr
      intro x hx hy
      simp only [mem_inter, outsideVertices, mem_sdiff, mem_univ, true_and] at hx hy
      exact hy.2 hx.2
    have hu : (K ∩ R) ∪ (K ∩ outsideVertices R) = K := by
      ext x
      simp only [mem_union, mem_inter, outsideVertices, mem_sdiff, mem_univ, true_and]
      tauto
    exact (congrArg card hu).symm.trans (card_union_of_disjoint hd)
  have hpiece : ∀ K ∈ noncanonicalPieces R Q,
      (K.card.choose 2 : ℚ) ≤ 10*rootPieceDefect R K := by
    intro K hK
    have hnc := (mem_filter.mp hK).2
    have hn : rootPieceDefect R K ≠ 0 := fun hz => hnc ((rootPieceDefect_eq_zero_iff R K).mp hz)
    rw [hcard K]
    exact piece_edges_le_ten_defect _ _ hn
  unfold noncanonicalEdgeMass
  push_cast
  calc
    _ ≤ ∑ K ∈ noncanonicalPieces R Q, 10*rootPieceDefect R K := sum_le_sum hpiece
    _ ≤ ∑ K ∈ Q.pieces, 10*rootPieceDefect R K :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun K _ _ => by
        exact mul_nonneg (by norm_num) (rootPieceDefect_nonneg R K))
    _ = _ := by rw [mul_sum]

theorem noncanonicalEdgeMass_le (R : Finset V) (hR : G.IsClique (R : Set V))
    (Q : CliquePartition G) (τ : ℚ)
    (hQ : (Q.size : ℚ) ≤ PaperIV.splitBaseline (Fintype.card V) R.card+τ) :
    (noncanonicalEdgeMass R Q : ℚ) ≤
      10*(τ+missingIncidences G R+3*(outsideEdges G R).card) := by
  have h := noncanonicalEdgeMass_le_sum_defect R Q
  have hid := sum_rootPieceDefect_eq R hR Q
  linarith

theorem noncanonicalEdgeMass_le_rootScore {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] {R : Finset (Fin n)} (hR : G.IsClique (R : Set (Fin n)))
    (Q : CliquePartition G) (τ : ℚ) (hQ : (Q.size : ℚ) ≤ targetSize n+τ) :
    (noncanonicalEdgeMass R Q : ℚ) ≤ 10*τ+30*rootScore G R := by
  have hb := noncanonicalEdgeMass_le R hR Q
    (τ+((targetSize n : ℚ)-PaperIV.splitBaseline n R.card))
    (by simp only [Fintype.card_fin]; linarith)
  have hg := integral_baseline_le_target n R.card
  have hw : 0 ≤ (n : ℚ)*|(R.card : ℚ)-(n : ℚ)/3| := by positivity
  have hm : (0 : ℚ) ≤ missingIncidences G R := Nat.cast_nonneg _
  dsimp [rootScore]
  linarith

theorem chordal_partition_edge_stability :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ G : SimpleGraph (Fin n), ∀ [DecidableRel G.Adj],
      IsChordal G → ∀ δ : ℚ, 0 ≤ δ → δ ≤ PaperIV.IntegralStability.gamma*(n : ℚ)^2 →
      (∀ Q : CliquePartition G, Q.OrderAtMost 4 → (PaperIV.targetSize n : ℚ)-δ ≤ Q.size) →
      ∃ R : Finset (Fin n), G.IsClique (R : Set (Fin n)) ∧
        ∀ (Q : CliquePartition G) (τ : ℚ), (Q.size : ℚ) ≤ PaperIV.targetSize n+τ →
          (noncanonicalEdgeMass R Q : ℚ) ≤ 10*τ+480*δ := by
  obtain ⟨N,hN⟩ := PaperIV.IntegralStability.chordal_linear_stability_sixteen
  refine ⟨N,?_⟩
  intro n hn G _ hG δ hδ0 hδ hmin
  obtain ⟨R,hR,_,_,hbase,_,hreserve,_⟩ := hN n hn G hG δ hδ0 hδ hmin
  refine ⟨R,hR,?_⟩
  intro Q τ hQ
  have hb := noncanonicalEdgeMass_le R hR Q
    (τ+((PaperIV.targetSize n : ℚ)-PaperIV.splitBaseline n R.card))
    (by simp only [Fintype.card_fin]; linarith)
  have hm : (0 : ℚ) ≤ (outsideEdges G R).card := Nat.cast_nonneg _
  have hA : (0 : ℚ) ≤ missingIncidences G R := Nat.cast_nonneg _
  nlinarith

end PaperIV.SublinearResearch
