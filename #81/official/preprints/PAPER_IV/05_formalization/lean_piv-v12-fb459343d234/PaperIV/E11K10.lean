import PaperIV.E11Core

/-!
# E11: the K₁₀ parity witness (proof)
-/

namespace PaperIV.E11

open Finset PaperIV.FarRounding

theorem targetSize_lt_of_orderAtMost_three_aux (n : ℕ) (hn : n % 6 = 4)
    (Q : CliquePartition (⊤ : SimpleGraph (Fin n))) (hQ : Q.OrderAtMost 3) :
    targetSize n < Q.size := by
  set P2 := Q.pieces.filter (fun K => K.card = 2) with hP2
  set P3 := Q.pieces.filter (fun K => ¬ K.card = 2) with hP3
  have hc3 : ∀ K ∈ P3, K.card = 3 := by
    intro K hK
    rw [hP3, mem_filter] at hK
    have := Q.two_le_card K hK.1
    have := hQ K hK.1
    omega
  -- (a) counting pairs
  have hsum := pairs_sum Q
  rw [← sum_filter_add_sum_filter_not Q.pieces (fun K => K.card = 2)] at hsum
  have e2 : ∑ K ∈ P2, K.card.choose 2 = P2.card := by
    rw [sum_congr rfl (fun K hK => by rw [(mem_filter.1 hK).2]), sum_const, smul_eq_mul]
    simp
  have e3 : ∑ K ∈ P3, K.card.choose 2 = 3 * P3.card := by
    rw [sum_congr rfl (fun K hK => by rw [hc3 K hK]), sum_const, smul_eq_mul, mul_comm]
    rfl
  rw [← hP2, ← hP3, e2, e3] at hsum
  have hsum' : P2.card + 3 * P3.card = n.choose 2 := by
    have h := SimpleGraph.card_edgeFinset_top_eq_card_choose_two (V := Fin n)
    rw [Fintype.card_fin] at h
    rw [← h]
    convert hsum using 1
  have hsize : Q.size = P2.card + P3.card := by
    rw [CliquePartition.size, hP2, hP3, card_filter_add_card_filter_not]
  -- (b) local count: every vertex lies in a 2-piece
  have hcover : ∀ x : Fin n, ∃ K ∈ P2, x ∈ K := by
    intro x
    by_contra hno
    push_neg at hno
    have hs := star_sum Q x
    have hdeg : ((⊤ : SimpleGraph (Fin n)).neighborFinset x).card = n - 1 := by
      rw [SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.complete_graph_degree,
        Fintype.card_fin]
    rw [hdeg] at hs
    have hall : ∀ K ∈ Q.pieces.filter (x ∈ ·), K.card - 1 = 2 := by
      intro K hK
      rw [mem_filter] at hK
      have hK3 : K ∈ P3 := by
        rw [hP3, mem_filter]
        refine ⟨hK.1, fun h2 => hno K ?_ hK.2⟩
        rw [hP2, mem_filter]; exact ⟨hK.1, h2⟩
      rw [hc3 K hK3]
    rw [sum_congr rfl hall, sum_const, smul_eq_mul] at hs
    omega
  have hn2 : n ≤ 2 * P2.card := by
    have hsub : (univ : Finset (Fin n)) ⊆ P2.biUnion id := by
      intro x _
      obtain ⟨K, hK, hx⟩ := hcover x
      exact mem_biUnion.2 ⟨K, hK, hx⟩
    have h1 := card_le_card hsub
    rw [card_univ, Fintype.card_fin] at h1
    refine h1.trans (card_biUnion_le.trans ?_)
    simp only [id]
    rw [sum_congr rfl (fun K hK => (mem_filter.1 hK).2), sum_const, smul_eq_mul]
    rw [mul_comm]
  -- (c), (d) arithmetic
  obtain ⟨q, rfl⟩ : ∃ q, n = 6 * q + 4 := ⟨n / 6, by omega⟩
  have hch : (6 * q + 4).choose 2 = 18 * (q * q) + 21 * q + 6 := by
    rw [Nat.choose_two_right]
    have : 6 * q + 4 - 1 = 6 * q + 3 := by omega
    rw [this]
    apply Nat.div_eq_of_eq_mul_left (by norm_num)
    ring
  have hts : targetSize (6 * q + 4) = 6 * (q * q) + 9 * q + 3 := by
    rw [targetSize]
    have h : (6 * q + 4) * (6 * q + 4 + 1) = 6 * (6 * (q * q) + 9 * q + 3) + 2 := by ring
    rw [h]
    omega
  rw [hts, hsize]
  rw [hch] at hsum'
  omega

end PaperIV.E11
