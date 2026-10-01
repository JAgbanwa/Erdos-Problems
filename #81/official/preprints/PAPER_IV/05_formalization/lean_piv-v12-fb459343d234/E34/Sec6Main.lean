import E34.Sec6Count

/-!
# E34 — §6 of arXiv:1902.06135: assembly (Theorem 1 from Lemma 11, counting form)
-/

namespace E34

open Finset

open scoped Classical

variable {n : ℕ}

/-- Samples: `q` ordered pairs for `S`, `ℓ` blocks of `M` vertices for `U`. -/
abbrev Omega (n q ℓ M : ℕ) := (Fin q → Fin n × Fin n) × (Fin ℓ → Fin M → Fin n)

/-- Count of the samples violating `U ∩ Y ⊆ Y_S` (Claim 6 summed over `U`). -/
theorem countA (G : SimpleGraph (Fin n)) (δ : ℝ) (hδ1 : δ ≤ 1) (q ℓ M : ℕ) :
    ((univ.filter (fun ω : Omega n q ℓ M =>
      ∃ u ∈ uSet ω.2, u ∉ lowSet G δ ∧ ¬ InYS G ω.1 u)).card : ℝ) ≤
      ((ℓ * M : ℕ) : ℝ) * (1 - δ) ^ q * ((n : ℝ) ^ (2 * q) * (n : ℝ) ^ (M * ℓ)) := by
  rw [card_filter_prod_eq_sum_right (fun pS wU => ∃ u ∈ uSet wU, u ∉ lowSet G δ ∧ ¬ InYS G pS u)]
  push_cast
  have hnn : 0 ≤ (1 - δ) * (n : ℝ) ^ 2 := mul_nonneg (by linarith) (by positivity)
  calc ∑ wU : Fin ℓ → Fin M → Fin n, ((univ.filter (fun pS : Fin q → Fin n × Fin n =>
        ∃ u ∈ uSet wU, u ∉ lowSet G δ ∧ ¬ InYS G pS u)).card : ℝ)
      ≤ ∑ _wU : Fin ℓ → Fin M → Fin n, ((ℓ : ℝ) * M) * ((1 - δ) * (n : ℝ) ^ 2) ^ q := by
        refine sum_le_sum (fun wU _ => (claim6_count G δ hδ1 (uSet wU) q).trans ?_)
        refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hnn q)
        have := card_uSet_le wU
        exact_mod_cast this
    _ = (ℓ : ℝ) * M * (1 - δ) ^ q * ((n : ℝ) ^ (2 * q) * (n : ℝ) ^ (M * ℓ)) := by
        rw [sum_const, card_univ, nsmul_eq_mul]
        simp only [Fintype.card_fun, Fintype.card_fin]
        push_cast
        rw [mul_pow, ← pow_mul, ← pow_mul]
        ring

/-- Count of the samples for which some compressed tree pins `H[U]`. -/
theorem countB (m11 : ℝ → ℕ → ℕ) (hL : Lemma11With m11) (ε' : ℝ) (hε' : 0 < ε')
    (G H : SimpleGraph (Fin n))
    (hfar : ∀ F : SimpleGraph (Fin n), AlonShapira.IsChordal F →
      ε' * (n : ℝ) ^ 2 < (AlonShapira.editDist H F : ℝ))
    (q ℓ M : ℕ) (hM : ∀ K0 ≤ kMax q, m11 ε' K0 ≤ M) (hcodes : 4 * nCodes q ≤ 2 ^ ℓ) :
    4 * (univ.filter (fun ω : Omega n q ℓ M =>
      ∃ K0, K0 ≤ kMax q ∧ ∃ Γ : RTree K0, ∃ y : Option (Pos q × Pos q) → Fin K0,
        PinnedOn Γ (fun u => y (lab G ω.1 u)) H (uSet ω.2))).card ≤
      n ^ (2 * q) * n ^ (M * ℓ) := by
  rw [card_filter_prod_eq_sum_left (fun pS wU => ∃ K0, K0 ≤ kMax q ∧ ∃ Γ : RTree K0,
    ∃ y : Option (Pos q × Pos q) → Fin K0, PinnedOn Γ (fun u => y (lab G pS u)) H (uSet wU))]
  have hone : ∀ pS : Fin q → Fin n × Fin n, 4 * (univ.filter (fun wU : Fin ℓ → Fin M → Fin n =>
      ∃ K0, K0 ≤ kMax q ∧ ∃ Γ : RTree K0, ∃ y : Option (Pos q × Pos q) → Fin K0,
        PinnedOn Γ (fun u => y (lab G pS u)) H (uSet wU))).card ≤ n ^ (M * ℓ) := by
    intro pS
    have h1 := pinned_count m11 hL ε' hε' H hfar q ℓ M hM (lab G pS)
    set c := (univ.filter (fun wU : Fin ℓ → Fin M → Fin n =>
      ∃ K0, K0 ≤ kMax q ∧ ∃ Γ : RTree K0, ∃ y : Option (Pos q × Pos q) → Fin K0,
        PinnedOn Γ (fun u => y (lab G pS u)) H (uSet wU))).card
    have hpos : 0 < 2 ^ ℓ := by positivity
    have : 2 ^ ℓ * (4 * c) ≤ 2 ^ ℓ * n ^ (M * ℓ) := by
      calc 2 ^ ℓ * (4 * c) = 4 * (2 ^ ℓ * c) := by ring
        _ ≤ 4 * (nCodes q * n ^ (M * ℓ)) := Nat.mul_le_mul_left _ h1
        _ = (4 * nCodes q) * n ^ (M * ℓ) := by ring
        _ ≤ 2 ^ ℓ * n ^ (M * ℓ) := Nat.mul_le_mul_right _ hcodes
    exact Nat.le_of_mul_le_mul_left this hpos
  rw [mul_sum]
  calc ∑ pS : Fin q → Fin n × Fin n, 4 * (univ.filter (fun wU : Fin ℓ → Fin M → Fin n =>
        ∃ K0, K0 ≤ kMax q ∧ ∃ Γ : RTree K0, ∃ y : Option (Pos q × Pos q) → Fin K0,
          PinnedOn Γ (fun u => y (lab G pS u)) H (uSet wU))).card
      ≤ ∑ _pS : Fin q → Fin n × Fin n, n ^ (M * ℓ) := sum_le_sum (fun pS _ => hone pS)
    _ = n ^ (2 * q) * n ^ (M * ℓ) := by
        rw [sum_const, card_univ, smul_eq_mul]
        simp only [Fintype.card_fun, Fintype.card_prod, Fintype.card_fin]
        ring

/-- **§6 of the paper, counting form.**  If `G` is `ε`-far from chordal and the parameters
`q, ℓ, M` satisfy the three displayed conditions, then at most half of the samples
`ω = (pS, wU)` induce a chordal graph. -/
theorem sec6_count (m11 : ℝ → ℕ → ℕ) (hL : Lemma11With m11) (ε : ℝ) (hε0 : 0 < ε)
    (hε1 : ε ≤ 1) (q ℓ M : ℕ) (hM : ∀ K0 ≤ kMax q, m11 (ε ^ 2 / 256 / 2) K0 ≤ M)
    (hcodes : 4 * nCodes q ≤ 2 ^ ℓ)
    (hq : 4 * ((ℓ * M : ℕ) : ℝ) * (1 - ε ^ 2 / 256) ^ q ≤ 1)
    (hn : 1 ≤ n) (G : SimpleGraph (Fin n))
    (hfar : ∀ F : SimpleGraph (Fin n), AlonShapira.IsChordal F →
      ε * (n : ℝ) ^ 2 ≤ (AlonShapira.editDist G F : ℝ)) :
    2 * (univ.filter (fun ω : Omega n q ℓ M =>
      AlonShapira.IsChordal (G.induce ((sSet ω.1 ∪ uSet ω.2 : Finset (Fin n)) :
        Set (Fin n))))).card ≤ n ^ (2 * q) * n ^ (M * ℓ) := by
  have hδ0 : 0 < ε ^ 2 / 256 / 2 := by positivity
  have hδ1 : ε ^ 2 / 256 ≤ 1 := by nlinarith
  have hHfar := sec6_claim1 G ε hε0 hε1 hn hfar
  have hsub : univ.filter (fun ω : Omega n q ℓ M =>
      AlonShapira.IsChordal (G.induce ((sSet ω.1 ∪ uSet ω.2 : Finset (Fin n)) : Set (Fin n))))
      ⊆ univ.filter (fun ω : Omega n q ℓ M =>
          ∃ u ∈ uSet ω.2, u ∉ lowSet G (ε ^ 2 / 256) ∧ ¬ InYS G ω.1 u) ∪
        univ.filter (fun ω : Omega n q ℓ M =>
          ∃ K0, K0 ≤ kMax q ∧ ∃ Γ : RTree K0, ∃ y : Option (Pos q × Pos q) → Fin K0,
            PinnedOn Γ (fun u => y (lab G ω.1 u))
              (padGraph G (lowSet G (ε ^ 2 / 256))) (uSet ω.2)) := by
    intro ω hω
    rw [mem_filter] at hω
    by_cases hA : ∃ u ∈ uSet ω.2, u ∉ lowSet G (ε ^ 2 / 256) ∧ ¬ InYS G ω.1 u
    · exact mem_union_left _ (mem_filter.2 ⟨mem_univ _, hA⟩)
    · push_neg at hA
      refine mem_union_right _ (mem_filter.2 ⟨mem_univ _, ?_⟩)
      exact sec6_claim2 G _ ω.1 (uSet ω.2) hω.2 hA
  have hA := countA G (ε ^ 2 / 256) hδ1 q ℓ M
  have hB := countB m11 hL _ hδ0 G _ hHfar q ℓ M hM hcodes
  have htot := (card_le_card hsub).trans (card_union_le _ _)
  have hB' : (((univ.filter (fun ω : Omega n q ℓ M =>
          ∃ K0, K0 ≤ kMax q ∧ ∃ Γ : RTree K0, ∃ y : Option (Pos q × Pos q) → Fin K0,
            PinnedOn Γ (fun u => y (lab G ω.1 u))
              (padGraph G (lowSet G (ε ^ 2 / 256))) (uSet ω.2))).card : ℕ) : ℝ) * 4 ≤
      (n : ℝ) ^ (2 * q) * (n : ℝ) ^ (M * ℓ) := by
    have := (Nat.cast_le (α := ℝ)).2 hB
    push_cast at this
    linarith
  have htot' := (Nat.cast_le (α := ℝ)).2 htot
  push_cast at htot'
  have hnn : (0 : ℝ) ≤ (n : ℝ) ^ (2 * q) * (n : ℝ) ^ (M * ℓ) := by positivity
  have hA' : ((ℓ * M : ℕ) : ℝ) * (1 - ε ^ 2 / 256) ^ q *
      ((n : ℝ) ^ (2 * q) * (n : ℝ) ^ (M * ℓ)) ≤ (1 / 4) * ((n : ℝ) ^ (2 * q) * (n : ℝ) ^ (M * ℓ)) :=
    mul_le_mul_of_nonneg_right (by linarith) hnn
  have hfin : (2 * ((univ.filter (fun ω : Omega n q ℓ M =>
      AlonShapira.IsChordal (G.induce ((sSet ω.1 ∪ uSet ω.2 : Finset (Fin n)) :
        Set (Fin n))))).card : ℕ) : ℝ) ≤ ((n ^ (2 * q) * n ^ (M * ℓ) : ℕ) : ℝ) := by
    push_cast
    push_cast at hA hA'
    linarith
  exact_mod_cast hfin

end E34
