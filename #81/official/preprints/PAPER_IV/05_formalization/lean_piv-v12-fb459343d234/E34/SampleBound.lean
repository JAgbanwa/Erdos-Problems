import RequestProject.AlonShapira

/-!
# E34 — sampling: bad `m`-sets are controlled by induced cycle counts

* `badSets G m` — the `m`-subsets `U` of `Fin n` such that `G[U]` is not chordal
  (`AlonShapira.IsChordal`, i.e. `G[U]` contains an induced `C_k`, `k ≥ 4`).
* `card_badSets_le` — union bound:
  `#badSets G m ≤ Σ_{4 ≤ k ≤ m} indCopies (C_k) G · C(n-k, m-k)`.
* `choose_ratio` — `C(n-k, m-k) · n^k ≤ C(n, m) · m^k` for `k ≤ m ≤ n`.
-/

namespace E34

open Finset SimpleGraph

open scoped Classical

variable {n : ℕ}

/-- The `m`-subsets of `Fin n` inducing a non-chordal graph. -/
noncomputable def badSets (G : SimpleGraph (Fin n)) (m : ℕ) : Finset (Finset (Fin n)) :=
  (powersetCard m univ).filter (fun U => ¬ AlonShapira.IsChordal (G.induce (U : Set (Fin n))))

/-- Supersets of a fixed `k`-set among the `m`-sets: at most `C(n-k, m-k)`. -/
theorem card_supersets_le (T : Finset (Fin n)) (m : ℕ) :
    ((powersetCard m univ).filter (fun U => T ⊆ U)).card ≤ (n - T.card).choose (m - T.card) := by
  have hsub : (powersetCard m univ).filter (fun U => T ⊆ U) ⊆
      (powersetCard (m - T.card) (univ \ T)).image (fun W => W ∪ T) := by
    intro U hU
    rw [mem_filter, mem_powersetCard] at hU
    obtain ⟨⟨_, hUc⟩, hTU⟩ := hU
    rw [mem_image]
    refine ⟨U \ T, ?_, sdiff_union_of_subset hTU⟩
    rw [mem_powersetCard]
    refine ⟨sdiff_subset_sdiff (subset_univ _) (Finset.Subset.refl _), ?_⟩
    rw [card_sdiff_of_subset hTU, hUc]
  refine (card_le_card hsub).trans (card_image_le.trans ?_)
  rw [card_powersetCard, card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_fin]

/-- A non-chordal induced subgraph on `U` yields an induced cycle of `G` inside `U`. -/
theorem exists_cycle_of_not_chordal (G : SimpleGraph (Fin n)) (U : Finset (Fin n))
    (h : ¬ AlonShapira.IsChordal (G.induce (U : Set (Fin n)))) :
    ∃ k, 4 ≤ k ∧ k ≤ U.card ∧ ∃ e : SimpleGraph.cycleGraph k ↪g G,
      (univ : Finset (Fin k)).map e.toEmbedding ⊆ U := by
  unfold AlonShapira.IsChordal AlonShapira.IndFree at h
  push_neg at h
  obtain ⟨k, H, ⟨hk, rfl⟩, hne⟩ := h
  obtain ⟨e⟩ := hne
  refine ⟨k, hk, ?_, (Embedding.induce (U : Set (Fin n))).comp e, ?_⟩
  · have := Fintype.card_le_of_injective _ e.injective
    simpa using this
  · intro x hx
    rw [mem_map] at hx
    obtain ⟨i, _, rfl⟩ := hx
    exact (e i).2

/-- **Union bound.** -/
theorem card_badSets_le (G : SimpleGraph (Fin n)) (m : ℕ) :
    (badSets G m).card ≤
      ∑ k ∈ Icc 4 m, AlonShapira.indCopies (SimpleGraph.cycleGraph k) G * (n - k).choose (m - k) := by
  have hsub : badSets G m ⊆ (Icc 4 m).biUnion (fun k =>
      (univ : Finset (SimpleGraph.cycleGraph k ↪g G)).biUnion (fun e =>
        (powersetCard m univ).filter (fun U => (univ : Finset (Fin k)).map e.toEmbedding ⊆ U))) := by
    intro U hU
    rw [badSets, mem_filter, mem_powersetCard] at hU
    obtain ⟨⟨_, hUc⟩, hnc⟩ := hU
    obtain ⟨k, hk, hkU, e, he⟩ := exists_cycle_of_not_chordal G U hnc
    rw [mem_biUnion]
    refine ⟨k, mem_Icc.2 ⟨hk, hUc ▸ hkU⟩, ?_⟩
    rw [mem_biUnion]
    refine ⟨e, mem_univ _, ?_⟩
    rw [mem_filter, mem_powersetCard]
    exact ⟨⟨subset_univ _, hUc⟩, he⟩
  refine (card_le_card hsub).trans (card_biUnion_le.trans (sum_le_sum fun k _ => ?_))
  refine card_biUnion_le.trans ?_
  have hb : ∀ e ∈ (univ : Finset (SimpleGraph.cycleGraph k ↪g G)),
      ((powersetCard m univ).filter (fun U => (univ : Finset (Fin k)).map e.toEmbedding ⊆ U)).card ≤
        (n - k).choose (m - k) := by
    intro e _
    have := card_supersets_le ((univ : Finset (Fin k)).map e.toEmbedding) m
    simpa using this
  refine (sum_le_sum hb).trans ?_
  rw [sum_const, card_univ, smul_eq_mul]
  unfold AlonShapira.indCopies
  exact le_of_eq (by congr 1)

/-- `m^{(k)} · n^k ≤ n^{(k)} · m^k` for `m ≤ n` (falling factorials). -/
theorem descFactorial_mul_pow_le {m : ℕ} (hmn : m ≤ n) (k : ℕ) :
    m.descFactorial k * n ^ k ≤ n.descFactorial k * m ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.descFactorial_succ, Nat.descFactorial_succ, pow_succ, pow_succ]
    have h1 : (m - k) * n ≤ (n - k) * m := by
      rcases le_or_gt k m with hk | hk
      · have e1 : (m - k) * n + k * n = m * n := by
          rw [← add_mul, Nat.sub_add_cancel hk]
        have e2 : (n - k) * m + k * m = n * m := by
          rw [← add_mul, Nat.sub_add_cancel (hk.trans hmn)]
        have : k * m ≤ k * n := Nat.mul_le_mul_left _ hmn
        nlinarith
      · rw [Nat.sub_eq_zero_of_le hk.le]; simp
    calc (m - k) * m.descFactorial k * (n ^ k * n)
        = ((m - k) * n) * (m.descFactorial k * n ^ k) := by ring
      _ ≤ ((n - k) * m) * (n.descFactorial k * m ^ k) := Nat.mul_le_mul h1 ih
      _ = (n - k) * n.descFactorial k * (m ^ k * m) := by ring

/-- `C(n-k, m-k) · n^k ≤ C(n, m) · m^k` for `k ≤ m ≤ n`. -/
theorem choose_ratio {m k : ℕ} (hkm : k ≤ m) (hmn : m ≤ n) :
    (n - k).choose (m - k) * n ^ k ≤ n.choose m * m ^ k := by
  have hcm : n.choose m * m.choose k = n.choose k * (n - k).choose (m - k) :=
    Nat.choose_mul hkm
  have hd := descFactorial_mul_pow_le hmn k
  rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_factorial_mul_choose] at hd
  have hd' : m.choose k * n ^ k ≤ n.choose k * m ^ k := by
    have hf : 0 < k.factorial := Nat.factorial_pos k
    have : k.factorial * (m.choose k * n ^ k) ≤ k.factorial * (n.choose k * m ^ k) := by
      calc k.factorial * (m.choose k * n ^ k) = k.factorial * m.choose k * n ^ k := by ring
        _ ≤ k.factorial * n.choose k * m ^ k := hd
        _ = k.factorial * (n.choose k * m ^ k) := by ring
    exact Nat.le_of_mul_le_mul_left this hf
  have hpos : 0 < n.choose k := Nat.choose_pos (hkm.trans hmn)
  have : n.choose k * ((n - k).choose (m - k) * n ^ k) ≤ n.choose k * (n.choose m * m ^ k) := by
    calc n.choose k * ((n - k).choose (m - k) * n ^ k)
        = (n.choose k * (n - k).choose (m - k)) * n ^ k := by ring
      _ = (n.choose m * m.choose k) * n ^ k := by rw [hcm]
      _ = n.choose m * (m.choose k * n ^ k) := by ring
      _ ≤ n.choose m * (n.choose k * m ^ k) := Nat.mul_le_mul_left _ hd'
      _ = n.choose k * (n.choose m * m ^ k) := by ring
  exact Nat.le_of_mul_le_mul_left this hpos

/-- Geometric bound `Σ_{k ≤ j} m^k ≤ 2 m^j` for `m ≥ 2`. -/
theorem geom_le {m : ℕ} (hm : 2 ≤ m) (j : ℕ) : ∑ k ∈ range (j + 1), m ^ k ≤ 2 * m ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [sum_range_succ, pow_succ]
    have : 2 * m ^ j ≤ m ^ j * m := by rw [mul_comm]; exact Nat.mul_le_mul_left _ hm
    nlinarith

/-- `Σ_{4 ≤ k ≤ m} k · m^k ≤ 2 m^(m+1)`. -/
theorem sum_k_pow_le (m : ℕ) : ∑ k ∈ Icc 4 m, k * m ^ k ≤ 2 * m ^ (m + 1) := by
  rcases Nat.lt_or_ge m 4 with hm | hm
  · rw [Icc_eq_empty (by omega)]; simp
  · have h1 : ∑ k ∈ Icc 4 m, k * m ^ k ≤ ∑ k ∈ range (m + 1), m * m ^ k := by
      refine (sum_le_sum (fun k hk => Nat.mul_le_mul_right _ (mem_Icc.1 hk).2)).trans ?_
      exact sum_le_sum_of_subset_of_nonneg (fun k hk => mem_range.2 (by
        have := (mem_Icc.1 hk).2; omega)) (fun _ _ _ => Nat.zero_le _)
    rw [← mul_sum] at h1
    have h2 := geom_le (m := m) (by omega) m
    calc ∑ k ∈ Icc 4 m, k * m ^ k ≤ m * ∑ k ∈ range (m + 1), m ^ k := h1
      _ ≤ m * (2 * m ^ m) := Nat.mul_le_mul_left _ h2
      _ = 2 * m ^ (m + 1) := by ring

end E34
