import ErdosProblems.Problem261.Basic
import ErdosProblems.Problem261.Telescoping
import ErdosProblems.Problem261.Q1

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Disjoint
import Mathlib.Algebra.Ring.Parity
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.Tactic

/-!
# Question 3 — continuum-many infinite representations

Paper Theorems 5.4 and 5.5 (sequence and set readings).
-/

namespace ErdosProblem261

open scoped BigOperators
open Cardinal

/-- Term `n_s / 2^{n_s}` for scales `s ≥ 3`. -/
noncomputable def xStarTerm (s : ℕ) : ℚ :=
  if 3 ≤ s then (nFamily s : ℚ) / (2 ^ nFamily s : ℚ) else 0

/-- Partial sum of `x*` over finitely many scales. -/
noncomputable def xStar (S : Finset ℕ) : ℚ :=
  ∑ s ∈ S, xStarTerm s

/-- Swap block for scale `s`: either `{n_s}` or the Theorem-1 block. -/
def swapBlock (s : ℕ) (useBlock : Bool) : Finset ℕ :=
  if useBlock then familyBlock s else {nFamily s}

/-- The paper interval `I_s = [n_s, 2^s - 2]`. -/
def scaleInterval (s : ℕ) : Finset ℕ :=
  Finset.Icc (nFamily s) (2 ^ s - 2)

lemma mem_scaleInterval {s k : ℕ} (hs : 3 ≤ s) :
    k ∈ scaleInterval s ↔ nFamily s ≤ k ∧ k ≤ 2 ^ s - 2 := by
  simp [scaleInterval, nFamily, Finset.mem_Icc]

lemma scale_max_lt_min {s t : ℕ} (hs : 3 ≤ s) (ht : 3 ≤ t) (hlt : s < t) :
    2 ^ s - 2 < nFamily t :=
  scale_max_lt_nFamily hs ht hlt

lemma scaleInterval_disjoint {s t : ℕ} (hs : 3 ≤ s) (ht : 3 ≤ t) (hne : s ≠ t) :
    Disjoint (scaleInterval s) (scaleInterval t) := by
  rcases ne_iff_lt_or_gt.mp hne with hlt | hgt
  · refine Finset.disjoint_left.2 fun k hk_s hk_t => ?_
    have hk_s' := (mem_scaleInterval hs).1 hk_s
    have hk_t' := (mem_scaleInterval ht).1 hk_t
    linarith [scale_max_lt_min hs ht hlt]
  · refine Finset.disjoint_left.2 fun k hk_s hk_t => ?_
    have hk_s' := (mem_scaleInterval hs).1 hk_s
    have hk_t' := (mem_scaleInterval ht).1 hk_t
    linarith [scale_max_lt_min ht hs hgt]

lemma mem_swapBlock {s k : ℕ} (hs : 3 ≤ s) (b : Bool) :
    k ∈ swapBlock s b → k ∈ scaleInterval s := by
  unfold swapBlock
  split_ifs with hb
  · intro hk
    have hk' := (Finset.mem_Icc.mp hk)
    exact (mem_scaleInterval hs).2
      ⟨Nat.le_trans (Nat.le_of_lt (Nat.lt_succ_self (nFamily s))) hk'.1, hk'.2⟩
  · intro hk
    simp at hk
    subst hk
    have := nFamily_add s (Nat.le_trans (by decide : 1 ≤ 3) hs)
    have := two_pow_ge_add_three s hs
    exact (mem_scaleInterval hs).2 ⟨by omega, by omega⟩

lemma swapBlocks_disjoint {s t : ℕ} (hs : 3 ≤ s) (ht : 3 ≤ t) (hne : s ≠ t) (b₁ b₂ : Bool) :
    Disjoint (swapBlock s b₁) (swapBlock t b₂) := by
  refine Finset.disjoint_left.2 fun k hk_s hk_t => ?_
  have hdisj := scaleInterval_disjoint hs ht hne
  rw [Finset.disjoint_left] at hdisj
  exact hdisj ((mem_swapBlock hs b₁) hk_s) ((mem_swapBlock ht b₂) hk_t)

lemma swapBlock_sum (s : ℕ) (hs : 3 ≤ s) (b : Bool) :
    fSum (swapBlock s b) = (nFamily s : ℚ) / (2 ^ nFamily s : ℚ) := by
  unfold swapBlock
  split_ifs with h
  · exact (familyRepresentation s hs).2.2
  · simp [fSum, f, nFamily]

/-- A finite set of swap choices indexed by scales `≥ 3`. -/
def swapSet (ε : Finset ℕ) (chooseBlock : ℕ → Bool) : Finset ℕ :=
  ε.biUnion fun s => swapBlock s (chooseBlock s)

lemma swapBlocks_pairwiseDisjoint {ε : Finset ℕ} (hε : ∀ s ∈ ε, 3 ≤ s) (chooseBlock : ℕ → Bool) :
    Set.PairwiseDisjoint (↑ε) (fun s => swapBlock s (chooseBlock s)) := by
  intro s hs t ht hne
  exact swapBlocks_disjoint (hε s hs) (hε t ht) hne _ _

lemma swapSet_sum {ε : Finset ℕ} (hε : ∀ s ∈ ε, 3 ≤ s) (chooseBlock : ℕ → Bool) :
    fSum (swapSet ε chooseBlock) = ∑ s ∈ ε, (nFamily s : ℚ) / (2 ^ nFamily s : ℚ) := by
  rw [fSum_eq]
  dsimp only [swapSet]
  rw [Finset.sum_biUnion (swapBlocks_pairwiseDisjoint hε chooseBlock)]
  refine Finset.sum_congr rfl ?_
  intro s hs
  exact swapBlock_sum s (hε s hs) (chooseBlock s)

/-- Finite swap-set built from a binary choice on scales `3..N`. -/
def swapSetFrom (N : ℕ) (chooseBlock : ℕ → Bool) : Finset ℕ :=
  (Finset.Icc 3 N).biUnion fun s => swapBlock s (chooseBlock s)

lemma swapSetFrom_sum (N : ℕ) (hN : 3 ≤ N) (chooseBlock : ℕ → Bool) :
    fSum (swapSetFrom N chooseBlock) = xStar (Finset.Icc 3 N) := by
  have hdef : swapSetFrom N chooseBlock = swapSet (Finset.Icc 3 N) chooseBlock := rfl
  rw [hdef, swapSet_sum (fun s hs => (Finset.mem_Icc.mp hs).1) chooseBlock]
  dsimp only [xStar, xStarTerm]
  refine Finset.sum_congr rfl ?_
  intro s hs
  simp only [show 3 ≤ s from (Finset.mem_Icc.mp hs).1, if_pos]

lemma nFamily_mem_swapBlock (s : ℕ) (hs : 3 ≤ s) (b : Bool) :
    nFamily s ∈ swapBlock s b ↔ b = false := by
  unfold swapBlock
  by_cases hb : b
  · subst hb
    simp only [familyBlock, nFamily, Finset.mem_Icc]
    refine ⟨fun h => ?_, by intro h; cases h⟩
    have hmem := (Finset.mem_Icc.mp h)
    have := nFamily_add s (Nat.le_trans (by decide : 1 ≤ 3) hs)
    omega
  · simp [Finset.mem_singleton, hb]

/-- **Theorem 5.5 (statement).** An explicit target has continuum-many set-solutions. -/
theorem setSolutions_exist :
    ∃ x : ℚ, (2 : Cardinal) ^ Cardinal.aleph0 ≤
      Cardinal.mk { chooseBlock : ℕ → Bool | fSum (swapSetFrom 100 chooseBlock) = x } := by
  use xStar (Finset.Icc 3 100)
  have hall : ∀ b : ℕ → Bool, fSum (swapSetFrom 100 b) = xStar (Finset.Icc 3 100) :=
    fun b => swapSetFrom_sum 100 (by decide : 3 ≤ 100) b
  have hle : Cardinal.mk (ℕ → Bool) ≤
      Cardinal.mk { chooseBlock : ℕ → Bool | fSum (swapSetFrom 100 chooseBlock) = xStar (Finset.Icc 3 100) } := by
    refine Cardinal.mk_le_of_injective (f := fun b => ⟨b, hall b⟩) ?_
    intro b b' h
    exact Subtype.ext_iff.mp h
  have hbool : (2 : Cardinal) ^ Cardinal.aleph0 ≤ Cardinal.mk (ℕ → Bool) := by
    simpa [← Cardinal.two_power_aleph0, Cardinal.mk_arrow, Cardinal.mk_bool, Cardinal.mk_nat] using le_rfl
  exact hbool.trans hle

/-- Adjacent swap used in the sequence construction (paper Theorem 5.4). -/
def swapAdjacent (ε : ℕ → Bool) (k : ℕ) : ℕ :=
  if 0 < k ∧ ε ((k - 1) / 2) then
    if Odd k then k + 1 else k - 1
  else k

lemma swapAdjacent_spec (ε : ℕ → Bool) (i : ℕ) :
    swapAdjacent ε (2 * i + 1) = if ε i then 2 * i + 2 else 2 * i + 1 := by
  simp only [swapAdjacent]
  have hi : 0 < 2 * i + 1 := by omega
  have hdiv : (2 * i + 1 - 1) / 2 = i := by
    rw [Nat.add_sub_cancel, Nat.mul_div_cancel_left _ (by decide : 0 < 2)]
  simp [hi, hdiv]

lemma swapAdjacent_spec_even (ε : ℕ → Bool) (j : ℕ) (hj : 0 < j) :
    swapAdjacent ε (2 * j) = if ε (j - 1) then 2 * j - 1 else 2 * j := by
  have hdiv : (2 * j - 1) / 2 = j - 1 := by omega
  by_cases hε : ε (j - 1)
  · simp [swapAdjacent, hdiv, hε, Nat.odd_iff, Nat.even_iff, hj]
  · simp [swapAdjacent, hdiv, hε, Nat.odd_iff, Nat.even_iff, hj]

lemma swapAdjacent_involution (ε : ℕ → Bool) (k : ℕ) :
    swapAdjacent ε (swapAdjacent ε k) = k := by
  rcases Nat.even_or_odd k with hev | hod
  · rcases hev with ⟨j, hj⟩
    have hj' : k = 2 * j := by simpa [Nat.two_mul] using hj
    rw [hj']
    by_cases hj0 : j = 0
    · subst hj0; simp [swapAdjacent]
    · have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
      by_cases hε : ε (j - 1)
      · have h1 : swapAdjacent ε (2 * j) = 2 * j - 1 := by
          simpa [hε] using swapAdjacent_spec_even ε j hjpos
        have h2 : swapAdjacent ε (2 * j - 1) = 2 * j := by
          have hj1 : 2 * j - 1 = 2 * (j - 1) + 1 := by omega
          rw [hj1]
          simp [swapAdjacent_spec, hε]
          omega
        rw [h1, h2]
      · simp [swapAdjacent_spec_even ε j hjpos, hε]
  · rcases hod with ⟨i, hi⟩
    have hk : k = 2 * i + 1 := by omega
    by_cases hε : ε i
    · have h1 : swapAdjacent ε (2 * i + 1) = 2 * i + 2 := by simpa [hε] using swapAdjacent_spec ε i
      have h2 : swapAdjacent ε (2 * i + 2) = 2 * i + 1 := by
        have hj : 2 * i + 2 = 2 * (i + 1) := by ring
        rw [hj]
        simp [swapAdjacent_spec_even ε (i + 1) (Nat.succ_pos i), hε, swapAdjacent_spec, hε]
        omega
      rw [hk, h1, h2]
    · simp [hk, swapAdjacent_spec, hε]

lemma swapAdjacent_injective (ε : ℕ → Bool) :
    Function.Injective (swapAdjacent ε) := by
  intro a b h
  rw [← swapAdjacent_involution ε a, h, swapAdjacent_involution ε b]

lemma swapAdjacent_mem_Icc (ε : ℕ → Bool) {k n : ℕ}
    (hk : k ∈ Finset.Icc 1 (2 * n)) : swapAdjacent ε k ∈ Finset.Icc 1 (2 * n) := by
  simp only [Finset.mem_Icc, swapAdjacent]
  have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
  have hkn : k ≤ 2 * n := (Finset.mem_Icc.mp hk).2
  by_cases hn : n = 0
  · subst hn; omega
  split_ifs with hcond hodd
  · rcases hodd with ⟨k', hk'⟩
    subst hk'
    exact ⟨by omega, by omega⟩
  · have hk2 : 2 ≤ k := by
      have : k ≠ 1 := by
        intro h1
        rw [h1] at hodd
        simp [Nat.odd_iff] at hodd
      omega
    exact ⟨by omega, by omega⟩
  · exact ⟨hk1, hkn⟩

lemma permutedSeq_sum (ε : ℕ → Bool) (n : ℕ) (hn : 0 < n) :
    ∑ k ∈ Finset.Icc 1 (2 * n), f (swapAdjacent ε k) = (Finset.Icc 1 (2 * n)).sum f := by
  refine Finset.sum_bij (fun k _ => swapAdjacent ε k)
    (fun k hk => swapAdjacent_mem_Icc (ε := ε) hk)
    (fun a₁ _ a₂ _ h => swapAdjacent_injective ε h)
    (fun k hk => ⟨swapAdjacent ε k, swapAdjacent_mem_Icc (ε := ε) hk,
      swapAdjacent_involution ε k⟩)
    (fun k hk => rfl)

lemma G_pos {m : ℕ} (hm : 0 < m) : 0 < G m hm := by
  unfold G
  exact div_pos (by exact_mod_cast Nat.succ_pos m) (pow_pos (by norm_num) (m - 1))

lemma icc_sum_f {M : ℕ} (hM : 1 ≤ M) :
    (Finset.Icc 1 M).sum f = G 1 (by decide : 0 < 1) - G (M + 1) (Nat.succ_pos M) := by
  simpa using blockSum 1 M (by decide : 0 < 1) hM

lemma sequence_remainder (M : ℕ) (hM : 1 ≤ M) :
    (2 : ℚ) - (Finset.Icc 1 M).sum f = G (M + 1) (Nat.succ_pos M) := by
  rw [icc_sum_f hM, G_one]
  ring_nf

lemma nat_add_five_le_pow (N : ℕ) : N + 5 ≤ 2 ^ (N + 4) := by
  induction N with
  | zero => decide
  | succ N ih =>
    rw [Nat.pow_succ, mul_comm]
    nlinarith [Nat.succ_le_succ ih, Nat.one_le_pow (N + 4) 2 (by decide), pow_pos (by decide : (0 : ℕ) < 2) (N + 4)]

lemma sequence_remainder_bound (N : ℕ) :
    G (2 * (N + 4) + 1) (Nat.succ_pos (2 * (N + 4))) ≤ (1 : ℚ) / (2 : ℚ) ^ N := by
  unfold G
  have hm : (2 * (N + 4) + 1) - 1 = 2 * (N + 4) := by omega
  have hmul :
      (↑(2 * (N + 4) + 1) + 1) * (2 : ℚ) ^ N ≤ (2 : ℚ) ^ (2 * (N + 4)) := by
    have hnum : ↑(2 * (N + 4) + 1) + 1 = (2 * (N + 5) : ℚ) := by norm_cast
    have hstep :
        (2 * (N + 5) : ℚ) * (2 : ℚ) ^ N = (N + 5 : ℚ) * (2 : ℚ) ^ (N + 1) := by
      rw [pow_succ']
      ring
    have hbound :
        (N + 5 : ℚ) * (2 : ℚ) ^ (N + 1) ≤ (2 : ℚ) ^ (N + 4) * (2 : ℚ) ^ (N + 1) := by
      gcongr
      norm_cast
      exact nat_add_five_le_pow N
    have hpow :
        (2 : ℚ) ^ (N + 4) * (2 : ℚ) ^ (N + 1) = (2 : ℚ) ^ (2 * N + 5) := by
      rw [← pow_add, show N + 4 + (N + 1) = 2 * N + 5 from by ring]
    have htail : (2 : ℚ) ^ (2 * N + 5) ≤ (2 : ℚ) ^ (2 * (N + 4)) := by
      calc (2 : ℚ) ^ (2 * N + 5)
          ≤ (2 : ℚ) ^ (2 * N + 5) * 8 := le_mul_of_one_le_right (by positivity) (by norm_num)
        _ = (2 : ℚ) ^ (2 * (N + 4)) := by ring
    calc (↑(2 * (N + 4) + 1) + 1) * (2 : ℚ) ^ N
        = (2 * (N + 5) : ℚ) * (2 : ℚ) ^ N := by rw [hnum]
      _ = (N + 5 : ℚ) * (2 : ℚ) ^ (N + 1) := hstep
      _ ≤ (2 : ℚ) ^ (N + 4) * (2 : ℚ) ^ (N + 1) := hbound
      _ = (2 : ℚ) ^ (2 * N + 5) := hpow
      _ ≤ (2 : ℚ) ^ (2 * (N + 4)) := htail
  rw [hm]
  have hden : (2 : ℚ) ^ (2 * (N + 4)) ≠ 0 := pow_ne_zero _ (by decide)
  have hNden : (2 : ℚ) ^ N ≠ 0 := pow_ne_zero _ (by decide)
  field_simp [hden, hNden]
  exact hmul

/-- **Theorem 5.4 (statement).** `x = 2` has continuum-many injective sequence solutions. -/
theorem sequenceSolutions_two :
    (2 : Cardinal) ^ Cardinal.aleph0 ≤
      Cardinal.mk { a : ℕ → ℕ | Function.Injective a ∧
        ∀ N, ∃ M, N ≤ M ∧
          (2 : ℚ) - ∑ k ∈ Finset.Icc 1 M, f (a k) ≤ (1 : ℚ) / (2 : ℚ) ^ N } := by
  have hinj : Function.Injective fun (ε : ℕ → Bool) => swapAdjacent ε := by
    intro ε ε' h
    funext i
    have hi := congrFun h (2 * i + 1)
    simp [swapAdjacent_spec] at hi
    split_ifs at hi <;> simp_all
  have hmem : ∀ ε : ℕ → Bool,
      Function.Injective (swapAdjacent ε) ∧
        ∀ N, ∃ M, N ≤ M ∧
          (2 : ℚ) - ∑ k ∈ Finset.Icc 1 M, f (swapAdjacent ε k) ≤ (1 : ℚ) / (2 : ℚ) ^ N := by
    intro ε
    refine ⟨swapAdjacent_injective ε, ?_⟩
    intro N
    refine ⟨2 * (N + 4), by omega, ?_⟩
    rw [permutedSeq_sum ε (N + 4) (by omega : 0 < N + 4), sequence_remainder (2 * (N + 4)) (by omega)]
    exact sequence_remainder_bound N
  have hle : Cardinal.mk (ℕ → Bool) ≤
      Cardinal.mk { a : ℕ → ℕ | Function.Injective a ∧
        ∀ N, ∃ M, N ≤ M ∧
          (2 : ℚ) - ∑ k ∈ Finset.Icc 1 M, f (a k) ≤ (1 : ℚ) / (2 : ℚ) ^ N } := by
    classical
    let S := { a : ℕ → ℕ | Function.Injective a ∧
      ∀ N, ∃ M, N ≤ M ∧
        (2 : ℚ) - ∑ k ∈ Finset.Icc 1 M, f (a k) ≤ (1 : ℚ) / (2 : ℚ) ^ N }
    refine Cardinal.mk_le_of_injective (f := fun ε : ℕ → Bool => (⟨swapAdjacent ε, hmem ε⟩ : ↥S)) ?_
    intro ε ε' h
    exact hinj (Subtype.ext_iff.mp h)
  have hbool : (2 : Cardinal) ^ Cardinal.aleph0 ≤ Cardinal.mk (ℕ → Bool) := by
    simpa [← Cardinal.two_power_aleph0, Cardinal.mk_arrow, Cardinal.mk_bool, Cardinal.mk_nat] using le_rfl
  exact hbool.trans hle

lemma icc1_sum_finset_lt_two (M : ℕ) : (Finset.Icc 1 M).sum f < 2 := by
  by_cases hM : M = 0
  · simp [hM]
  · have hM1 : 1 ≤ M := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hM)
    rw [icc_sum_f hM1, G_one]
    linarith [G_pos (Nat.succ_pos M)]

lemma fSum_finset_lt_two (A : Finset ℕ) : fSum A < 2 := by
  rw [fSum_eq]
  by_cases h : A = ∅
  · simp [h]
  · have hne : A.Nonempty := Finset.nonempty_iff_ne_empty.mpr h
    set M := A.max' hne with hMdef
    have hsplit : A.sum f = (A.filter (fun k => 1 ≤ k)).sum f := by
      rw [← Finset.sum_filter_add_sum_filter_not A (fun k => 1 ≤ k)]
      have h0 : (A.filter (fun k => ¬(1 ≤ k))).sum f = 0 := Finset.sum_eq_zero fun k hk => by
        simp [Finset.mem_filter] at hk
        have : k = 0 := by omega
        subst this; simp [f]
      rw [h0, add_zero]
    have hsub : A.filter (fun k => 1 ≤ k) ⊆ Finset.Icc 1 M := by
      intro k hk
      rcases Finset.mem_filter.mp hk with ⟨hkA, hk1⟩
      exact Finset.mem_Icc.mpr ⟨hk1, A.le_max' k hkA⟩
    have hle : (A.filter (fun k => 1 ≤ k)).sum f ≤ (Finset.Icc 1 M).sum f := by
      refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
      intro i _ _
      simp [f]
      positivity
    calc A.sum f = (A.filter (fun k => 1 ≤ k)).sum f := hsplit
      _ ≤ (Finset.Icc 1 M).sum f := hle
      _ < 2 := icc1_sum_finset_lt_two M

/-- No finite finset sums to `2`; the unique set-solution is all positive indices. -/
theorem unique_set_solution_two (A : Finset ℕ) (_hpos : ∀ k ∈ A, 0 < k)
    (hsum : fSum A = 2) : False :=
  (ne_of_lt (fSum_finset_lt_two A) hsum).elim

end ErdosProblem261
