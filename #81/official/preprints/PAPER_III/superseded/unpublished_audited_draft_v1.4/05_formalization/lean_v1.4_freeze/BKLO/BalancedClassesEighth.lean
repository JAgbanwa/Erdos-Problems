/-
# Balanced classes, to an **eighth**

`BKLO.exists_balanced_classes` (`BKLO/BalancedClasses.lean`) extracts pairwise disjoint classes of
`t` places in each of which every bad set `T v` occupies at most a **quarter** of the places.  That
quarter is what `BKLO.IsGridSharpReservoir.classBalancedSharp` records, and through it the reserved
link of the two-sided design is equalized at `c = q - q / 4` places of every class — exactly three
quarters, which saturates `IsGridTwoSidedReservoir.linkClassGe` and leaves the quarter condition of
`BKLO.exists_cell_balanced_leftovers` no room at all for a perturbation
(`BKLO/AX2CellStepRepair.lean`).

This file sharpens the quarter to an **eighth**.  The bad sets are a tenth of the pool and the pool
a class is drawn from is at least nine tenths of it, so the mean of `|T v ∩ C i|` is at most `t / 9`
and an eighth is the last constant above it that the union bound can reach.  It is reached by
running `BKLO.exists_powersetCard_avoiding` at the target `y = t / 8 + 1`, with the deviation
parameter `ρ = 19 / 20` in place of `9 / 10` and the exponent `k = 2 ⌊t / 512⌋` in place of
`2 ⌊t / 32⌋`:

  `(19 / 20) · (31 / 256) · (255 / 256) = 0.1145… > 1 / 9`,

which is the ratio condition of the tail bound.  The price is the smallness hypothesis, which is a
factor `16` in the exponent weaker than the one of `BKLO.exists_balanced_classes`.

* `BKLO.exists_balanced_classes_eighth` — the classes, balanced to an eighth.

Everything here is `sorry`-free.
-/
import BKLO.BalancedClasses

open Finset

namespace BKLO

variable {V : Type*} [DecidableEq V]

/-- **Balanced classes, to an eighth.**  As `BKLO.exists_balanced_classes`, with every bad set
occupying at most an *eighth* of every class instead of a quarter, at the cost of a stronger
smallness hypothesis: `|W| (19/20)^{2⌊t/512⌋} < 1`. -/
theorem exists_balanced_classes_eighth {W P : Finset V} {T : V → Finset V} {g t : ℕ}
    (hTcard : ∀ v ∈ W, 10 * (T v).card ≤ P.card)
    (hvol : 10 * (g * t) ≤ P.card) (ht : 0 < t)
    (hsmall : (W.card : ℝ) * (19 / 20 : ℝ) ^ (2 * (t / 512)) < 1) :
    ∃ C : ℕ → Finset V, (∀ i < g, C i ⊆ P) ∧ (∀ i < g, (C i).card = t) ∧
      (∀ i < g, ∀ j < g, i ≠ j → Disjoint (C i) (C j)) ∧
      (∀ v ∈ W, ∀ i < g, 8 * ((T v ∩ C i).card) ≤ t) := by
  classical
  revert hvol
  induction g with
  | zero =>
    intro _
    exact ⟨fun _ => ∅, fun i hi => absurd hi (Nat.not_lt_zero i),
      fun i hi => absurd hi (Nat.not_lt_zero i), fun i hi => absurd hi (Nat.not_lt_zero i),
      fun v _ i hi => absurd hi (Nat.not_lt_zero i)⟩
  | succ g ih =>
    intro hvol
    have hvol' : 10 * (g * t) ≤ P.card := by nlinarith only [hvol]
    obtain ⟨C, hCP, hCcard, hCdisj, hCbal⟩ := ih hvol'
    -- the pool left over by the first `g` classes
    set U : Finset V := (Finset.range g).biUnion C with hUdef
    set A : Finset V := P \ U with hAdef
    have hUP : U ⊆ P := by
      intro z hz
      obtain ⟨i, hi, hzi⟩ := Finset.mem_biUnion.1 hz
      exact hCP i (Finset.mem_range.1 hi) hzi
    have hUcard : U.card ≤ g * t := by
      calc U.card ≤ ∑ i ∈ Finset.range g, (C i).card := Finset.card_biUnion_le
        _ = ∑ _i ∈ Finset.range g, t :=
            Finset.sum_congr rfl fun i hi => hCcard i (Finset.mem_range.1 hi)
        _ = g * t := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
    have hAcardeq : A.card = P.card - U.card := Finset.card_sdiff_of_subset hUP
    have hAcard : 10 * A.card ≥ 9 * P.card + 10 * t := by
      have h1 : U.card ≤ P.card := Finset.card_le_card hUP
      have : 10 * (g * t + t) ≤ P.card := by nlinarith only [hvol]
      omega
    -- the parameters of the tail bound
    set k : ℕ := 2 * (t / 512) with hkdef
    set y : V → ℕ := fun _ => t / 8 + 1 with hydef
    have hkt : k ≤ t := by simp only [hkdef]; omega
    have hky : ∀ v ∈ W, k ≤ y v := by
      intro v _; simp only [hydef, hkdef]; omega
    have htA : t ≤ A.card := by omega
    have hkA : k ≤ A.card := le_trans hkt htA
    have hratio : ∀ v ∈ W, ((T v ∩ A).card : ℝ) * (t : ℝ)
        ≤ (19 / 20 : ℝ) * (((y v + 1 - k : ℕ) : ℝ) * ((A.card + 1 - k : ℕ) : ℝ)) := by
      intro v hv
      -- the three integer facts
      have f1 : 256 * (y v + 1 - k) ≥ 31 * t := by simp only [hydef, hkdef]; omega
      have f2 : 256 * (A.card + 1 - k) ≥ 255 * A.card := by simp only [hkdef]; omega
      have f4 : (T v ∩ A).card ≤ (T v).card := Finset.card_le_card Finset.inter_subset_left
      have f3 : 9 * (T v ∩ A).card + t ≤ A.card := by
        have h5 := hTcard v hv
        omega
      -- their real forms
      have g1 : (256 : ℝ) * ((y v + 1 - k : ℕ) : ℝ) ≥ 31 * (t : ℝ) := by exact_mod_cast f1
      have g2 : (256 : ℝ) * ((A.card + 1 - k : ℕ) : ℝ) ≥ 255 * (A.card : ℝ) := by
        exact_mod_cast f2
      have g3 : (9 : ℝ) * ((T v ∩ A).card : ℝ) + (t : ℝ) ≤ (A.card : ℝ) := by exact_mod_cast f3
      have g4 : (t : ℝ) ≤ (A.card : ℝ) := by exact_mod_cast htA
      have ht0 : (0 : ℝ) ≤ (t : ℝ) := Nat.cast_nonneg _
      have hA0 : (0 : ℝ) ≤ (A.card : ℝ) := Nat.cast_nonneg _
      have hX0 : (0 : ℝ) ≤ ((T v ∩ A).card : ℝ) := Nat.cast_nonneg _
      have hY0 : (0 : ℝ) ≤ ((y v + 1 - k : ℕ) : ℝ) := Nat.cast_nonneg _
      have hA'0 : (0 : ℝ) ≤ ((A.card + 1 - k : ℕ) : ℝ) := Nat.cast_nonneg _
      have hprod : (31 * (t : ℝ) / 256) * (255 * (A.card : ℝ) / 256)
          ≤ ((y v + 1 - k : ℕ) : ℝ) * ((A.card + 1 - k : ℕ) : ℝ) := by
        have hl : (31 * (t : ℝ) / 256) ≤ ((y v + 1 - k : ℕ) : ℝ) := by linarith
        have hr : (255 * (A.card : ℝ) / 256) ≤ ((A.card + 1 - k : ℕ) : ℝ) := by linarith
        exact mul_le_mul hl hr (by positivity) hY0
      nlinarith only [hprod, mul_le_mul_of_nonneg_right g3 ht0, sq_nonneg ((t : ℝ))]
    obtain ⟨S, hS, hSgood⟩ :=
      exists_powersetCard_avoiding (A := A) (W := W) (T := fun v => T v ∩ A) (y := y)
        (t := t) (k := k) (ρ := 19 / 20) (fun v _ => Finset.inter_subset_right) hkt hky hkA htA
        hratio hsmall
    obtain ⟨hSA, hScard⟩ := Finset.mem_powersetCard.1 hS
    refine ⟨fun i => if i = g then S else C i, ?_, ?_, ?_, ?_⟩
    · intro i hi
      by_cases hig : i = g
      · simp only [if_pos hig]
        exact hSA.trans Finset.sdiff_subset
      · simp only [if_neg hig]
        exact hCP i (by omega)
    · intro i hi
      by_cases hig : i = g
      · simp only [if_pos hig]; exact hScard
      · simp only [if_neg hig]; exact hCcard i (by omega)
    · intro i hi j hj hij
      have hCU : ∀ n < g, Disjoint (C n) S := by
        intro n hn
        refine Finset.disjoint_left.2 fun z hz hzS => ?_
        have : z ∈ U := Finset.mem_biUnion.2 ⟨n, Finset.mem_range.2 hn, hz⟩
        exact (Finset.mem_sdiff.1 (hSA hzS)).2 this
      by_cases hig : i = g
      · have hjg : j ≠ g := by omega
        simp only [if_pos hig, if_neg hjg]
        exact (hCU j (by omega)).symm
      · by_cases hjg : j = g
        · simp only [if_neg hig, if_pos hjg]
          exact hCU i (by omega)
        · simp only [if_neg hig, if_neg hjg]
          exact hCdisj i (by omega) j (by omega) hij
    · intro v hv i hi
      by_cases hig : i = g
      · simp only [if_pos hig]
        have hinter : T v ∩ S = T v ∩ A ∩ S := by
          rw [Finset.inter_assoc]
          congr 1
          exact (Finset.inter_eq_right.2 hSA).symm
        have hgood := hSgood v hv
        simp only [hydef] at hgood
        rw [hinter]
        omega
      · simp only [if_neg hig]
        exact hCbal v hv i (by omega)

end BKLO
