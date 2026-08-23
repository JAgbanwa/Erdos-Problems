/-
# Balanced classes inside a level.

The reservoir of §10 has to be *spread*: no vertex of the next level `W'` may be reserved for more
than an `ε`-fraction of the outer vertices, and yet any two outer vertices must keep `Ω(|W|)`
reserved common neighbours.  The construction of `BKLO/ReservoirDesign.lean` gets both from a
partition-like family of small **balanced classes** inside `W'`: pairwise disjoint sets `C i`, all
of the same size `t`, in each of which every vertex of `W` has at most a quarter of its
non-neighbours share, i.e. `4|T v ∩ C i| ≤ t` where `T v` is the non-neighbourhood of `v`.

Such a family exists as soon as the classes take up at most a tenth of `W'`, each `T v` is at most
a tenth of `W'`, and `t` is large enough for the union bound: this is
`BKLO.exists_balanced_classes`, proved by extracting the classes one at a time with the moment
tail bound `BKLO.exists_powersetCard_avoiding` of `BKLO/LevelSampling.lean` applied to the
remaining pool, which is always at least nine tenths of `W'`.

Everything here is `sorry`-free.
-/
import BKLO.LevelSampling

open Finset

namespace BKLO

variable {V : Type*} [DecidableEq V]

/-- **Balanced classes.**  Given a pool `P`, a family of "bad" sets `T v ⊆ P` indexed by `v ∈ W`,
each of size at most `|P|/10`, and sizes `g`, `t` with `10gt ≤ |P|`, there are `g` pairwise
disjoint subsets of `P` of size `t` in each of which every bad set occupies at most a quarter of
the places — provided `t` is large enough that the union bound `|W|(9/10)^{2⌊t/32⌋} < 1` holds. -/
theorem exists_balanced_classes {W P : Finset V} {T : V → Finset V} {g t : ℕ}
    (hTcard : ∀ v ∈ W, 10 * (T v).card ≤ P.card)
    (hvol : 10 * (g * t) ≤ P.card) (ht : 0 < t)
    (hsmall : (W.card : ℝ) * (9 / 10 : ℝ) ^ (2 * (t / 32)) < 1) :
    ∃ C : ℕ → Finset V, (∀ i < g, C i ⊆ P) ∧ (∀ i < g, (C i).card = t) ∧
      (∀ i < g, ∀ j < g, i ≠ j → Disjoint (C i) (C j)) ∧
      (∀ v ∈ W, ∀ i < g, 4 * ((T v ∩ C i).card) ≤ t) := by
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
    set k : ℕ := 2 * (t / 32) with hkdef
    set y : V → ℕ := fun _ => t / 4 + 1 with hydef
    have hkt : k ≤ t := by simp only [hkdef]; omega
    have hky : ∀ v ∈ W, k ≤ y v := by
      intro v _; simp only [hydef, hkdef]; omega
    have htA : t ≤ A.card := by omega
    have hkA : k ≤ A.card := le_trans hkt htA
    have hratio : ∀ v ∈ W, ((T v ∩ A).card : ℝ) * (t : ℝ)
        ≤ (9 / 10 : ℝ) * (((y v + 1 - k : ℕ) : ℝ) * ((A.card + 1 - k : ℕ) : ℝ)) := by
      intro v hv
      have f1 : 3 * t ≤ 16 * (y v + 1 - k) := by simp only [hydef, hkdef]; omega
      have f2 : 15 * A.card ≤ 16 * (A.card + 1 - k) := by simp only [hkdef]; omega
      have f4 : (T v ∩ A).card ≤ (T v).card := Finset.card_le_card Finset.inter_subset_left
      have g1 : (3 : ℝ) * (t : ℝ) ≤ 16 * ((y v + 1 - k : ℕ) : ℝ) := by exact_mod_cast f1
      have g2 : (15 : ℝ) * (A.card : ℝ) ≤ 16 * ((A.card + 1 - k : ℕ) : ℝ) := by exact_mod_cast f2
      have g3 : (9 : ℝ) * (P.card : ℝ) ≤ 10 * (A.card : ℝ) := by
        have : 9 * P.card ≤ 10 * A.card := by omega
        exact_mod_cast this
      have g4 : ((T v ∩ A).card : ℝ) ≤ ((T v).card : ℝ) := by exact_mod_cast f4
      have g5 : (10 : ℝ) * ((T v).card : ℝ) ≤ (P.card : ℝ) := by exact_mod_cast hTcard v hv
      have hY0 : (0 : ℝ) ≤ ((y v + 1 - k : ℕ) : ℝ) := Nat.cast_nonneg _
      have hA0 : (0 : ℝ) ≤ ((A.card + 1 - k : ℕ) : ℝ) := Nat.cast_nonneg _
      have ht0 : (0 : ℝ) ≤ (t : ℝ) := Nat.cast_nonneg _
      have hAc0 : (0 : ℝ) ≤ (A.card : ℝ) := Nat.cast_nonneg _
      have hX0 : (0 : ℝ) ≤ ((T v ∩ A).card : ℝ) := Nat.cast_nonneg _
      have hprod : (3 * (t : ℝ) / 16) * (15 * (A.card : ℝ) / 16)
          ≤ ((y v + 1 - k : ℕ) : ℝ) * ((A.card + 1 - k : ℕ) : ℝ) := by
        have hl : (3 * (t : ℝ) / 16) ≤ ((y v + 1 - k : ℕ) : ℝ) := by linarith
        have hr : (15 * (A.card : ℝ) / 16) ≤ ((A.card + 1 - k : ℕ) : ℝ) := by linarith
        exact mul_le_mul hl hr (by positivity) hY0
      nlinarith only [hprod, mul_le_mul_of_nonneg_right g4 ht0,
        mul_le_mul_of_nonneg_right g5 ht0, mul_le_mul_of_nonneg_right g3 ht0]
    obtain ⟨S, hS, hSgood⟩ :=
      exists_powersetCard_avoiding (A := A) (W := W) (T := fun v => T v ∩ A) (y := y)
        (t := t) (k := k) (ρ := 9 / 10) (fun v _ => Finset.inter_subset_right) hkt hky hkA htA
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
