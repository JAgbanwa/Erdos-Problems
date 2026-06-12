import ErdosProblems.Problem261.Basic
import ErdosProblems.Problem261.Telescoping

import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Set.Card
import Mathlib.Tactic

/-!
# Question 1 — infinitely many representable `n`

Theorem 1 and the second telescoping family (Remark 2).
-/

namespace ErdosProblem261

@[simp] lemma fSum_eq (S : Finset ℕ) : fSum S = S.sum f := rfl

lemma two_pow_ge_add_three (s : ℕ) (hs : 3 ≤ s) : s + 3 ≤ 2 ^ s := by
  induction s, hs using Nat.le_induction with
  | base => decide
  | succ s hs ih =>
      rw [pow_succ, mul_comm]
      nlinarith [ih, pow_pos (show (0 : ℕ) < 2 by decide) s]

lemma nFamily_sub_valid (s : ℕ) (hs : 3 ≤ s) : s + 1 ≤ 2 ^ s := by
  have := two_pow_ge_add_three s hs
  omega

lemma nFamily_add (s : ℕ) (hs : 1 ≤ s) : nFamily s + s + 1 = 2 ^ s := by
  simp [nFamily]
  have : s + 1 ≤ 2 ^ s := by
    cases s with
    | zero => omega
    | succ s =>
      exact Nat.succ_le_of_lt (Nat.lt_pow_self (by decide) (s + 1))
  omega

lemma nFamily_succ_pos (s : ℕ) (hs : 3 ≤ s) : 0 < nFamily s + 1 := by
  have := nFamily_add s (Nat.le_trans (by decide : 1 ≤ 3) hs)
  rw [this]
  exact pow_pos (by decide) s

lemma two_pow_sub_one_pos (s : ℕ) (hs : 3 ≤ s) : 0 < 2 ^ s - 1 := by
  have := two_pow_ge_add_three s hs
  omega

lemma familyBlock_upper (s : ℕ) (hs : 3 ≤ s) : nFamily s + 1 ≤ 2 ^ s - 2 := by
  simp [nFamily]
  have := two_pow_ge_add_three s hs
  omega

lemma two_pow_sub_strictMono {s t : ℕ} (hs : 1 ≤ s) (hst : s < t) : 2 ^ s - s < 2 ^ t - t := by
  have step : ∀ s, 1 ≤ s → 2 ^ s - s < 2 ^ (s + 1) - (s + 1) := by
    intro s hs
    rw [pow_succ, mul_comm]
    omega
  rcases Nat.exists_eq_add_of_lt hst with ⟨k, rfl⟩
  induction k with
  | zero => exact step s hs
  | succ k ih => exact lt_trans ih (step (s + k + 1) (by omega))

lemma two_pow_sub_ge_one {s : ℕ} (hs : 3 ≤ s) : 1 ≤ 2 ^ s - s := by
  have := two_pow_ge_add_three s hs
  omega

lemma nFamily_strictMono {s t : ℕ} (hs : 3 ≤ s) (hst : s < t) :
    nFamily s < nFamily t := by
  simp only [nFamily]
  exact Nat.sub_lt_sub_right
    (two_pow_sub_strictMono (Nat.le_trans (by decide : 1 ≤ 3) hs) hst)
    (two_pow_sub_ge_one hs)

lemma nFamily_eq_iff {s t : ℕ} (hs : 3 ≤ s) (ht : 3 ≤ t) :
    nFamily s = nFamily t ↔ s = t := by
  simp only [nFamily]
  constructor
  · intro h
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact (nFamily_strictMono hs hlt).ne h
    · exact (nFamily_strictMono ht hgt).ne h.symm
  · intro h; rw [h]

lemma familyBlock_two_le (s : ℕ) (hs : 3 ≤ s) : 2 ≤ (familyBlock s).card := by
  have hp := two_pow_ge_add_three s hs
  have h1 : nFamily s + 1 ∈ familyBlock s := by
    simp [familyBlock, nFamily, Finset.mem_Icc]; omega
  have h2 : nFamily s + 2 ∈ familyBlock s := by
    simp [familyBlock, nFamily, Finset.mem_Icc]; omega
  have hsub : ({nFamily s + 1, nFamily s + 2} : Finset ℕ) ⊆ familyBlock s := by
    intro x hx; simp at hx
    rcases hx with hx | hx <;> simp [familyBlock, nFamily, Finset.mem_Icc, hx] <;> omega
  have hcard : ({nFamily s + 1, nFamily s + 2} : Finset ℕ).card = 2 := by
    rw [Finset.card_pair (by omega)]
  exact Nat.le_trans (by rw [hcard]) (Finset.card_le_card hsub)

lemma familyBlock_pos (s : ℕ) (hs : 3 ≤ s) {k : ℕ} (hk : k ∈ familyBlock s) : 0 < k := by
  simp [familyBlock, nFamily, Finset.mem_Icc] at hk
  have := two_pow_ge_add_three s hs; omega

lemma familyBlock_blockSum (s : ℕ) (hs : 3 ≤ s) :
    (familyBlock s).sum f =
      G (nFamily s + 1) (nFamily_succ_pos s hs) -
        G (2 ^ s - 1) (two_pow_sub_one_pos s hs) := by
  simp only [familyBlock]
  rw [blockSum (nFamily s + 1) (2 ^ s - 2) (nFamily_succ_pos s hs)
    (familyBlock_upper s hs), show (2 ^ s - 2 + 1 : ℕ) = 2 ^ s - 1 by omega]

/-- The rigid power-of-two identity underlying Theorem 1. -/
lemma familyPowerNat (s : ℕ) (_hs : 3 ≤ s) :
    (2 : ℕ) * 2 ^ (2 ^ s - 2) = 2 ^ s * 2 ^ (nFamily s) := by
  have hexp : s + nFamily s = 2 ^ s - 1 := by
    simp [nFamily]; omega
  calc
    (2 : ℕ) * 2 ^ (2 ^ s - 2) = 2 ^ ((2 ^ s - 2) + 1) := by
      rw [mul_comm, ← pow_succ]
    _ = 2 ^ (2 ^ s - 1) := by congr 1; omega
    _ = 2 ^ (s + nFamily s) := by rw [hexp]
    _ = 2 ^ s * 2 ^ (nFamily s) := pow_add 2 s (nFamily s)

lemma familySum_eq (s : ℕ) (hs : 3 ≤ s) :
    fSum (familyBlock s) = (nFamily s : ℚ) / (2 ^ nFamily s : ℚ) := by
  rw [fSum_eq, familyBlock_blockSum s hs]
  simp only [G, nFamily]
  have hp := familyPowerNat s hs
  field_simp
  ring_nf
  exact_mod_cast hp

/-- **Theorem 1.** Block-sum identity for the explicit family (paper Theorem 4.1). -/
theorem familyRepresentation (s : ℕ) (hs : 3 ≤ s) :
    HasFiniteRepresentation (nFamily s) (familyBlock s) := by
  refine ⟨familyBlock_two_le s hs, fun k hk => familyBlock_pos s hs hk, ?_⟩
  exact familySum_eq s hs

theorem infinitelyMany_question1 :
    {n : ℕ | Question1 n}.Infinite := by
  have hinj : Set.InjOn nFamily (Set.Ici 3) := by
    intro s hs t ht h
    exact (nFamily_eq_iff hs ht).mp h
  have hsub : nFamily '' Set.Ici 3 ⊆ {n | Question1 n} := by
    intro n hn
    rcases hn with ⟨s, hs, rfl⟩
    exact ⟨familyBlock s, familyRepresentation s hs⟩
  exact Set.Infinite.mono hsub (Set.Infinite.image hinj (Set.Ici_infinite 3))

theorem secondFamily_representation_five :
    fSum {6, 10} = fSum (Finset.Icc 7 9) := by
  rw [fSum_pair (by decide), fSum_eq]; simp [f]; native_decide

theorem secondFamily_representation_seven :
    fSum {36, 42} = fSum (Finset.Icc 37 41) := by
  rw [fSum_pair (by decide), fSum_eq]; simp [f]; native_decide

theorem secondFamily_representation_nine :
    fSum {162, 170} = fSum (Finset.Icc 163 169) := by
  rw [fSum_pair (by decide), fSum_eq]; simp [f]; native_decide

theorem secondFamily_representation_eleven :
    fSum {672, 682} = fSum (Finset.Icc 673 681) := by
  rw [fSum_pair (by decide), fSum_eq]; simp [f]; native_decide

theorem secondFamily_representation_thirteen :
    fSum {2718, 2730} = fSum (Finset.Icc 2719 2729) := by
  rw [fSum_pair (by decide), fSum_eq]; simp [f]; native_decide

/-- Remark 2: odd `E ≥ 5` yields a two-point / block identity (paper Remark 2). -/
theorem secondFamily_representation (E : ℕ) (hE : 5 ≤ E) (hodd : Odd E) :
    fSum {secondFamilyA E, secondFamilyB E} = fSum (secondFamilyInterior E) := by
  sorry

end ErdosProblem261
