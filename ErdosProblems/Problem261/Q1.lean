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
  have hM : 2 ^ s - 2 + 1 = 2 ^ s - 1 := by
    have hle : 2 ≤ 2 ^ s := by
      calc 2 ≤ 2 ^ 3 := by decide
        _ ≤ 2 ^ s := Nat.pow_le_pow_right (by decide) hs
    omega
  have h := blockSum (nFamily s + 1) (2 ^ s - 2) (nFamily_succ_pos s hs)
    (familyBlock_upper s hs)
  simp only [G] at h ⊢
  rw [hM]
  exact h

/-- The rigid power-of-two identity underlying Theorem 1. -/
lemma familyPowerNat (s : ℕ) (hs : 3 ≤ s) :
    (2 : ℕ) * 2 ^ (2 ^ s - 2) = 2 ^ s * 2 ^ (nFamily s) := by
  have hexp : s + nFamily s + 1 = 2 ^ s := nFamily_add s (Nat.le_trans (by decide : 1 ≤ 3) hs)
  have hinner : (2 ^ s - 2) + 1 = 2 ^ s - 1 := by omega
  calc
    (2 : ℕ) * 2 ^ (2 ^ s - 2) = 2 ^ ((2 ^ s - 2) + 1) := by rw [mul_comm, ← pow_succ]
    _ = 2 ^ (2 ^ s - 1) := by congr 1; exact hinner
    _ = 2 ^ (s + nFamily s) := by congr 1; omega
    _ = 2 ^ s * 2 ^ (nFamily s) := pow_add 2 s (nFamily s)

lemma familySum_eq (s : ℕ) (hs : 3 ≤ s) :
    fSum (familyBlock s) = (nFamily s : ℚ) / (2 ^ nFamily s : ℚ) := by
  rw [fSum_eq, familyBlock_blockSum s hs]
  have hexp : s + nFamily s + 1 = 2 ^ s := nFamily_add s (Nat.le_trans (by decide : 1 ≤ 3) hs)
  have hp := familyPowerNat s hs
  simp only [G, nFamily]
  field_simp
  ring_nf
  norm_cast
  rw [← hexp, hp]
  ring

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

lemma secondFamily_b_sub_a (E : ℕ) :
    secondFamilyB E - secondFamilyA E + 1 = E := by
  simp [secondFamilyA, secondFamilyB]; omega

lemma two_pow_odd_mod_three (E : ℕ) (hodd : Odd E) : 2 ^ E % 3 = 2 := by
  rcases hodd with ⟨k, rfl⟩
  induction k with
  | zero => decide
  | succ k ih =>
      rw [pow_add, pow_mul, mul_mod, ih, show 2 ^ 2 % 3 = 1 from by decide]
      omega

lemma two_pow_ge_five {E : ℕ} (hE : 5 ≤ E) : 5 ≤ 2 ^ E := by
  calc 5 ≤ 2 ^ 5 := by decide
    _ ≤ 2 ^ E := Nat.pow_le_pow_right (by decide) hE

lemma secondFamily_div_three (E : ℕ) (hodd : Odd E) : 3 ∣ 2 ^ E - 5 := by
  have h := two_pow_odd_mod_three E hodd
  omega

lemma secondFamily_power (E : ℕ) (hE : 5 ≤ E) (hodd : Odd E) :
    3 * secondFamilyB E + 2 = 2 ^ E := by
  have hdiv := secondFamily_div_three E hodd
  have hle : 5 ≤ 2 ^ E := two_pow_ge_five hE
  simp only [secondFamilyB]
  have h := Nat.mul_div_cancel' hdiv
  calc
    3 * ((2 ^ E - 5) / 3 + 1) + 2 = 3 * ((2 ^ E - 5) / 3) + 3 + 2 := by ring
    _ = (2 ^ E - 5) + 5 := by rw [h]
    _ = 2 ^ E := Nat.sub_add_cancel hle

lemma secondFamily_a_pos (E : ℕ) (hE : 5 ≤ E) (hodd : Odd E) : 0 < secondFamilyA E := by
  have hpow := secondFamily_power E hE hodd
  have hle : 5 ≤ 2 ^ E := two_pow_ge_five hE
  have hdiv := secondFamily_div_three E hodd
  have h := Nat.mul_div_cancel' hdiv
  have hb : 1 ≤ (2 ^ E - 5) / 3 + 1 := by
    have : 0 < 2 ^ E - 5 := Nat.sub_pos_of_lt (lt_of_lt_of_le (by decide : 5 < 2 ^ 5) hle)
    omega
  simp only [secondFamilyA, secondFamilyB]
  rw [h]
  omega

lemma secondFamily_b_pos (E : ℕ) (hE : 5 ≤ E) (hodd : Odd E) : 0 < secondFamilyB E := by
  have hle : 5 ≤ 2 ^ E := two_pow_ge_five hE
  have hdiv := secondFamily_div_three E hodd
  have h := Nat.mul_div_cancel' hdiv
  have : 0 < 2 ^ E - 5 := Nat.sub_pos_of_lt (lt_of_lt_of_le (by decide : 5 < 2 ^ 5) hle)
  simp only [secondFamilyB]
  rw [h]
  omega

lemma secondFamily_interior_lower (E : ℕ) (hE : 5 ≤ E) (hodd : Odd E) :
    secondFamilyA E + 1 ≤ secondFamilyB E - 1 := by
  have hle : 5 ≤ 2 ^ E := two_pow_ge_five hE
  have hdiv := secondFamily_div_three E hodd
  have h := Nat.mul_div_cancel' hdiv
  simp only [secondFamilyA, secondFamilyB, h]
  omega

lemma secondFamily_interior_blockSum (E : ℕ) (hE : 5 ≤ E) (hodd : Odd E) :
    (secondFamilyInterior E).sum f =
      G (secondFamilyA E + 1) (Nat.succ_pos (secondFamilyA E)) -
        G (secondFamilyB E) (secondFamily_b_pos E hE hodd) := by
  simp only [secondFamilyInterior]
  exact blockSum (secondFamilyA E + 1) (secondFamilyB E - 1)
    (Nat.succ_pos (secondFamilyA E)) (secondFamily_interior_lower E hE hodd)

lemma secondFamily_ratIdentity {a b E : ℕ} (hapos : 0 < a) (hbpos : 0 < b)
    (hdiff : b - a + 1 = E) (hpow : 3 * b + 2 = 2 ^ E) :
    (a : ℚ) / 2 ^ a + (b : ℚ) / 2 ^ b =
      ((a + 2 : ℚ)) / 2 ^ a - ((b + 1 : ℚ)) / 2 ^ (b - 1) := by
  have hpow' : 3 * b + 2 = 2 ^ (b - a + 1) := hdiff ▸ hpow
  have ha : 0 < (2 : ℚ) ^ a := pow_pos (by norm_num) a
  have hb : 0 < (2 : ℚ) ^ b := pow_pos (by norm_num) b
  have hc : 0 < (2 : ℚ) ^ (b - 1) := pow_pos (by norm_num) (b - 1)
  field_simp [ha.ne', hb.ne', hc.ne']
  norm_cast
  rw [hpow']
  omega

lemma secondFamily_GIdentity {a b E : ℕ} (hapos : 0 < a) (hbpos : 0 < b)
    (hG1 : 0 < a + 1) (hG2 : 0 < b + 1) (hdiff : b - a + 1 = E) (hpow : 3 * b + 2 = 2 ^ E) :
    G a hapos - G (a + 1) hG1 + (G b hbpos - G (b + 1) hG2) = G (a + 1) hG1 - G b hbpos := by
  have hsucc : ∀ n, n + 1 - 1 = n := fun n => by omega
  simp only [G, hsucc, show (a + 1) + 1 = a + 2 from rfl, show (b + 1) + 1 = b + 2 from rfl]
  have hleft :
      (a + 1 : ℚ) / 2 ^ (a - 1) - (a + 2 : ℚ) / 2 ^ a +
        ((b + 1 : ℚ) / 2 ^ (b - 1) - (b + 2 : ℚ) / 2 ^ b) =
      (a : ℚ) / 2 ^ a + (b : ℚ) / 2 ^ b := by
    have ha' : 0 < (2 : ℚ) ^ a := pow_pos (by norm_num) a
    have hb' : 0 < (2 : ℚ) ^ b := pow_pos (by norm_num) b
    have hc' : 0 < (2 : ℚ) ^ (b - 1) := pow_pos (by norm_num) (b - 1)
    have hd' : 0 < (2 : ℚ) ^ (a - 1) := pow_pos (by norm_num) (a - 1)
    field_simp [ha'.ne', hb'.ne', hc'.ne', hd'.ne']
    ring
  rw [hleft]
  exact secondFamily_ratIdentity hapos hbpos hdiff hpow

/-- Remark 2: odd `E ≥ 5` yields a two-point / block identity (paper Remark 2). -/
theorem secondFamily_representation (E : ℕ) (hE : 5 ≤ E) (hodd : Odd E) :
    fSum {secondFamilyA E, secondFamilyB E} = fSum (secondFamilyInterior E) := by
  have hne : secondFamilyA E ≠ secondFamilyB E := by
    simp [secondFamilyA, secondFamilyB]
    have hle := two_pow_ge_five hE
    omega
  have hapos := secondFamily_a_pos E hE hodd
  have hbpos := secondFamily_b_pos E hE hodd
  have hdiff := secondFamily_b_sub_a E
  have hpow := secondFamily_power E hE hodd
  rw [fSum_pair hne, fSum_eq, secondFamily_interior_blockSum E hE hodd]
  rw [← G_sub_G_succ (secondFamilyA E) hapos, ← G_sub_G_succ (secondFamilyB E) hbpos]
  exact secondFamily_GIdentity hapos hbpos (Nat.succ_pos (secondFamilyA E))
    (Nat.succ_pos (secondFamilyB E)) hdiff hpow

end ErdosProblem261
