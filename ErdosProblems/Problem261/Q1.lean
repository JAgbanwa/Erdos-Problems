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

lemma succ_le_pow (n : ℕ) (hn : 1 ≤ n) : n + 1 ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
      rw [pow_succ]
      omega

lemma nFamily_add (s : ℕ) (hs : 1 ≤ s) : nFamily s + s + 1 = 2 ^ s := by
  simp [nFamily]
  have : s + 1 ≤ 2 ^ s := succ_le_pow s hs
  omega

lemma nFamily_succ_pos (s : ℕ) (hs : 3 ≤ s) : 0 < nFamily s + 1 := by
  have := nFamily_add s (Nat.le_trans (by decide : 1 ≤ 3) hs)
  omega

lemma two_pow_sub_one_pos (s : ℕ) (hs : 3 ≤ s) : 0 < 2 ^ s - 1 := by
  have := two_pow_ge_add_three s hs
  omega

lemma familyBlock_upper (s : ℕ) (hs : 3 ≤ s) : nFamily s + 1 ≤ 2 ^ s - 2 := by
  simp [nFamily]
  have := two_pow_ge_add_three s hs
  omega

lemma nat_two_mul_sub_succ (x s : ℕ) (hx0 : 1 ≤ x) (hx1 : s + 1 ≤ x) :
    2 * x - (s + 2) = x - (s + 1) + (x - 1) := by omega

lemma two_pow_sub_succ_eq (s : ℕ) (hs : 1 ≤ s) :
    2 * 2 ^ s - (s + 1) = 2 ^ s - s + (2 ^ s - 1) := by
  induction s, hs using Nat.le_induction with
  | base => decide
  | succ s hs _ =>
      have h1 : 1 ≤ 2 ^ s * 2 := by
        have hpow : 2 ≤ 2 ^ s := by
          calc 2 = 2 ^ 1 := by decide
            _ ≤ 2 ^ s := Nat.pow_le_pow_right (by decide) hs
        omega
      have h2 : s + 1 ≤ 2 ^ s * 2 := by
        have := succ_le_pow s hs
        omega
      simpa only [pow_succ] using nat_two_mul_sub_succ (2 ^ s * 2) s h1 h2

lemma two_pow_sub_strictMono {s t : ℕ} (hs : 1 ≤ s) (hst : s < t) : 2 ^ s - s < 2 ^ t - t := by
  have step : ∀ s, 1 ≤ s → 2 ^ s - s < 2 ^ (s + 1) - (s + 1) := by
    intro s hs
    have hpos : 0 < 2 ^ s - 1 := by
      have h2 : 2 ≤ 2 ^ s := by
        calc 2 ≤ 2 ^ 1 := by decide
          _ ≤ 2 ^ s := Nat.pow_le_pow_right (by decide) hs
      exact Nat.sub_pos_of_lt (Nat.lt_of_lt_of_le (by decide : 1 < 2) h2)
    have hEq := two_pow_sub_succ_eq s hs
    rw [pow_succ, mul_comm, hEq]
    exact Nat.lt_add_of_pos_right hpos
  rcases Nat.exists_eq_add_of_lt hst with ⟨d, rfl⟩
  suffices ∀ d, 2 ^ s - s < 2 ^ (s + d + 1) - (s + d + 1) from this d
  intro d
  induction d with
  | zero => exact step s hs
  | succ d ih => exact lt_trans ih (step (s + d + 1) (by omega))

lemma two_pow_sub_ge_one {s : ℕ} (hs : 3 ≤ s) : 1 ≤ 2 ^ s - s := by
  have := two_pow_ge_add_three s hs
  omega

lemma nFamily_strictMono {s t : ℕ} (hs : 3 ≤ s) (hst : s < t) :
    nFamily s < nFamily t := by
  simp only [nFamily]
  have hmono := two_pow_sub_strictMono (Nat.le_trans (by decide : 1 ≤ 3) hs) hst
  have hs1 := two_pow_sub_ge_one hs
  have ht1 := two_pow_sub_ge_one (Nat.le_trans hs (Nat.le_of_lt hst))
  omega

lemma scale_max_lt_nFamily {s t : ℕ} (hs : 3 ≤ s) (ht : 3 ≤ t) (hlt : s < t) :
    2 ^ s - 2 < nFamily t := by
  have hns := nFamily_add s (Nat.le_trans (by decide : 1 ≤ 3) hs)
  have hbase : 2 ^ s - 2 < nFamily (s + 1) := by
    simp only [nFamily]
    omega
  rcases Nat.eq_or_lt_of_le (Nat.succ_le_of_lt hlt) with rfl | htlt
  · exact hbase
  · exact Nat.lt_trans hbase (nFamily_strictMono (Nat.le_trans hs (by omega)) htlt)

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
  rw [h]
  simp only [G, hM]

/-- The rigid power-of-two identity underlying Theorem 1. -/
lemma familyPowerNat (s : ℕ) (hs : 3 ≤ s) :
    (2 : ℕ) * 2 ^ (2 ^ s - 2) = 2 ^ s * 2 ^ (nFamily s) := by
  have hexp : nFamily s + s + 1 = 2 ^ s := nFamily_add s (Nat.le_trans (by decide : 1 ≤ 3) hs)
  have hinner : (2 ^ s - 2) + 1 = 2 ^ s - 1 := by
    have hle : 2 ≤ 2 ^ s := by
      calc 2 ≤ 2 ^ 3 := by decide
        _ ≤ 2 ^ s := Nat.pow_le_pow_right (by decide) hs
    omega
  calc
    (2 : ℕ) * 2 ^ (2 ^ s - 2) = 2 ^ ((2 ^ s - 2) + 1) := by rw [pow_succ, mul_comm]
    _ = 2 ^ (2 ^ s - 1) := by rw [hinner]
    _ = 2 ^ (s + nFamily s) := by congr 1; omega
    _ = 2 ^ s * 2 ^ (nFamily s) := pow_add 2 s (nFamily s)

lemma familySum_eq (s : ℕ) (hs : 3 ≤ s) :
    fSum (familyBlock s) = (nFamily s : ℚ) / (2 ^ nFamily s : ℚ) := by
  rw [fSum_eq, familyBlock_blockSum s hs]
  have hp := familyPowerNat s hs
  have hsucc₁ : nFamily s + 1 - 1 = nFamily s := by omega
  have hsucc₂ : 2 ^ s - 1 - 1 = 2 ^ s - 2 := by
    have hle : 2 ≤ 2 ^ s := by
      calc 2 ≤ 2 ^ 3 := by decide
        _ ≤ 2 ^ s := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hs
    omega
  have hG₁ : G (nFamily s + 1) (nFamily_succ_pos s hs) =
      (nFamily s + 2 : ℚ) / 2 ^ (nFamily s) := by
    simp only [G]
    rw [show (nFamily s + 1 - 1 : ℕ) = nFamily s from hsucc₁]
    simp only [nFamily]
    field_simp
    norm_cast
  have hG₂ : G (2 ^ s - 1) (two_pow_sub_one_pos s hs) =
      (2 ^ s : ℚ) / 2 ^ (2 ^ s - 2) := by
    simp only [G, hsucc₂]
    field_simp
    norm_cast
    have htop : (2 ^ s - 1 + 1 : ℕ) = 2 ^ s := by
      have hle : 1 ≤ 2 ^ s := by
        calc (1 : ℕ) ≤ 2 ^ 3 := by decide
          _ ≤ 2 ^ s := Nat.pow_le_pow_right (by decide) hs
      exact Nat.sub_add_cancel hle
    omega
  rw [hG₁, hG₂]
  have hcore : (2 : ℚ) / 2 ^ (nFamily s) = (2 ^ s : ℚ) / 2 ^ (2 ^ s - 2) := by
    field_simp
    norm_cast
    rw [mul_comm (2 ^ (nFamily s))]
    exact hp
  have hnum :
      ((nFamily s + 2 : ℚ) / 2 ^ (nFamily s) - (nFamily s : ℚ) / 2 ^ (nFamily s)) =
        (2 : ℚ) / 2 ^ (nFamily s) := by
    field_simp [pow_pos (by norm_num : (0 : ℚ) < 2 ^ (nFamily s))]
    ring
  linarith [hcore, hnum]

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

lemma nat_sub_add_cancel {a b c : ℕ} (hbc : b ≤ a) (hab : a = b + c) : a - b = c := by omega

lemma two_pow_gt_three_mul (E : ℕ) (hE : 5 ≤ E) : 3 * E < 2 ^ E + 1 := by
  induction E, hE using Nat.le_induction with
  | base => decide
  | succ E hE ih =>
      rw [pow_succ]
      nlinarith [ih, pow_pos (show (0 : ℕ) < 2 by decide) E]

lemma two_pow_odd_mod_three (E : ℕ) (hodd : Odd E) : 2 ^ E % 3 = 2 := by
  rcases hodd with ⟨k, rfl⟩
  have h : ∀ k, 2 ^ (2 * k + 1) % 3 = 2 := by
    intro k
    induction k with
    | zero => decide
    | succ k ih =>
        rw [show 2 * (k + 1) + 1 = 2 * k + 3 by ring]
        rw [show 2 ^ (2 * k + 3) = 2 ^ (2 * k + 1) * (2 ^ 2) by
          conv_lhs => rw [show 2 * k + 3 = 2 * k + 1 + 2 from by ring, pow_add]]
        rw [Nat.mul_mod, ih, show (2 ^ 2 : ℕ) % 3 = 1 by decide]
  exact h k

lemma two_pow_ge_five {E : ℕ} (hE : 5 ≤ E) : 5 ≤ 2 ^ E := by
  calc 5 ≤ 2 ^ 5 := by decide
    _ ≤ 2 ^ E := Nat.pow_le_pow_right (by decide) hE

lemma secondFamilyB_ge_E (E : ℕ) (hE : 1 ≤ E) : E ≤ secondFamilyB E + 1 := by
  unfold secondFamilyB
  by_cases h5 : 5 ≤ E
  · have h32 : 2 ^ 5 ≤ 2 ^ E := Nat.pow_le_pow_right (by decide : (1 : ℕ) ≤ 2) h5
    have hlt : 5 < 2 ^ E := Nat.lt_of_lt_of_le (by decide : (5 : ℕ) < 32) h32
    have : 0 < 2 ^ E - 5 := Nat.sub_pos_of_lt hlt
    have hkey := two_pow_gt_three_mul E h5
    omega
  · have : E ≤ 4 := by omega
    interval_cases E <;> decide

lemma nat_sub_add_eq (a c : ℕ) (hac : c ≤ a + 1) (hc : 1 ≤ c) :
    a - (a + 1 - c) + 1 = c := by omega

lemma secondFamily_b_sub_a (E : ℕ) (hE : 1 ≤ E) :
    secondFamilyB E - secondFamilyA E + 1 = E := by
  by_cases h5 : 5 ≤ E
  · have hBE := secondFamilyB_ge_E E hE
    simp only [secondFamilyA, secondFamilyB]
    exact nat_sub_add_eq (secondFamilyB E) E hBE hE
  · have : E ≤ 4 := by omega
    interval_cases E <;> decide

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
  have hkey := two_pow_gt_three_mul E hE
  unfold secondFamilyA secondFamilyB at hpow ⊢
  omega

lemma secondFamily_b_pos (E : ℕ) (hE : 5 ≤ E) (hodd : Odd E) : 0 < secondFamilyB E := by
  have hle := two_pow_ge_five hE
  have hlt : 5 < 2 ^ E := by
    calc (5 : ℕ) < 2 ^ 5 := by decide
      _ ≤ 2 ^ E := Nat.pow_le_pow_right (by decide) hE
  have hdiv := secondFamily_div_three E hodd
  have : 0 < 2 ^ E - 5 := Nat.sub_pos_of_lt hlt
  simp only [secondFamilyB]
  omega

lemma secondFamily_interior_lower (E : ℕ) (hE : 5 ≤ E) (hodd : Odd E) :
    secondFamilyA E + 1 ≤ secondFamilyB E - 1 := by
  have h3 : 3 ≤ E := Nat.le_trans (by decide : (3 : ℕ) ≤ 5) hE
  have hBE := secondFamilyB_ge_E E (Nat.le_trans (by decide : 1 ≤ 5) hE)
  have hkey : secondFamilyA E + 2 ≤ secondFamilyB E := by
    simp only [secondFamilyA]
    have _ := secondFamilyB_ge_E E (Nat.le_trans (by decide : 1 ≤ 5) hE)
    omega
  have hB := secondFamily_b_pos E hE hodd
  have h1 : 1 ≤ secondFamilyB E := by linarith
  exact (Nat.le_sub_iff_add_le h1).2 hkey

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
  have hab : a ≤ b := by
    by_contra h
    have hba : b < a := lt_of_not_ge h
    have hsub : b - a = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_lt hba)
    have hE1 : E = 1 := by omega
    have h2 : (2 : ℕ) ^ E = 2 := by rw [hE1, pow_one]
    rw [h2] at hpow
    have : 3 ≤ 3 * b + 2 := by nlinarith
    omega
  have ha : 0 < (2 : ℚ) ^ a := pow_pos (by norm_num) a
  have hb : 0 < (2 : ℚ) ^ b := pow_pos (by norm_num) b
  have hc : 0 < (2 : ℚ) ^ (b - 1) := pow_pos (by norm_num) (b - 1)
  have hpow_nat : (3 * b + 2) * 2 ^ a = 2 ^ (b + 1) := by
    calc (3 * b + 2) * 2 ^ a = 2 ^ (b - a + 1) * 2 ^ a := by rw [hpow']
      _ = 2 ^ ((b - a + 1) + a) := by rw [← pow_add 2 (b - a + 1) a]
      _ = 2 ^ (b + 1) := by congr 1; omega
  have hn : a * 2 ^ b + b * 2 ^ a + 2 * (b + 1) * 2 ^ a = (a + 2) * 2 ^ b := by
    have hsum : b * 2 ^ a + 2 * (b + 1) * 2 ^ a = (3 * b + 2) * 2 ^ a := by ring
    calc a * 2 ^ b + b * 2 ^ a + 2 * (b + 1) * 2 ^ a
        = a * 2 ^ b + (b * 2 ^ a + 2 * (b + 1) * 2 ^ a) := by ring
      _ = a * 2 ^ b + (3 * b + 2) * 2 ^ a := by rw [hsum]
      _ = a * 2 ^ b + 2 ^ (b + 1) := by rw [hpow_nat]
      _ = (a + 2) * 2 ^ b := by
          rw [show 2 ^ (b + 1) = 2 * 2 ^ b from by rw [pow_succ, mul_comm]]
          ring
  calc (a : ℚ) / 2 ^ a + (b : ℚ) / 2 ^ b
      _ = ((a : ℚ) * 2 ^ b + (b : ℚ) * 2 ^ a) / (2 ^ a * 2 ^ b) := by
            field_simp [ha.ne', hb.ne']
      _ = ((a + 2 : ℚ) * 2 ^ b - 2 * (b + 1 : ℚ) * 2 ^ a) / (2 ^ a * 2 ^ b) := by
            congr 1
            have hle : 2 * (b + 1) * 2 ^ a ≤ (a + 2) * 2 ^ b := by
              calc 2 * (b + 1) * 2 ^ a ≤ (3 * b + 2) * 2 ^ a :=
                  Nat.mul_le_mul_right _ (by nlinarith)
                _ = 2 ^ (b + 1) := by rw [hpow_nat]
                _ = 2 * 2 ^ b := by rw [pow_succ, mul_comm]
                _ ≤ (a + 2) * 2 ^ b := Nat.mul_le_mul_right _ (by nlinarith)
            have hnat : a * 2 ^ b + b * 2 ^ a = (a + 2) * 2 ^ b - 2 * (b + 1) * 2 ^ a := by omega
            exact_mod_cast hnat
      _ = (a + 2 : ℚ) / 2 ^ a - (b + 1 : ℚ) / 2 ^ (b - 1) := by
            have hb1 : b - 1 + 1 = b := by omega
            rw [div_sub_div]
            · field_simp [ha.ne', hb.ne', hc.ne']
              have hpow : (2 : ℚ) ^ b = 2 * (2 : ℚ) ^ (b - 1) := by
                nth_rw 1 [show b = (b - 1) + 1 from by omega]
                rw [pow_succ (2) (b - 1), mul_comm]
              rw [hpow]
              ring
            · exact ha.ne'
            · exact hc.ne'

lemma secondFamily_GIdentity {a b E : ℕ} (hapos : 0 < a) (hbpos : 0 < b)
    (hG1 : 0 < a + 1) (hG2 : 0 < b + 1) (hdiff : b - a + 1 = E) (hpow : 3 * b + 2 = 2 ^ E) :
    G a hapos - G (a + 1) hG1 + (G b hbpos - G (b + 1) hG2) = G (a + 1) hG1 - G b hbpos := by
  have hf₁ : G a hapos - G (a + 1) hG1 = f a := G_sub_G_succ a hapos
  have hf₂ : G b hbpos - G (b + 1) hG2 = f b := G_sub_G_succ b hbpos
  have hr := secondFamily_ratIdentity hapos hbpos hdiff hpow
  rw [hf₁, hf₂]
  have hG_a1 : G (a + 1) hG1 = ((a + 2 : ℚ)) / 2 ^ a := by
    simp only [G]
    rw [show (a + 1 - 1 : ℕ) = a from by omega]
    field_simp
    norm_cast
  have hG_b : G b hbpos = ((b + 1 : ℚ)) / 2 ^ (b - 1) := by simp only [G]
  rw [hG_a1, hG_b]
  exact hr

/-- Remark 2: odd `E ≥ 5` yields a two-point / block identity (paper Remark 2). -/
theorem secondFamily_representation (E : ℕ) (hE : 5 ≤ E) (hodd : Odd E) :
    fSum {secondFamilyA E, secondFamilyB E} = fSum (secondFamilyInterior E) := by
  have hne : secondFamilyA E ≠ secondFamilyB E := by
    simp [secondFamilyA, secondFamilyB]
    have hle := two_pow_ge_five hE
    omega
  have hapos := secondFamily_a_pos E hE hodd
  have hbpos := secondFamily_b_pos E hE hodd
  have hdiff := secondFamily_b_sub_a E (Nat.le_trans (by decide : 1 ≤ 5) hE)
  have hpow := secondFamily_power E hE hodd
  rw [fSum_pair hne, fSum_eq, secondFamily_interior_blockSum E hE hodd]
  rw [← G_sub_G_succ (secondFamilyA E) hapos, ← G_sub_G_succ (secondFamilyB E) hbpos]
  exact secondFamily_GIdentity hapos hbpos (Nat.succ_pos (secondFamilyA E))
    (Nat.succ_pos (secondFamilyB E)) hdiff hpow

end ErdosProblem261
