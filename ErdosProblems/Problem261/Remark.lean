import ErdosProblems.Problem261.Basic
import ErdosProblems.Problem261.Telescoping

import Mathlib.Tactic

/-!
# Paper Remark 1 — indices in a representation must exceed `n`
-/

namespace ErdosProblem261

@[simp] lemma f_one : f 1 = (1 : ℚ) / 2 := by norm_num [f]

@[simp] lemma f_two : f 2 = (1 : ℚ) / 2 := by norm_num [f]

lemma two_mul_lt_pow {n : ℕ} (hn : 3 ≤ n) : 2 * n < 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
      rw [pow_succ, mul_comm]
      nlinarith [ih, pow_pos (show (0 : ℕ) < 2 by decide) n]

lemma target_lt_half {n : ℕ} (hn : 3 ≤ n) : (n : ℚ) / 2 ^ n < (1 : ℚ) / 2 := by
  have h := two_mul_lt_pow hn
  have hpos : 0 < (2 : ℚ) ^ n := pow_pos (by norm_num) n
  field_simp
  rw [mul_comm ((n : ℚ)) 2]
  exact_mod_cast h

lemma f_pred_gt_target {n : ℕ} (hn : 3 ≤ n) :
    (n : ℚ) / 2 ^ n < f (n - 1) := by
  unfold f
  have hexp : (2 : ℚ) ^ n = 2 * 2 ^ (n - 1) := by
    have hnat : (2 : ℕ) ^ n = 2 * 2 ^ (n - 1) := by
      conv_lhs => rw [show n = (n - 1) + 1 from by omega]
      rw [pow_succ, mul_comm]
    exact_mod_cast hnat
  rw [hexp]
  field_simp
  have : n < 2 * (n - 1) := by omega
  exact_mod_cast this

lemma f_succ_lt {k : ℕ} (hk : 2 ≤ k) : f (k + 1) < f k := by
  unfold f
  rw [show (2 : ℚ) ^ (k + 1) = 2 * 2 ^ k from by rw [pow_succ, mul_comm]]
  field_simp
  norm_cast
  omega

lemma f_succ_le {k : ℕ} (hk : 2 ≤ k) : f (k + 1) ≤ f k :=
  le_of_lt (f_succ_lt hk)

lemma f_antitone {a b : ℕ} (ha : 2 ≤ a) (hab : a ≤ b) : f b ≤ f a := by
  suffices h : ∀ b, a ≤ b → f b ≤ f a from h b hab
  intro b hb
  induction hb with
  | refl => rfl
  | step hab ih =>
      exact le_trans (f_succ_le (Nat.le_trans ha hab)) ih

lemma f_term_ge_pred {n k : ℕ} (hn : 3 ≤ n) (hk : k ≤ n - 1) (hkpos : 0 < k) :
    f (n - 1) ≤ f k := by
  have htop : f (n - 1) ≤ f 2 := f_antitone (by decide : 2 ≤ 2) (by omega : 2 ≤ n - 1)
  match k with
  | 0 => exact hkpos.false.elim
  | 1 => simpa [f_one, f_two] using htop
  | 2 => exact htop
  | k + 3 => exact f_antitone (by omega : 2 ≤ k + 3) hk

lemma f_gt_target_of_le_pred {n k : ℕ} (hn : 3 ≤ n) (hk : k ≤ n - 1) (hkpos : 0 < k) :
    (n : ℚ) / 2 ^ n < f k :=
  lt_of_lt_of_le (f_pred_gt_target hn) (f_term_ge_pred hn hk hkpos)

lemma fSum_gt_pair_mem {S : Finset ℕ} {k j : ℕ} (hk : k ∈ S) (hj : j ∈ S) (hne : k ≠ j)
    (hpos : ∀ x ∈ S, 0 < x) : f k < fSum S := by
  have hjpos : 0 < f j := f_pos j (hpos j hj)
  have hj_le : f j ≤ (S.erase k).sum f :=
    Finset.single_le_sum (fun x hx => le_of_lt (f_pos x (hpos x (Finset.mem_of_mem_erase hx))))
      (Finset.mem_erase.mpr ⟨Ne.symm hne, hj⟩)
  have : f k < S.sum f := by
    calc
      f k < f k + f j := lt_add_of_pos_right _ hjpos
      _ ≤ f k + (S.erase k).sum f := by
        convert add_le_add_right hj_le (f k) using 1
      _ = S.sum f := by
        rw [← Finset.sum_erase_add S f hk]
        ac_rfl
  simpa [fSum] using this

lemma fSum_gt_mem {S : Finset ℕ} {k : ℕ} (hk : k ∈ S) (hcard : 2 ≤ S.card)
    (hpos : ∀ j ∈ S, 0 < j) : f k < fSum S := by
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hcard
  by_cases hka : a = k
  · exact fSum_gt_pair_mem hk hb (hka.symm ▸ hab) hpos
  · exact fSum_gt_pair_mem hk ha (Ne.symm hka) hpos

lemma not_mem_of_eq_target {n : ℕ} {S : Finset ℕ} (hrep : HasFiniteRepresentation n S) :
    n ∉ S := by
  intro hn
  have hfn : f n = (n : ℚ) / 2 ^ n := by simp [f]
  have hsum := hrep.2.2
  rw [show fSum S = S.sum f from rfl, ← Finset.sum_erase_add _ _ hn, hfn] at hsum
  have hrest : fSum (S.erase n) = 0 := by
    change (S.erase n).sum f = 0
    linarith
  have hpos : 0 < fSum (S.erase n) := by
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hrep.1
    have hexists : ∃ j ∈ S.erase n, 0 < f j := by
      by_cases hna : a = n
      · refine ⟨b, ?_, f_pos b (hrep.2.1 b hb)⟩
        exact Finset.mem_erase.mpr ⟨fun h => hab (hna.trans h.symm), hb⟩
      · by_cases hnb : b = n
        · refine ⟨a, ?_, f_pos a (hrep.2.1 a ha)⟩
          exact Finset.mem_erase.mpr ⟨hna, ha⟩
        · refine ⟨b, ?_, f_pos b (hrep.2.1 b hb)⟩
          exact Finset.mem_erase.mpr ⟨hnb, hb⟩
    obtain ⟨j, hj, hjpos⟩ := hexists
    rw [show fSum (S.erase n) = (S.erase n).sum f from rfl]
    exact lt_of_lt_of_le hjpos
      (Finset.single_le_sum (fun x hx => le_of_lt (f_pos x (hrep.2.1 x (Finset.mem_of_mem_erase hx)))) hj)
  rw [hrest] at hpos
  exact hpos.false

/-- **Remark 1.** For `n ≥ 3`, every index in a representation with at least two terms
exceeds `n`. -/
theorem indicesAbove_n_of_rep {n : ℕ} (hn : 3 ≤ n) {S : Finset ℕ}
    (hrep : HasFiniteRepresentation n S) : ∀ k ∈ S, n < k := by
  intro k hk
  by_contra hle
  have hkn : k ≤ n := le_of_not_gt hle
  by_cases hn' : k = n
  · exact not_mem_of_eq_target hrep (hn' ▸ hk)
  · have hk' : k ≤ n - 1 := by omega
    have hkpos : 0 < k := hrep.2.1 k hk
    have hgt : (n : ℚ) / 2 ^ n < f k := f_gt_target_of_le_pred hn hk' hkpos
    have hsum : f k < fSum S := fSum_gt_mem hk hrep.1 hrep.2.1
    linarith [hrep.2.2]

lemma f_eq_half_of_le_two {k : ℕ} (hk : k ≤ 2) (hkpos : 0 < k) : f k = (1 : ℚ) / 2 := by
  have : k = 1 ∨ k = 2 := by omega
  rcases this with rfl | rfl
  · exact f_one
  · exact f_two

lemma target_eq_half {n : ℕ} (hn : n = 1 ∨ n = 2) : (n : ℚ) / 2 ^ n = (1 : ℚ) / 2 := by
  rcases hn with rfl | rfl <;> norm_num

theorem indicesAbove_n_of_rep_small {n : ℕ} (hn : n = 1 ∨ n = 2) {S : Finset ℕ}
    (hrep : HasFiniteRepresentation n S) : ∀ k ∈ S, 2 < k := by
  intro k hk
  by_contra hle
  have hkle : k ≤ 2 := by omega
  have hfk : f k = (1 : ℚ) / 2 := f_eq_half_of_le_two hkle (hrep.2.1 k hk)
  have hlt : f k < fSum S := fSum_gt_mem hk hrep.1 hrep.2.1
  linarith [hlt, hfk, hrep.2.2, target_eq_half hn]

end ErdosProblem261
