module

public import Mathlib.Combinatorics.SimpleGraph.Regularity.Bound

/-!
# E19 — towers of twos and the regularity step bound

`tower2 m` is the tower of `m` twos (`tower2 0 = 1`, `tower2 (m+1) = 2 ^ tower2 m`).
We prove `stepBound n ≤ 2^(3n)`, the sharper `4 · stepBound n ≤ 2^(4n)` (`n ≥ 1`), and hence
`stepBound^[m] n ≤ tower2 (m + j)` whenever `1 ≤ n` and `4 n ≤ tower2 j`; the choice
`j = n + 2` always works.  We also record the lower bound `2^(2^n) ≤ stepBound^[2] n`.
-/

@[expose] public section

namespace E19

open SzemerediRegularity

/-- The tower of twos: `tower2 0 = 1`, `tower2 (m+1) = 2 ^ tower2 m`. -/
def tower2 : ℕ → ℕ
  | 0 => 1
  | m + 1 => 2 ^ tower2 m

@[simp] theorem tower2_zero : tower2 0 = 1 := rfl

theorem tower2_succ (m : ℕ) : tower2 (m + 1) = 2 ^ tower2 m := rfl

theorem tower2_pos (m : ℕ) : 0 < tower2 m := by
  cases m with
  | zero => simp
  | succ m => rw [tower2_succ]; positivity

/-- `2^(k+1) ≤ tower2 (k+1)`. -/
theorem two_pow_le_tower2_succ (k : ℕ) : 2 ^ (k + 1) ≤ tower2 (k + 1) := by
  induction k with
  | zero => simp [tower2_succ]
  | succ k ih =>
    rw [tower2_succ (k + 1)]
    apply Nat.pow_le_pow_right (by norm_num)
    have : k + 2 ≤ 2 ^ (k + 1) := by
      have := Nat.lt_two_pow_self (n := k + 1)
      omega
    omega

theorem tower2_mono : Monotone tower2 := by
  apply monotone_nat_of_le_succ
  intro m
  rw [tower2_succ]
  exact (Nat.lt_two_pow_self).le

/-- **`stepBound n ≤ 2^(3n)`** (for every `n`, in particular for `n ≥ 1`). -/
theorem stepBound_le_two_pow (n : ℕ) : stepBound n ≤ 2 ^ (3 * n) := by
  unfold stepBound
  have h1 : n ≤ 2 ^ n := (Nat.lt_two_pow_self).le
  have h2 : (4 : ℕ) ^ n = 2 ^ (2 * n) := by rw [pow_mul]; norm_num
  rw [h2, show 3 * n = n + 2 * n by ring, pow_add]
  exact Nat.mul_le_mul_right _ h1

theorem four_mul_le_four_pow (n : ℕ) (hn : 1 ≤ n) : 4 * n ≤ 4 ^ n := by
  induction n with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; norm_num
    · have := ih h
      rw [pow_succ]
      omega

/-- `4 · stepBound n ≤ 2^(4n)` for `n ≥ 1`. -/
theorem four_mul_stepBound_le (n : ℕ) (hn : 1 ≤ n) : 4 * stepBound n ≤ 2 ^ (4 * n) := by
  unfold stepBound
  have h := four_mul_le_four_pow n hn
  have h2 : (2 : ℕ) ^ (4 * n) = 4 ^ n * 4 ^ n := by
    rw [← mul_pow, pow_mul]; norm_num
  rw [h2, ← mul_assoc]
  exact Nat.mul_le_mul_right _ h

theorem one_le_stepBound (n : ℕ) (hn : 1 ≤ n) : 1 ≤ stepBound n :=
  le_trans hn (le_stepBound n)

/-- **Tower bound for the iterates**, invariant form: if `1 ≤ n` and `4n ≤ tower2 j` then
`4 · stepBound^[m] n ≤ tower2 (m + j)`. -/
theorem four_mul_iterate_le_tower2 (m : ℕ) :
    ∀ n j : ℕ, 1 ≤ n → 4 * n ≤ tower2 j → 4 * stepBound^[m] n ≤ tower2 (m + j) := by
  induction m with
  | zero => intro n j _ h; simpa using h
  | succ m ih =>
    intro n j hn h
    rw [Function.iterate_succ_apply, show m + 1 + j = m + (j + 1) by ring]
    apply ih _ _ (one_le_stepBound n hn)
    rw [tower2_succ]
    exact le_trans (four_mul_stepBound_le n hn) (Nat.pow_le_pow_right (by norm_num) h)

/-- **`stepBound^[m] n ≤ tower2 (m + j)`** whenever `1 ≤ n` and `4n ≤ tower2 j`. -/
theorem iterate_le_tower2 (m n j : ℕ) (hn : 1 ≤ n) (h : 4 * n ≤ tower2 j) :
    stepBound^[m] n ≤ tower2 (m + j) := by
  have := four_mul_iterate_le_tower2 m n j hn h
  omega

/-- The explicit offset `L(n) = n + 2` satisfies `4n ≤ tower2 (L n)`. -/
theorem four_mul_le_tower2_add_two (n : ℕ) : 4 * n ≤ tower2 (n + 2) := by
  have h1 := two_pow_le_tower2_succ (n + 1)
  have h2 : n ≤ 2 ^ n := (Nat.lt_two_pow_self).le
  have h3 : (2 : ℕ) ^ (n + 1 + 1) = 4 * 2 ^ n := by rw [pow_succ, pow_succ]; ring
  rw [h3] at h1
  have h4 : tower2 (n + 1 + 1) = tower2 (n + 2) := rfl
  omega

/-- **`stepBound^[m] n ≤ tower2 (m + n + 2)`** for `n ≥ 1` (explicit `L(n) = n + 2`). -/
theorem iterate_le_tower2_explicit (m n : ℕ) (hn : 1 ≤ n) :
    stepBound^[m] n ≤ tower2 (m + (n + 2)) :=
  iterate_le_tower2 m n (n + 2) hn (four_mul_le_tower2_add_two n)

/-! ## Lower bounds for the iterates -/

theorem le_iterate_stepBound (m n : ℕ) : n ≤ stepBound^[m] n := by
  induction m generalizing n with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply]
    exact le_trans (le_stepBound n) (ih _)

theorem iterate_stepBound_mono_left (n : ℕ) : Monotone (fun m => stepBound^[m] n) := by
  apply monotone_nat_of_le_succ
  intro m
  rw [Function.iterate_succ_apply']
  exact le_stepBound _

theorem two_pow_le_stepBound (n : ℕ) (hn : 1 ≤ n) : 2 ^ n ≤ stepBound n := by
  unfold stepBound
  calc 2 ^ n ≤ 4 ^ n := Nat.pow_le_pow_left (by norm_num) n
    _ = 1 * 4 ^ n := (one_mul _).symm
    _ ≤ n * 4 ^ n := Nat.mul_le_mul_right _ hn

/-- `2^(2^n) ≤ stepBound (stepBound n)` for `n ≥ 1`. -/
theorem two_pow_two_pow_le_iterate_two (n : ℕ) (hn : 1 ≤ n) :
    2 ^ (2 ^ n) ≤ stepBound^[2] n := by
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id]
  have h1 := two_pow_le_stepBound n hn
  have h2 := two_pow_le_stepBound (stepBound n) (one_le_stepBound n hn)
  exact le_trans (Nat.pow_le_pow_right (by norm_num) h1) h2

/-- `2^(2^K) ≤ stepBound^[m] n` whenever `2 ≤ m`, `1 ≤ n` and `K ≤ n`. -/
theorem two_pow_two_pow_le_iterate (m n K : ℕ) (hm : 2 ≤ m) (hn : 1 ≤ n) (hK : K ≤ n) :
    2 ^ (2 ^ K) ≤ stepBound^[m] n :=
  le_trans (Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_right (by norm_num) hK))
    (le_trans (two_pow_two_pow_le_iterate_two n hn) (iterate_stepBound_mono_left n hm))

/-- `tower2 (j + 7) = 2^(2^tower2 (j + 5))`. -/
theorem tower2_add_seven (j : ℕ) : tower2 (j + 7) = 2 ^ (2 ^ tower2 (j + 5)) := rfl

end E19

end
