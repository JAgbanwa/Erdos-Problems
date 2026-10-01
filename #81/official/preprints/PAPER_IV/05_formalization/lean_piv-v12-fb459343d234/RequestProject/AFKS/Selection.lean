module

public import Mathlib
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.Positivity

/-!
# Averaging over a random choice of one element in each set

For sets `t i` (`i ∈ ι`) we average over all choice functions `x` with `x i ∈ t i` (the elements
of `Fintype.piFinset t`). This is the "choose a random vertex in every part" step of the proof of
Corollary 4.2 of AFKS. The only fact we need is that, for `i ≠ j`, the pair `(x i, x j)` is
uniformly distributed on `t i × t j`.
-/

@[expose] public section

open Finset Fintype

namespace AFKS

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {V : Type*} [DecidableEq V]

/-- The number of choice functions with prescribed values at two distinct coordinates. -/
theorem card_fiber_mul (t : ι → Finset V) {i j : ι} (hij : i ≠ j) {a b : V} (ha : a ∈ t i)
    (hb : b ∈ t j) :
    (∑ x ∈ piFinset t, (if x i = a ∧ x j = b then (1 : ℝ) else 0)) * (#(t i) * #(t j)) =
      #(piFinset t) := by
  let g : ι → V → ℝ := fun l c =>
    if l = i then (if c = a then 1 else 0) else if l = j then (if c = b then 1 else 0) else 1
  have hprod : ∀ x : ι → V, ∏ l, g l (x l) = if x i = a ∧ x j = b then (1 : ℝ) else 0 := by
    intro x
    rw [← Finset.mul_prod_erase _ _ (mem_univ i),
      ← Finset.mul_prod_erase _ _ (mem_erase.2 ⟨hij.symm, mem_univ j⟩)]
    have hrest : ∏ l ∈ (univ.erase i).erase j, g l (x l) = 1 := by
      refine Finset.prod_eq_one fun l hl => ?_
      obtain ⟨hlj, hli⟩ : l ≠ j ∧ l ≠ i := by simpa using hl
      simp [g, hli, hlj]
    rw [hrest]
    simp only [g, if_pos rfl, if_neg hij.symm, mul_one]
    by_cases h1 : x i = a <;> by_cases h2 : x j = b <;> simp [h1, h2]
  have hsum : ∀ l, ∑ c ∈ t l, g l c =
      if l = i then 1 else if l = j then 1 else (#(t l) : ℝ) := by
    intro l
    by_cases hli : l = i
    · subst hli; simp [g, ha]
    · by_cases hlj : l = j
      · subst hlj; simp [g, hli, hb]
      · simp [g, hli, hlj]
  have key := Finset.prod_univ_sum t g
  simp_rw [hprod, hsum] at key
  have hj' : j ∈ univ.erase i := mem_erase.2 ⟨hij.symm, mem_univ j⟩
  have e1 : ∏ l, (if l = i then (1 : ℝ) else if l = j then 1 else (#(t l) : ℝ)) =
      ∏ l ∈ (univ.erase i).erase j, (#(t l) : ℝ) := by
    rw [← Finset.mul_prod_erase _ _ (mem_univ i), ← Finset.mul_prod_erase _ _ hj']
    rw [if_pos rfl, if_neg hij.symm, if_pos rfl, one_mul, one_mul]
    refine Finset.prod_congr rfl fun l hl => ?_
    obtain ⟨hlj, hli⟩ : l ≠ j ∧ l ≠ i := by simpa using hl
    simp [hli, hlj]
  have e2 : ∏ l, (#(t l) : ℝ) =
      #(t i) * (#(t j) * ∏ l ∈ (univ.erase i).erase j, (#(t l) : ℝ)) := by
    rw [← Finset.mul_prod_erase _ _ (mem_univ i), ← Finset.mul_prod_erase _ _ hj']
  rw [← key, card_piFinset]
  push_cast
  rw [e1, e2]
  ring

/-- **The pair `(x i, x j)` is uniform on `t i × t j`.** For `i ≠ j`,
`(∑_x F(x i, x j)) · |t i| |t j| = |X| · ∑_{a ∈ t i, b ∈ t j} F(a, b)`. -/
theorem sum_piFinset_pair (t : ι → Finset V) {i j : ι} (hij : i ≠ j) (F : V → V → ℝ) :
    (∑ x ∈ piFinset t, F (x i) (x j)) * (#(t i) * #(t j)) =
      #(piFinset t) * ∑ a ∈ t i, ∑ b ∈ t j, F a b := by
  have hpt : ∀ x ∈ piFinset t, F (x i) (x j) = ∑ a ∈ t i, ∑ b ∈ t j,
      F a b * (if x i = a ∧ x j = b then (1 : ℝ) else 0) := by
    intro x hx
    have hxi : x i ∈ t i := Fintype.mem_piFinset.1 hx i
    have hxj : x j ∈ t j := Fintype.mem_piFinset.1 hx j
    rw [Finset.sum_eq_single (x i)]
    · rw [Finset.sum_eq_single (x j)]
      · simp
      · intro b _ hb; simp [Ne.symm hb]
      · intro h; exact absurd hxj h
    · intro a _ ha
      refine Finset.sum_eq_zero fun b _ => ?_
      simp [Ne.symm ha]
    · intro h; exact absurd hxi h
  have h1 : ∑ x ∈ piFinset t, F (x i) (x j) =
      ∑ a ∈ t i, ∑ b ∈ t j, F a b *
        ∑ x ∈ piFinset t, (if x i = a ∧ x j = b then (1 : ℝ) else 0) := by
    rw [Finset.sum_congr rfl hpt, Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.mul_sum]
  rw [h1, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [mul_assoc, card_fiber_mul t hij ha hb]
  ring

end AFKS
