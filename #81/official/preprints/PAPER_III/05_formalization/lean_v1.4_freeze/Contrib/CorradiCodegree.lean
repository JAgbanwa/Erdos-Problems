/-
# A Corrádi-type bound: many large sets with small pairwise intersections

If `N_x`, `x ∈ T`, are subsets of a set `W` of size `n`, each of size at least `m`, with all
pairwise intersections of size at most `c`, then

  `|T| · m² ≤ n · m + n · |T| · c`,

so that `|T| ≤ nm / (m² − nc)` as soon as `m² > nc`.

Proved by double counting and Cauchy–Schwarz (first and second moments of point multiplicities).
A clean, general set-family counting inequality of the Corrádi type.

* `Contrib.Corradi.card_le_of_codegree` (with the moment identities `sum_multiplicity`,
  `sum_multiplicity_sq`).

Sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib

open Finset

namespace Contrib.Corradi

variable {ι V : Type*} [DecidableEq V]

/-- Double counting: the sum over `W` of the number of sets containing a point is the sum of the
sizes of the sets. -/
theorem sum_multiplicity (W : Finset V) (T : Finset ι) (N : ι → Finset V)
    (hsub : ∀ x ∈ T, N x ⊆ W) :
    ∑ w ∈ W, (T.filter (fun x => w ∈ N x)).card = ∑ x ∈ T, (N x).card := by
  classical
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x hx => ?_)
  rw [← Finset.card_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.2 (hsub x hx)]

/-- Double counting: the sum over `W` of the squared multiplicity is the sum of all pairwise
intersection sizes. -/
theorem sum_multiplicity_sq (W : Finset V) (T : Finset ι) (N : ι → Finset V)
    (hsub : ∀ x ∈ T, N x ⊆ W) :
    ∑ w ∈ W, ((T.filter (fun x => w ∈ N x)).card) ^ 2
      = ∑ x ∈ T, ∑ x' ∈ T, ((N x) ∩ (N x')).card := by
  classical
  have h1 : ∀ w : V, ((T.filter (fun x => w ∈ N x)).card) ^ 2
      = ∑ x ∈ T, ∑ x' ∈ T, (if w ∈ N x ∩ N x' then 1 else 0) := by
    intro w
    rw [sq, Finset.card_filter, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun x' _ => ?_))
    by_cases h : w ∈ N x <;> by_cases h' : w ∈ N x' <;> simp [h, h']
  simp only [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x hx => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x' _ => ?_)
  rw [← Finset.card_filter, Finset.filter_mem_eq_inter,
    Finset.inter_eq_right.2 (fun z hz => hsub x hx (Finset.mem_inter.1 hz).1)]

/-- **Corrádi's counting bound.**  Sets of size at least `m` inside a set of size `n`, with
pairwise intersections at most `c`, are few: `|T| m² ≤ n m + n |T| c`. -/
theorem card_le_of_codegree [DecidableEq ι] (W : Finset V) (T : Finset ι) (N : ι → Finset V) (m c : ℝ)
    (hm : 0 ≤ m) (hc : 0 ≤ c) (hsub : ∀ x ∈ T, N x ⊆ W)
    (hsize : ∀ x ∈ T, m ≤ ((N x).card : ℝ))
    (hcodeg : ∀ x ∈ T, ∀ x' ∈ T, x ≠ x' → (((N x) ∩ (N x')).card : ℝ) ≤ c) :
    (T.card : ℝ) * m ^ 2 ≤ (W.card : ℝ) * m + (W.card : ℝ) * (T.card : ℝ) * c := by
  classical
  set n : ℝ := (W.card : ℝ) with hn
  set t : ℝ := (T.card : ℝ) with ht
  have hn0 : 0 ≤ n := by positivity
  have ht0 : 0 ≤ t := by positivity
  set dd : V → ℕ := fun w => (T.filter (fun x => w ∈ N x)).card with hdd
  set S1 : ℝ := ∑ w ∈ W, ((dd w : ℕ) : ℝ) with hS1
  set S2 : ℝ := ∑ w ∈ W, (((dd w : ℕ) : ℝ)) ^ 2 with hS2
  -- the two double-counting identities, over `ℝ`
  have hstep1 : S1 = ∑ x ∈ T, ((N x).card : ℝ) := by
    rw [hS1, ← Nat.cast_sum, sum_multiplicity W T N hsub, Nat.cast_sum]
  have hstep2 : S2 = ∑ x ∈ T, ∑ x' ∈ T, (((N x) ∩ (N x')).card : ℝ) := by
    have h := sum_multiplicity_sq W T N hsub
    have : S2 = ((∑ w ∈ W, ((dd w) ^ 2 : ℕ) : ℕ) : ℝ) := by
      rw [hS2, Nat.cast_sum]
      exact Finset.sum_congr rfl (fun w _ => by push_cast; ring)
    rw [this, h, Nat.cast_sum]
    exact Finset.sum_congr rfl (fun x _ => by rw [Nat.cast_sum])
  -- lower bound for the first moment
  have hS1ge : t * m ≤ S1 := by
    rw [hstep1, ht]
    have := Finset.card_nsmul_le_sum T (fun x => ((N x).card : ℝ)) m hsize
    rwa [nsmul_eq_mul] at this
  have hS1nonneg : 0 ≤ S1 := by
    rw [hS1]
    exact Finset.sum_nonneg (fun w _ => by positivity)
  -- upper bound for the second moment
  have hS2le : S2 ≤ S1 + t * t * c := by
    rw [hstep2, hstep1]
    have hrow : ∀ x ∈ T, ∑ x' ∈ T, (((N x) ∩ (N x')).card : ℝ)
        ≤ ((N x).card : ℝ) + t * c := by
      intro x hx
      rw [Finset.sum_eq_add_sum_diff_singleton hx]
      have h1 : (((N x) ∩ (N x)).card : ℝ) = ((N x).card : ℝ) := by
        rw [Finset.inter_self]
      have h2 : ∑ x' ∈ T \ {x}, (((N x) ∩ (N x')).card : ℝ) ≤ ((T \ {x}).card : ℝ) * c := by
        have := Finset.sum_le_card_nsmul (T \ {x}) (fun x' => (((N x) ∩ (N x')).card : ℝ)) c
          (fun x' hx' => by
            obtain ⟨hx'T, hx'ne⟩ := Finset.mem_sdiff.1 hx'
            exact hcodeg x hx x' hx'T (fun hc => hx'ne (by simp [hc])))
        rwa [nsmul_eq_mul] at this
      have h3 : ((T \ {x}).card : ℝ) ≤ t := by
        rw [ht]
        exact_mod_cast Finset.card_le_card Finset.sdiff_subset
      have h4 : ((T \ {x}).card : ℝ) * c ≤ t * c := mul_le_mul_of_nonneg_right h3 hc
      rw [h1]
      linarith
    calc ∑ x ∈ T, ∑ x' ∈ T, (((N x) ∩ (N x')).card : ℝ)
        ≤ ∑ x ∈ T, (((N x).card : ℝ) + t * c) := Finset.sum_le_sum hrow
      _ = (∑ x ∈ T, ((N x).card : ℝ)) + t * (t * c) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ht]
      _ = (∑ x ∈ T, ((N x).card : ℝ)) + t * t * c := by ring
  -- Cauchy–Schwarz
  have hCS : S1 ^ 2 ≤ n * S2 := by
    have := sq_sum_le_card_mul_sum_sq (s := W) (f := fun w => ((dd w : ℕ) : ℝ))
    rwa [← hS1, ← hS2, ← hn] at this
  -- the algebra
  rcases eq_or_lt_of_le hm with hm0 | hmpos
  · rw [← hm0]
    have : (0:ℝ) ≤ n * t * c := by positivity
    nlinarith
  rcases eq_or_lt_of_le ht0 with ht0' | htpos
  · rw [← ht0']
    have : (0:ℝ) ≤ n * m := by positivity
    nlinarith
  have hS1pos : 0 < S1 := lt_of_lt_of_le (by positivity) hS1ge
  have h1 : S1 ^ 2 ≤ n * S1 + n * (t * t) * c := by nlinarith [hS2le, hCS, hn0]
  have h2 : n * (t * t) * c * m ≤ n * t * c * S1 := by
    have hfac : (0:ℝ) ≤ n * t * c := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hS1ge hfac]
  have hkey : S1 * m ≤ n * m + n * t * c := by
    nlinarith [mul_le_mul_of_nonneg_right h1 (le_of_lt hmpos), hS1pos]
  nlinarith [mul_le_mul_of_nonneg_right hS1ge (le_of_lt hmpos)]

end Contrib.Corradi
