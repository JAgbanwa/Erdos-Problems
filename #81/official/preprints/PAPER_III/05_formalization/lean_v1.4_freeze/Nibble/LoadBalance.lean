/-
# Round-robin / least-loaded load balancing (the heart of the sweep ledger).

The round-robin assignment `i ↦ i mod m` puts at most `⌈t/m⌉ = t/m + 1` of the first `t` items in
any single bucket.  Deterministic, no probability — the core of the ledger bound on the sweep's
per-class spread `sp`.
-/
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Bound

open Finset

namespace Nibble.AX1

/-- **Round-robin balance.**  Among the first `t` items, at most `t/m + 1` fall in bucket `j`
under `i ↦ i mod m`.  (The map `i ↦ i / m` injects that bucket into `range (t/m+1)`.) -/
theorem balanced_bucket_le (t m j : ℕ) :
    ((Finset.range t).filter (fun i => i % m = j)).card ≤ t / m + 1 := by
  classical
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    have h1 : ((Finset.range t).filter (fun i => i % 0 = j)).card ≤ 1 := by
      refine Finset.card_le_one.mpr ?_
      intro a ha b hb
      simp only [mem_filter, Nat.mod_zero] at ha hb
      exact ha.2.trans hb.2.symm
    simpa [Nat.div_zero] using h1
  refine le_trans (Finset.card_le_card_of_injOn (fun i => i / m) ?_ ?_)
    (by rw [Finset.card_range])
  · intro i hi
    have hi1 : i < t := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right (le_of_lt hi1)))
  · intro a ha b hb hab
    simp only [mem_coe, mem_filter, mem_range] at ha hb
    have hab' : a / m = b / m := hab
    have ea : m * (a / m) + a % m = a := Nat.div_add_mod a m
    have eb : m * (b / m) + b % m = b := Nat.div_add_mod b m
    rw [ha.2] at ea
    rw [hb.2] at eb
    rw [hab'] at ea
    exact ea.symm.trans eb

end Nibble.AX1
