import ErdosProblems.Problem261.Corridor

import Mathlib.Tactic

/-!
# Computational verification for `1 ≤ n ≤ 2000` (paper Theorem 4.4)

The reachability checker is defined in `Corridor.lean`; this file proves the batch
verification by native evaluation.
-/

namespace ErdosProblem261

/-- Check all target `n` in one decidable batch. -/
def checkReachableAllLe2000 : Bool :=
  (List.range 2000).all fun i =>
    corridorReachableBool (i + 1) 250000

theorem reachable_all_le_2000 : checkReachableAllLe2000 = true := by
  native_decide

theorem reachable_all_le_2000' : ReachableAllLe2000 := by
  intro n hn1 hn2
  have hmem : n - 1 ∈ List.range 2000 := by
    simp [List.mem_range]
    omega
  have h := congrArg id (reachable_all_le_2000)
  unfold checkReachableAllLe2000 at h
  simp [List.all_eq_true, List.mem_range] at h
  exact h (n - 1) hmem

theorem question1_corridor_le_2000 (n : ℕ) (hn1 : 1 ≤ n) (hn2 : n ≤ 2000) :
    CorridorReachableToZero n 250000 := by
  rcases corridorReachableBool_iff n 250000 |>.1 (reachable_all_le_2000' n hn1 hn2) with
    ⟨t, ht, h0⟩
  exact ⟨t, ht, h0⟩

end ErdosProblem261
