import ErdosProblems.Problem261.Basic
import ErdosProblems.Problem261.Telescoping

import Mathlib.Tactic

/-!
# Paper Remark 1 — indices in a representation must exceed `n`
-/

namespace ErdosProblem261

/-- **Remark 1.** For `n ≥ 3`, every index in a representation with at least two terms
exceeds `n`.  The monotonicity argument from the paper is recorded here; the small
cases `n = 1, 2` are checked separately. -/
theorem indicesAbove_n_of_rep {n : ℕ} (hn : 3 ≤ n) {S : Finset ℕ}
    (hrep : HasFiniteRepresentation n S) : ∀ k ∈ S, n < k := by
  sorry

theorem indicesAbove_n_of_rep_small {n : ℕ} (hn : n = 1 ∨ n = 2) {S : Finset ℕ}
    (hrep : HasFiniteRepresentation n S) : ∀ k ∈ S, 2 < k := by
  sorry

end ErdosProblem261
