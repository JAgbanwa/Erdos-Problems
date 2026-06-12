import ErdosProblems.Problem261.Basic
import ErdosProblems.Problem261.Telescoping
import ErdosProblems.Problem261.Q1
import ErdosProblems.Problem261.Corridor
import ErdosProblems.Problem261.Certificates
import ErdosProblems.Problem261.Compute
import ErdosProblems.Problem261.Q3

/-!
# Erdős Problem #261 — Representations as sums of distinct terms `k/2^k`

Formalization of the paper in folder `#261`.

## Status

| Result | Lean name | Status |
|--------|-----------|--------|
| Telescoping (Lemma 0) | `G_sub_G_succ`, `blockSum` | **proved** |
| Indices exceed `n` (Remark 1) | `indicesAbove_n_of_rep` | **proved** |
| Infinite family (Theorem 1) | `familyRepresentation` | **proved** |
| Infinitely many `n` (Q1) | `infinitelyMany_question1` | **proved** |
| Second family (Remark 2) | `secondFamily_representation` | **proved** |
| Table certificates | `tableCert_*`, `question1_table` | **proved** (`native_decide`) |
| Corridor digraph | `reachSet`, `CorridorReachableToZero` | **defined** |
| `n ≤ 2000` reachability | `reachable_all_le_2000` | **proved** (`native_decide`) |
| All `n` (Open Problem) | `AllNRepresentable` | **stated** |
| Sequence continuum (Theorem 5.4) | `sequenceSolutions_two` | **stated** (`sorry`) |
| Set continuum (Theorem 5.5) | `setSolutions_exist` | **stated** (`sorry`) |
| Unique set solution at `x=2` | `unique_set_solution_two` | **stated** (`sorry`) |

The algebraic and computational parts of the paper are fully formalized in exact rational
and native-decide arithmetic. The continuum-cardinality theorems and the full
bi-implication of the corridor reformulation remain open in this development.
-/

namespace ErdosProblem261

/-- Summary: Question (1) has infinitely many positive instances. -/
theorem question1_yes : Set.Infinite {n : ℕ | Question1 n} :=
  infinitelyMany_question1

/-- Summary: Question (2) holds for all `n ≤ 2000` in the corridor formulation. -/
theorem question2_for_le_2000 (n : ℕ) (hn1 : 1 ≤ n) (hn2 : n ≤ 2000) :
    CorridorReachableToZero n 250000 :=
  question1_corridor_le_2000 n hn1 hn2

end ErdosProblem261
