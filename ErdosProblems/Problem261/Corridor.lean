import ErdosProblems.Problem261.Basic
import ErdosProblems.Problem261.Telescoping

import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

/-!
# Question 2 — corridor digraph reformulation

Paper Definition 4.1 and Proposition 4.2, plus a computable reachability checker.
-/

namespace ErdosProblem261

/-- Residue at scale `j` lies in the corridor `0 … j+2`. -/
def InCorridor (j rho : ℕ) : Prop := rho ≤ j + 2

/-- One layer of forward reachability from residues at scale `j`. -/
def forwardLayer (j : ℕ) (rhos : Finset ℕ) : Finset ℕ :=
  rhos.biUnion fun rho =>
    (if 2 * rho ≤ j + 3 then {2 * rho} else ∅) ∪
      (if 2 * rho ≥ j + 1 ∧ 2 * rho - (j + 1) ≤ j + 3 then {2 * rho - (j + 1)} else ∅)

/-- `reachSet n t` is the set of residues reachable at scale `n + t`. -/
def reachSet (n : ℕ) : ℕ → Finset ℕ
  | 0 => {n}
  | t + 1 => forwardLayer (n + t) (reachSet n t)

lemma mem_reachSet_zero {n rho : ℕ} : rho ∈ reachSet n 0 ↔ rho = n := by
  simp [reachSet]

/-- `(n,n)` reaches `(n+t,0)` within `t` steps (paper `Γ_n`). -/
def CorridorReachableToZero (n horizon : ℕ) : Prop :=
  ∃ t ≤ horizon, 0 ∈ reachSet n t

/-- Decidable checker for the computational theorem. -/
def corridorReachableBool (n horizon : ℕ) : Bool :=
  (List.range (horizon + 1)).any fun t => decide (0 ∈ reachSet n t)

lemma corridorReachableBool_iff (n horizon : ℕ) :
    corridorReachableBool n horizon = true ↔ CorridorReachableToZero n horizon := by
  unfold corridorReachableBool CorridorReachableToZero
  simp [List.any_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_iff]

/-- A finite certificate: distinct indices summing to `n / 2^n`. -/
structure CorridorCertificate (n : ℕ) where
  indices : Finset ℕ
  card_ge_two : 2 ≤ indices.card
  pos : ∀ k ∈ indices, 0 < k
  sum_eq : fSum indices = (n : ℚ) / (2 ^ n : ℚ)

theorem certificate_to_representation {n : ℕ} (c : CorridorCertificate n) :
    HasFiniteRepresentation n c.indices :=
  ⟨c.card_ge_two, c.pos, c.sum_eq⟩

theorem corridor_implies_representation {n : ℕ} (c : CorridorCertificate n) :
    Question1 n := ⟨c.indices, certificate_to_representation c⟩

/-- Paper Open Problem 1.1. -/
def AllNRepresentable : Prop := ∀ n, 0 < n → Question1 n

/-- All `1 ≤ n ≤ 2000` reach zero within horizon `250000` (Appendix verification target). -/
def ReachableAllLe2000 : Prop :=
  ∀ n, 1 ≤ n → n ≤ 2000 → corridorReachableBool n 250000 = true

/-- Proposition 4.2 (corridor formulation): representability is equivalent to reaching `0`
in the corridor digraph. The full bi-implication is recorded here; the forward direction
(from an explicit certificate) is immediate, while the converse constructs the certificate
from a successful walk by taking the Include edges along the path. -/
def CorridorReformulation (n : ℕ) : Prop :=
  Question1 n ↔ CorridorReachableToZero n 250000

end ErdosProblem261
