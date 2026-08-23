/-
# Nibble — concrete T3 wiring : edge count vs vertex count

Standalone, Mathlib-only. Toward discharging `NibbleTheorem` by instantiating the abstract
convergence chain with actual nibble rounds. A key quantitative ingredient: a near-regular
`r`-uniform hypergraph has `|H| ≈ qd/r` edges, so the per-round covered count
`r·|matching| ≥ r·|H|·p·(1-p)^{rΔ}` is a definite fraction of the `q = |V|` vertices.

* `edge_count_lower` — `(1-μ)·d·|V| ≤ r·|H|` for a `(1±μ)`-nearly `d`-regular `r`-uniform
  hypergraph (from the handshake `∑ deg = r|H|` and the degree-sum squeeze).

Definitions from `Nibble.Basic` / `Nibble.Regular`. Must be sorry-free and axiom-clean.
-/
import Nibble.Basic
import Nibble.Regular
import Mathlib.Tactic.Bound

open Finset

namespace Hypergraph

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- **Wiring — edge count lower bound.** For a `(1±μ)`-nearly `d`-regular `r`-uniform hypergraph,
`(1-μ)·d·|V| ≤ r·|H|`. Combined with `|covered| = r·|matching|` this makes the per-round covered
count a definite fraction of the vertex set. -/
theorem edge_count_lower {H : Finset (Finset V)} {d μ : ℝ} {r : ℕ}
    (hr : IsUniform H r) (hReg : NearlyRegular H d μ) :
    (1 - μ) * d * (Fintype.card V : ℝ) ≤ r * (H.card : ℝ) := by
  have hsum : (∑ v : V, (degree H v : ℝ)) = r * (H.card : ℝ) := by
    rw [← Nat.cast_sum, sum_degree H hr]
    push_cast
    ring
  have hlow := (sum_degree_bounds hReg).1
  rw [hsum] at hlow
  exact hlow

end Hypergraph
