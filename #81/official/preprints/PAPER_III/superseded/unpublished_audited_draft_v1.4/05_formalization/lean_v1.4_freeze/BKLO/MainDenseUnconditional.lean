/-
# The dense triangle-decomposition theorem, UNCONDITIONAL.

This is the capstone of the faithful BKLO route for `F = K₃` at the threshold `9/10`.

* `BKLO.triangle_decomposition_of_nibble` (Section11CellsMain, faithful BKLO §11 cells route:
  reserve the §8 absorber spread along the vortex, run the proved §10 near-optimal decomposition,
  absorb the cell-confined remainder via per-cell absorbers and boundary connectors) reduces the
  dense theorem to the single hypothesis `ApproxTriDecompMinDeg (9/10)` — the approximate
  triangle decomposition ("nibble").
* `BKLO.approxTriDecompMinDeg_dense` (ApproxTriDecompMinDegDense, from the proved dense nibble
  `Nibble.denseTriNibbleMaxDeg_holds`) discharges exactly that hypothesis.

Composing the two makes the dense triangle-decomposition theorem UNCONDITIONAL: every sufficiently
large triangle-divisible graph `G` with `δ(G) ≥ (9/10 + ε)|G|` has a triangle decomposition,
sorry-free and depending only on `[propext, Classical.choice, Quot.sound]`.
-/
import BKLO.Section11CellsMain
import BKLO.ApproxTriDecompMinDegDense

namespace BKLO

/-- **The dense triangle-decomposition theorem (BKLO 9/10), UNCONDITIONAL.**
For every `ε > 0` there is `n₀` such that every triangle-divisible graph `G` on `n ≥ n₀` vertices
with `δ(G) ≥ (9/10 + ε)·n` has a triangle decomposition. -/
theorem triangle_decomposition_dense :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ,
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        n₀ ≤ Fintype.card V →
        (3 ∣ G.edgeFinset.card ∧ ∀ v, Even (G.degree v)) →
        (9 / 10 + ε) * (Fintype.card V : ℝ) ≤ (G.minDegree : ℝ) →
        TriangleDecomposable G :=
  triangle_decomposition_of_nibble (approxTriDecompMinDeg_dense (le_refl (9 / 10)))

end BKLO
