/-
# The dense triangle decomposition theorem in graph language, from the nibble alone

`BKLO/Section11CellsPlace.lean` closes the BKLO §11 cells route and delivers

```
BKLO.triDecompDense_of_nibble_faithful_uncond :
  ApproxTriDecompMinDeg (9/10) → TriDecompDense
```

in the edge-set language of the engine.  This file transports it to the language of simple graphs
through the project's existing bridges
(`BKLO.nearOptimalConclusion_of_triDecompDense`, `BKLO.triangle_decomposition_of_nearOptimal`).

* `BKLO.triangle_decomposition_of_nibble` — every large triangle-divisible graph of minimum degree
  at least `(9/10 + ε)n` decomposes into triangles, given the approximate (nibble) decomposition at
  minimum degree `9/10`.

Everything here is `sorry`-free.
-/
import BKLO.Section11CellsPlace
import BKLO.NearOptimalFaithful
import BKLO.Main

open Finset

namespace BKLO

/-- **The dense triangle decomposition theorem, in graph language, from the dense nibble.**

Given the approximate (nibble) triangle decomposition at minimum degree `9/10`
(`BKLO.ApproxTriDecompMinDeg`), every sufficiently large graph whose number of edges is divisible
by three, whose degrees are all even, and whose minimum degree is at least `(9/10 + ε)n`, has a
decomposition of its edge set into triangles.

This is the BKLO §11 route run end to end: reserve the §8 absorbing structure spread over the
bottom cells of the §10 vortex (`BKLO.cellsChainReservation_holds`), run the proved §10 near-optimal
decomposition on what is left, and absorb the remainder. -/
theorem triangle_decomposition_of_nibble (happ : ApproxTriDecompMinDeg (9 / 10)) :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ,
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        n₀ ≤ Fintype.card V →
        (3 ∣ G.edgeFinset.card ∧ ∀ v, Even (G.degree v)) →
        (9 / 10 + ε) * (Fintype.card V : ℝ) ≤ (G.minDegree : ℝ) →
        TriangleDecomposable G :=
  triangle_decomposition_of_nearOptimal
    (nearOptimalConclusion_of_triDecompDense (triDecompDense_of_nibble_faithful_uncond happ))

end BKLO
