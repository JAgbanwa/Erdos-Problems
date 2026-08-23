/-
# Paper III — obstructions justifying the AX2 density hypothesis

AX2 (exact triangle decomposition of a triangle-divisible graph) is only invoked under a *density*
hypothesis (`(0.9 + ε)·n ≤ minDegree`). These two obstructions, proved in the BKLO development,
show why such a hypothesis is genuinely needed: triangle-divisibility (`3 ∣ |E|`, all degrees even)
does **not** by itself imply triangle-decomposability. They are surfaced here as Paper-III-facing
remarks (no new proof; re-exported from `BKLO`).

* `ax2_divisibility_degree_insufficient` — a graph on `Fin 6` (the 6-cycle) with all degrees even and
  `3 ∣ |E|` that is NOT triangle-decomposable: divisibility + degree parity is not sufficient.
* `ax2_density_necessary_K7_minus_two_triangles` — `K₇` minus two vertex-disjoint triangles is not
  triangle-decomposable, a concrete surviving obstruction even at high edge count.

Both are sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import BKLO.Fano
import BKLO.ClusterWeb

namespace PaperIII

/-- **Divisibility + even degrees is not sufficient for triangle decomposition.** There is a graph
(the 6-cycle on `Fin 6`) with all degrees even and `3 ∣ |E|` that is not triangle-decomposable — so
AX2's exact-decomposition conclusion genuinely requires more than triangle-divisibility, motivating
its density hypothesis. -/
alias ax2_divisibility_degree_insufficient := BKLO.exists_even_three_dvd_not_triDecomp

/-- **A surviving obstruction at high edge count.** `K₇` minus two vertex-disjoint triangles is not
triangle-decomposable: the residue has 15 edges but every triangle inside uses two of the six edges
at the seventh vertex, so no decomposition exists. Divisibility-plus-degree counting cannot rule such
configurations out, which is why the dense regime is used. -/
alias ax2_density_necessary_K7_minus_two_triangles := BKLO.not_triDecomp_sdiff_twoTriangles7

end PaperIII
