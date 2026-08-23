/-
# The greedy-loop assembly of BKLO Lemma 10.3 (r = 2)

BKLO Lemma 10.3 processes the apices `x ∈ U` in turn, choosing for each a perfect matching `M_x` in
the unused part of the neighbourhood `N_H(x, V)` (a `K₂`-factor, existing by Dirac's theorem), and
forms the triangles `{x} ∪ e` for `e ∈ M_x`.  The union of these, over all apices, is the graph `HV`
together with the covered star edges, and `H[U,V] ∪ HV` is triangle-decomposable.

This file supplies the **assembly** half of that loop, `sorry`-free: given a matching per apex
(edge-disjoint *across* apices — the property the greedy `unused-part` bookkeeping guarantees), the
union of the per-apex stars is triangle-decomposable.  It combines the per-apex brick
`BKLO.triDecomp_famEdges_starTriangles` with the disjoint-composition brick
`BKLO.DistributiveAbsorption.dec_biUnion_of_pairwiseDisjoint`.

What remains of Lemma 10.3 is the **existence** half — that the greedy choice of edge-disjoint
perfect matchings succeeds (min degree of the unused neighbourhood stays `≥ half` by the
bookkeeping, so Dirac `BKLO.perfectMatchingDirac_holds` applies) — isolated as a separate step.

Everything here is `sorry`-free.
-/
import BKLO.StarMatchingTriangles
import BKLO.DistributiveAbsorptionSkeleton

open Finset

namespace BKLO

variable {V : Type*} [DecidableEq V]

/-- **Greedy-loop assembly (BKLO Lemma 10.3, r = 2).**  A matching `Mx x` per apex `x ∈ U`, whose
star-triangle edge sets are pairwise edge-disjoint across apices, assembles into a triangle
decomposition of the union of the stars.  The union is exactly `H[U,V] ∪ HV` in the notation of the
paper; edge-disjointness across apices is what the greedy `unused-part` construction provides. -/
theorem triDecomp_biUnion_starTriangles {U : Finset V} {Mx : V → Finset (Finset V)}
    (hM : ∀ x ∈ U, IsMatchingAvoiding (Mx x) x)
    (hdisj : (U : Set V).Pairwise
      (fun x y => Disjoint (famEdges (starTriangles x (Mx x))) (famEdges (starTriangles y (Mx y))))) :
    TriDecomp (U.biUnion (fun x => famEdges (starTriangles x (Mx x)))) :=
  DistributiveAbsorption.dec_biUnion_of_pairwiseDisjoint
    (Dec := fun E => TriDecomp E) triDecomp_empty
    (fun hd h₁ h₂ => TriDecomp.union hd h₁ h₂)
    U (fun x => famEdges (starTriangles x (Mx x))) hdisj
    (fun x hx => triDecomp_famEdges_starTriangles (hM x hx))

end BKLO
