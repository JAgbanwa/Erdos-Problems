/-
# Yuster Y-a — matchings of the triangle hypergraph ↔ `ν₃`

Standalone, Mathlib-only. Completes the correspondence between matchings of the edge-based triangle
hypergraph `triangleHypergraphE G` and the integral triangle-packing number `nu3 G`. A matching of
`triangleHypergraphE G` is a set of triangles sharing no edge — an edge-disjoint triangle packing — so
`nu3 G` (defined as the max matching card) is exactly the maximum edge-disjoint triangle packing.

* `nu3_ge` (existing) — every matching card is `≤ nu3` (lower bound direction).
* `nu3_achieved` — `nu3` IS attained by some matching (the sup is a max).
* `nu3_le` — if every matching has card `≤ K` then `nu3 ≤ K` (upper bound direction).

Together these characterise `nu3 G` as the maximum matching card: the bridge by which `NibbleTheorem`
(a large matching) lower-bounds `ν₃`, and by which `ν₃*` counting upper-bounds it.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.YusterEdge

open Finset Hypergraph SimpleGraph
open scoped Classical

namespace Nibble.YusterE

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The empty set is a matching of any hypergraph. -/
theorem isMatching_empty (H : Finset (Finset (Finset V))) :
    IsMatching H (∅ : Finset (Finset (Finset V))) :=
  { subset := Finset.empty_subset _,
    disjoint := fun e he => absurd he (Finset.notMem_empty e) }

/-- **Y-a — `ν₃` is attained.** The maximum in the definition of `nu3` is realised by an actual
matching: there is a matching of `triangleHypergraphE G` whose cardinality equals `nu3 G`. This is the
upper companion of `nu3_ge`, so `nu3 G` is genuinely the *maximum* edge-disjoint triangle packing. -/
theorem nu3_achieved : ∃ M, IsMatching (triangleHypergraphE G) M ∧ M.card = nu3 G := by
  have hne : ((triangleHypergraphE G).powerset.filter
      (fun M => IsMatching (triangleHypergraphE G) M)).Nonempty := by
    refine ⟨∅, ?_⟩
    rw [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.empty_subset _, isMatching_empty _⟩
  obtain ⟨M, hM, hsup⟩ := Finset.exists_mem_eq_sup _ hne Finset.card
  rw [Finset.mem_filter, Finset.mem_powerset] at hM
  exact ⟨M, hM.2, hsup.symm⟩

/-- **Y-a — upper bound direction.** If every matching of `triangleHypergraphE G` has card `≤ K`, then
`nu3 G ≤ K`. Together with `nu3_ge` and `nu3_achieved`, `nu3 G = max matching card`. -/
theorem nu3_le {K : ℕ}
    (h : ∀ M, IsMatching (triangleHypergraphE G) M → M.card ≤ K) : nu3 G ≤ K := by
  rw [nu3]
  apply Finset.sup_le
  intro M hM
  rw [Finset.mem_filter, Finset.mem_powerset] at hM
  exact h M hM.2

end Nibble.YusterE
