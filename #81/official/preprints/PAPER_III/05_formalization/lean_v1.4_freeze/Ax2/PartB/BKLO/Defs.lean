/-
  Part B (Phase 2) — BKLO transfer, DECOMPOSED.

  We break the monolithic `bklo_kthree_transfer` axiom into small interfaces, mirroring the
  successful A5/Farkas decomposition. This file fixes the intermediate objects; the interface
  lemmas and the top-level assembly live in `Transfer.lean`.

  Phase-1 note: this does NOT touch the axiom in `Ax2.PartB.Axioms`; it is the parallel
  Phase-2 scaffold aiming to eventually de-axiomatize it.
-/
import Ax2.Basic

namespace Ax2.BKLO

open SimpleGraph Finset Ax2

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The edges covered by a family of triangles. -/
def coveredEdges (P : Finset (Finset V)) : Finset (Sym2 V) := P.biUnion triEdges

/-- A family of triangles is **edge-disjoint** (their edge sets are pairwise disjoint). -/
def EdgeDisjoint (P : Finset (Finset V)) : Prop :=
  ∀ t₁ ∈ P, ∀ t₂ ∈ P, t₁ ≠ t₂ → Disjoint (triEdges t₁) (triEdges t₂)

/-- An **approximate triangle decomposition** of `G`: an edge-disjoint family of triangles of
`G` covering every edge except those in `leftover`. -/
def ApproxTriangleDecomp (G : SimpleGraph V) [DecidableRel G.Adj]
    (leftover : Finset (Sym2 V)) : Prop :=
  ∃ P : Finset (Finset V), (∀ t ∈ P, G.IsNClique 3 t) ∧ EdgeDisjoint P ∧
    coveredEdges P = G.edgeFinset \ leftover

/-- A **`β`-absorber** for `G`: an edge-disjoint family `A` of triangles of `G` such that any
**triangle-divisible** leftover edge set `L` of density `≤ β` (disjoint from `A`'s edges) can be
completed, together with `A`, to an edge-disjoint triangle family covering exactly
`coveredEdges A ∪ L`.

Triangle-divisibility of `L` — `3 ∣ |L|` **and every degree even** — is REQUIRED, not merely
`3 ∣ |L|`: a graph covered by edge-disjoint triangles has all even degrees
(`coveredEdges_degree_even`), so `coveredEdges A ∪ L` (with `coveredEdges A` already even) is
triangle-decomposable only when `L` has even degrees. Omitting the even-degree condition makes
this predicate unsatisfiable (a leftover with an odd-degree vertex cannot be absorbed). -/
def TriangleAbsorber (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset (Finset V)) (β : ℝ) : Prop :=
  (∀ t ∈ A, G.IsNClique 3 t) ∧ EdgeDisjoint A ∧
    ∀ L : Finset (Sym2 V), L ⊆ G.edgeFinset → Disjoint L (coveredEdges A) →
      (L.card : ℝ) ≤ β * (Fintype.card V : ℝ) ^ 2 → 3 ∣ L.card →
      (∀ v : V, Even ((L.filter (fun e => v ∈ e)).card)) →
      ∃ P : Finset (Finset V), (∀ t ∈ P, G.IsNClique 3 t) ∧ EdgeDisjoint P ∧
        coveredEdges P = coveredEdges A ∪ L

end Ax2.BKLO
