import Mathlib
import PaperII.CloneSimplicial

/-!
# Paper II — Chordal-structure hypotheses (ledger Part A, A1–A6) as an explicit bundle

**Path 3 (thinned).** The classical structure theory of chordal graphs (Dirac 1961: simplicial
vertices) is not yet in Mathlib. Rather than assume it as global `axiom`s (which would appear in
`#print axioms`), we bundle exactly the Dirac-family facts A1/A3 as an explicit hypothesis structure
`ChordalStructure G`. The main theorem is then *conditional* on this structure: `#print axioms` stays
clean, and the dependence is visible in the statement. The bundle can be discharged later (proving
chordal theory in Lean) without changing any downstream theorem.

**A4 removed.** The clique-tree / running-intersection fields (Gavril 1974) were only ever consumed
by L7 (terminal characterization). Since L7 was refactored to a clique-tree-free proof
(`PaperII.L7`, using `PaperII.Dirac`), A4 is no longer needed and has been deleted from the bundle.
The residual interface is exactly the Dirac-family facts A1/A3.

Fields mirror ledger Part A:
* A1 + A3a  `simplicial_hereditary`  — every nonempty induced subgraph has a simplicial vertex;
* A3b       `two_nonadj_simplicial`  — a connected noncomplete one has two nonadjacent simplicial vertices.
A2 (chordality closure under simplicial extension) is threaded separately as `A2Transfer` in L4/L6.
-/

open scoped BigOperators

namespace PaperII

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `G` is **chordal**: every cycle of length `≥ 4` has a chord — an adjacency `G.Adj x y` between two
vertices `x, y` on the cycle whose edge `s(x,y)` is not one of the cycle's own edges. Standard
definition (no data, no assumed theorems). Defined here (upstream of `ChordalStructure`) so the bundle
can carry it as a field (Path 2, Fase 5); A1 (`chordal_induce`) stays in `PaperII.IsChordal`. -/
def IsChordal (G : SimpleGraph V) : Prop :=
  ∀ ⦃v : V⦄ (c : G.Walk v v), c.IsCycle → 4 ≤ c.length →
    ∃ x y : V, x ∈ c.support ∧ y ∈ c.support ∧ G.Adj x y ∧ s(x, y) ∉ c.edges

/-- Ledger Part A (Dirac-family A1/A3) as an explicit hypothesis bundle on `G` (Path 3).

Kept data-valued (`: Type`) for continuity: after A4 removal the two surviving fields are both
propositions, so Lean would otherwise infer `Prop`; we pin `Type` so `A2Transfer` (`: Type _`, L4)
and `theorem_1_2`'s hypotheses keep their exact committed types. No mathematical content changes. -/
structure ChordalStructure (G : SimpleGraph V) : Type where
  /-- The graph is chordal in the standard sense (Path 2, Fase 5). This field lets the whole bundle be
      discharged from `IsChordal` (`chordalStructure_of_isChordal`) and lets `A2Transfer` be proven via
      `chordal_classCopy`. Kept first so `⟨…⟩` constructors read structurally. -/
  isChordal : IsChordal G
  /-- A1 + A3a (hereditary simplicial existence): every nonempty induced subgraph has a simplicial
      vertex. Combines A1 (an induced subgraph of a chordal graph is chordal) with A3a (a nonempty
      chordal graph has a simplicial vertex). L7 applies this to connected components and to `H−K`. -/
  simplicial_hereditary : ∀ (W : Set V), W.Nonempty → ∃ v : W, IsSimplicial (G.induce W) v
  /-- A3b: a connected noncomplete graph has two nonadjacent simplicial vertices. -/
  two_nonadj_simplicial : G.Connected → (¬ ∀ u v : V, u ≠ v → G.Adj u v) →
      ∃ x y : V, x ≠ y ∧ ¬ G.Adj x y �