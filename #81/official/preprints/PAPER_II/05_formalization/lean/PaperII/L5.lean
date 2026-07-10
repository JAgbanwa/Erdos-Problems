import PaperII.CloneCopy

/-!
# Paper II — A both-simplicial admissible pair exists at every non-terminal graph (ledger L5 = Cor 5.2)

Contrapositive of L7: if a chordal `G` (with `ChordalStructure`) is not complete-split, there are two
nonadjacent simplicial vertices with distinct open neighborhoods. These are representatives of the
both-simplicial admissible clone-class pair `U,V` used by the symmetrization L6 (their clone classes
are `{v | N(v)=N(x)}`, `{v | N(v)=N(y)}`; simpliciality and the class are neighborhood invariants).
-/

open scoped BigOperators

namespace PaperII

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Ledger L5 (Corollary 5.2). -/
theorem exists_both_simplicial_pair (G : SimpleGraph V) (hchord : ChordalStructure G)
    (hnc : ¬ IsCompleteSplit G) :
    ∃ x y : V, IsSimplicial G x ∧ IsSimplicial G y ∧
      ¬ G.Adj x y ∧ G.neighborSet x ≠ G.neighborSet y := by
  by_contra h
  push_neg at h
  exact hnc (isCompleteSplit_of_isTerminal G