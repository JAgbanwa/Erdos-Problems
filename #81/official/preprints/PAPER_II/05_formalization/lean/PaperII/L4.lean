import PaperII.CloneCopy

/-!
# Paper II — Copying toward a simplicial target preserves chordality (ledger L4 = Lemma 4.3, A2)

**Path 3.** L4 is exactly the admitted textbook fact A2 (adding vertices with a clique neighborhood
preserves chordality), specialized to the class-copy toward a simplicial target. It is threaded as an
explicit HYPOTHESIS `A2Transfer` — a data-valued assumption (`ChordalStructure` carries the clique-tree
data, so this is a `Type`, not a `Prop`), passed as a parameter, never discharged inside the project.
This keeps the downstream results (L6, L12) axiom-clean (`[propext, Classical.choice, Quot.sound]`) with
the dependence on A2 visible in their signatures (Path 3, citable to Dirac/Gavril).

Two guards baked in:
* **simplicial-target only** — fires only when the target neighborhood `B` is a clique
  (`H.IsClique B`), i.e. the target clone class is simplicial. The general copy does NOT preserve
  chordality (`C₄` counterexample); only the simplicial-target restriction is admitted.
* **chordality only** — yields `ChordalStructure (classCopy H A B)` and nothing else; never a `Φ_τ`
  bound. L6's monotonicity (L1–L2) and termination (L3) are established, not assumed.

Quantified over all `H : SimpleGraph V` so L6's symmetrization iteration (which stays on the same vertex
type `V`) can invoke it at each intermediate graph.
-/

open scoped BigOperators

namespace PaperII

variable (V : Type*) [Fintype V] [DecidableEq V]

/-- Ledger A2 as an explicit, admitted Path-3 hypothesis (data-valued): copying the clone class
`{v | N(v)=A}` toward a **simplicial** target (neighborhood `B` a clique) preserves chordality.
Threaded as a parameter, never discharged in-project. Yields ONLY chordality of the copy. -/
def A2Transfer : Type _ :=
  ∀ (H : SimpleGraph V) [DecidableRel H.Adj] (A B : Finset V),
    ChordalStructure H → H.IsClique (B : Set V) → ChordalStructure (classCopy H A B)

variable {V}

/-- Ledger L4 (Lemma 4.3): under the admitted A2 hypothesis, the class-copy toward a simplicial target
is chordal. A direct application of the threaded hypothesis (no new proof content). -/
def chordalStructure_classCopy (hA2 : A2Transfer V) (H : SimpleGraph V) [DecidableRel H.Adj]
    (A B : Finset V) (hchord : ChordalStructure H) (hclique : H.IsClique (B : Set V)) :
    ChordalStructure (classCopy H A B) :