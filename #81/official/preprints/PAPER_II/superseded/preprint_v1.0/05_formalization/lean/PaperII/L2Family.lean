import PaperII.CloneCopy

/-!
# Paper II — The interpolation family `H_k` for L2, built around the frozen `classCopy`

`moveGraph G A B M` reassigns the vertices in `M` (a subset of the open-neighborhood clone class
`{v | N(v)=A}`) to have neighborhood `B`, leaving everything else as in `G`. This is the L2
interpolation: as `M` grows from `∅` to the whole `A`-class, `G` deforms into `classCopy G A B`.

**Endpoint guard (crucial for L6 soundness):** `H_k` is designed around the FROZEN `classCopy`, so its
full-move endpoint is exactly that operation — the same graph L3 proves termination for. With
`M = sourceClass G A` the relation reduces definitionally to `classCopyRel`, so the "D7 bridge"
(`moveGraph (whole class) = classCopy`) is essentially `rfl` (`moveGraph_sourceClass` below), not a
separately-risky normal-form lemma.
-/

open scoped BigOperators
open Finset

namespace PaperII

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The open-neighborhood clone class of neighborhood `A`. -/
def sourceClass (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) : Finset V :=
  univ.filter (fun v => G.neighborFinset v = A)

/-- Relation for the partial move: the vertices of `M ⊆ {v|N(v)=A}` are reassigned neighborhood `B`. -/
def moveRel (G : SimpleGraph V) [DecidableRel G.Adj] (A B M : Finset V) : V → V → Prop := fun a b =>
  ((G.neighborFinset a = A → a ∉ M) ∧ (G.neighborFinset b = A → b ∉ M) ∧ G.Adj a b)
  ∨ (G.neighborFinset a = A ∧ a ∈ M ∧ b ∈ B)
  ∨ (G.neighborFinset b = A ∧ b ∈ M ∧ a ∈ B)

instance (G : SimpleGraph V) [DecidableRel G.Adj] (A B M : Finset V) :
    DecidableRel (moveRel G A B M) := fun a b => by unfold moveRel; infer_instance

/-- The interpolation graph `H` after moving the subset `M` of the `A`-class onto `B`. -/
def moveGraph (G : SimpleGraph V) [DecidableRel G.Adj] (A B M : Finset V) : SimpleGraph V :=
  SimpleGraph.fromRel (moveRel G A B M)

/-- **Endpoint / D7 bridge:** moving the entire source class yields the frozen `classCopy`.
Reduces to `classCopyRel` because `x ∈ sourceClass G A ↔ N(x) = A`. -/
theorem moveGraph_sourceClass (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V) :
    moveGraph G A B (sourceClass G A) = classCopy G A B := by
  unfold moveGraph classCopy
  congr 1
  funext a b
  unfold moveRel classCopyRel sourceClass
  simp only [mem_filter, mem_univ, true_and]
  by_cases ha : G.neighborFinset a = A <;> by_cases hb : G.nei