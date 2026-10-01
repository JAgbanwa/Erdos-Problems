import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The literal class-copy operation used by the near-regime copy path. -/

namespace PaperIV.ClassCopy

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Reassign every vertex whose open neighbourhood is `A` the target
neighbourhood `B`, retaining all other adjacencies. -/
def rel (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V) : V → V → Prop :=
  fun a b =>
    (G.neighborFinset a ≠ A ∧ G.neighborFinset b ≠ A ∧ G.Adj a b)
      ∨ (G.neighborFinset a = A ∧ b ∈ B)
      ∨ (G.neighborFinset b = A ∧ a ∈ B)

instance (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V) :
    DecidableRel (rel G A B) := fun a b => by
  unfold rel
  infer_instance

/-- The graph obtained by the literal class-copy relation. -/
def graph (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V) : SimpleGraph V :=
  SimpleGraph.fromRel (rel G A B)

instance (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V) :
    DecidableRel (graph G A B).Adj := fun a b => by
  unfold graph
  rw [SimpleGraph.fromRel_adj]
  infer_instance

omit [DecidableEq V] in
theorem graph_adj_iff (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V)
    (a b : V) : (graph G A B).Adj a b ↔
      a ≠ b ∧ (rel G A B a b ∨ rel G A B b a) :=
  by
    unfold graph
    exact SimpleGraph.fromRel_adj (rel G A B) a b

end PaperIV.ClassCopy
