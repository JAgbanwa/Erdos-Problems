import PaperII.Model

/-!
# Paper II — Clone classes and simplicial vertices (ledger D5, D6)

`IsClone`  (D5): open-neighborhood clones `N(u) = N(v)` (forces `u,v` nonadjacent).
`IsSimplicial` (D6): the neighborhood of `v` induces a clique.
-/

open scoped BigOperators

namespace PaperII

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- D5 (clone): `u` and `v` are open-neighborhood clones, `N_G(u) = N_G(v)`. -/
def IsClone (G : SimpleGraph V) (u v : V) : Prop := G.neighborSet u = G.neighborSet v

/-- D6 (simplicial): the neighborhood of `v` induces a clique. -/
def IsSimplicial (G : SimpleGraph V) (v : V) : Prop := G.IsClique (G.neighborSet v)

/-- Open-neighborhood clones are nonadjacent (ledger D5 remark). -/
theorem not_adj_of_isClone (G : SimpleGraph V) {u v : V} (h : IsClone G u v) :
    ¬ G.Adj u v := by
  intro hadj
  have hmem : v ∈ G.neighborSet v := by
    have : v ∈ G.neighborSet u := (SimpleGraph.mem_neighborSet _ _ _).2 hadj
    rwa [h] at this
  exact G.irrefl ((SimpleGraph.mem_neighborSet _ _ _).1 hmem)

/-- `IsClone` is symmetric. -/
theorem isClone_comm (G : SimpleGraph V) {u v : V} (h : IsClone G u v) : IsClone G v u := by
  unfold IsClone at h 