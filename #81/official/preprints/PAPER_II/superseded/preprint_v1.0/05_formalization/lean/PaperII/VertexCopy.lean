import PaperII.Model

/-!
# Paper II — Vertex-copy operation (ledger D7) and its structural lemmas

`copyVertex G v u` = `G_{v→u}`: delete all edges at `v`, then join `v` to `N_G(u)`.

Realized as Mathlib's `SimpleGraph.replaceVertex u v` ("replace `v` by a copy of `u`, removing the
`u–v` edge if present") — this is exactly ledger D7.  Reusing `replaceVertex` gives the adjacency
spec and (later) the edge-count identity from Mathlib.
-/

open scoped BigOperators

namespace PaperII

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Ledger D7: the graph `G_{v→u}`. -/
def copyVertex (G : SimpleGraph V) (v u : V) : SimpleGraph V := G.replaceVertex u v

instance (G : SimpleGraph V) [DecidableRel G.Adj] (v u : V) :
    DecidableRel (copyVertex G v u).Adj := by unfold copyVertex; infer_instance

/-- The copied vertex `v` acquires exactly `u`'s neighborhood: for `w ≠ v`,
    `v ~ w` in `G_{v→u}` iff `u ~ w` in `G`. -/
theorem copyVertex_adj_v (G : SimpleGraph V) (v u w : V) (hw : w ≠ v) :
    (copyVertex G v u).Adj v w ↔ G.Adj u w := by
  unfold copyVertex; exact G.adj_replaceVertex_iff_of_ne_right u hw

/-- Edges away from the copied vertex are unchanged: for `a ≠ v` and `b ≠ v`,
    `a ~ b` in `G_{v→u}` iff `a ~ b` in `G`. -/
theorem copyVertex_adj_of_ne (G : SimpleGraph V) (v u a b : V) (ha : a ≠ v) (hb : b ≠ v) :
    (copyVertex G v u).Adj a b ↔ G.Adj a b := by
  unfold copyVertex; exact G.adj_replaceVertex_iff_of_ne u ha hb

/-- In `G_{v→u}` the copied vertex `v` is not adjacent to its target `u`. -/
theorem not_copyVertex_adj (G : SimpleGraph V) (v u : V) :
    ¬ (copyVertex G v u).Adj u v := by
  unfold copyVertex; exact G.not_a