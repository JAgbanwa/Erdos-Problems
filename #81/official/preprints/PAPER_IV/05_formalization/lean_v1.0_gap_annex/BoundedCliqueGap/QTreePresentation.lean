import BoundedCliqueGap.Ladder
import BoundedCliqueGap.QTree

/-
`BoundedCliqueGap.QTreePresentation` — declaration-level extract of the Route B
triangle-packing development.  Only the declarations in the constant cone of
`BoundedCliqueGap.chordal_gap_linear_cliqueFree` were kept (plus the few that
the retained sources need in order to elaborate); the module documentation
below is the original one and may advertise results that were pruned away.
-/

/-
# Rung Q3 (part 2) — presented tree flowers

`TreePresentation H` presents the abstract tree flower of rung Q2 inside a
concrete graph `H`, exactly as `ChainPresentation` presents the chain flower.
Its charge is the same `(n − |S₀|) + t`, and the two transport theorems

* `TreePresentation.gap_of_moderate` — unconditional, constant `10`;
* `TreePresentation.gap_of_interface` — from `TreeGapFull C`, constant `C`;

carry the abstract bounds of rung Q2 to `H`.

`ChainPresentation.toTree` shows the new vocabulary contains the old one
(intervals are the subtrees of a path), with the same charge; so every witness
of the L-, M- and N-ladders survives verbatim.
-/

namespace BoundedCliqueGap

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **A tree-flower presentation of a graph `H`**: an injective labelling of
`H`'s non-isolated vertices by `Fin n ⊕ Fin t` under which `H` is exactly the
abstract tree flower `treeFlower sub S₀ terr sep`, together with the data
witnessing that `sub` really is a family of subtrees of a rooted tree. -/
structure TreePresentation (H : SimpleGraph V) where
  /-- the number of hub vertices -/
  n : ℕ
  /-- the number of private vertices -/
  t : ℕ
  /-- the number of territories -/
  m : ℕ
  /-- a strict bound for the node indices of the skeleton tree -/
  r : ℕ
  /-- the parent function of the skeleton tree -/
  par : ℕ → ℕ
  /-- the root node of each hub vertex's subtree -/
  rt : Fin n → ℕ
  /-- the subtree occupied by each hub vertex -/
  sub : Fin n → Finset ℕ
  /-- the hub-hole: the parent separator, confined to the root node -/
  S0 : Finset (Fin n)
  /-- the territory of each private vertex -/
  terr : Fin t → Fin m
  /-- the port set of each territory -/
  sep : Fin m → Finset (Fin n)
  isRep : IsSubtreeRep par rt sub
  hS0 : ∀ x ∈ S0, rt x = 0
  hr : ∀ x, rt x < r
  /-- the labelling -/
  emb : Fin n ⊕ Fin t → V
  emb_inj : Function.Injective emb
  emb_adj : ∀ a b, H.Adj (emb a) (emb b) ↔ (treeFlower sub S0 terr sep).Adj a b
  emb_supp : ∀ u v, H.Adj u v → ∃ a, emb a = u

/-! ## Axiom audit -/

end BoundedCliqueGap
