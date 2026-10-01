import BoundedCliqueGap.QTree

/-
`BoundedCliqueGap.TTreeLift` — declaration-level extract of the Route B
triangle-packing development.  Only the declarations in the constant cone of
`BoundedCliqueGap.chordal_gap_linear_cliqueFree` were kept (plus the few that
the retained sources need in order to elaborate); the module documentation
below is the original one and may advertise results that were pruned away.
-/

/-
# T3 — the ported Y lift, instantiated on the real `treeFlower`

Rung T3 asks for the Y2 lift (`hub_territory_lift`, `BoundedCliqueGap.YLift`) on the
actual tree flower of the Q-ladder (`treeFlower`, `BoundedCliqueGap.QTree`), with
`NoCrossBid` verified from the tree's own anatomy.  This file carries that out
and reports exactly where it stops.

## What instantiates, unconditionally

Take as territories the `m` port groups of the flower:

  `treePorts terr i` = the ports `x` with `terr x = i`, as vertices `Sum.inr x`,
  `treeSep sep i`    = the separator `sep i`, as vertices `Sum.inl a`,

and as hub the graph `treeHubGraph` of the hub–hub edges of the flower.  Then

* `treeFlower_noCrossBid` — **`NoCrossBid` holds, with no hypothesis at all.**
  The `card_pieces_of_edge_le_two` phenomenon of `BoundedCliqueGap.TTree` (a *hub* edge is
  claimed by up to two nodes) does not bite here: a territory of the Y lift owns
  only *port-incident* edges (`territoryGraph P S` has no edge inside `S`), and
  ports of distinct groups are distinct vertices, while ports and hub vertices
  live in different summands.  So the two families are disjoint for type
  reasons, and the cross-bidding condition is discharged outright;
* `treeFlower_territory_le`, `treeFlower_hub_le`, `treeFlower_ports_sep_disjoint`,
  `treeFlower_hub_territory_edgeDisjoint` — the remaining structural hypotheses
  of the lift.

## Where it stops — the mixed triangle, with a machine-checked witness

The lift needs every triangle in the support to belong to the hub or to a single
territory.  A triangle of the tree flower with **exactly one** port and two hub
vertices belongs to neither: its hub–hub edge is not an edge of any
`territoryGraph`.  Triangles with `0`, `2` or `3` ports are fine
(`treeFlower_hub_triangle_of_no_port`, `treeFlower_territory_triangle`), so the
mixed type is the *whole* obstruction, and it is not vacuous:
`treeFlower_mixed_triangle_witness` exhibits one by `decide` on the two-node,
one-port flower.

Hence the honest headline is conditional on the support avoiding that type:

  `treeFlower_gap_of_hubGap_of_noMixed` :
      hub gap `c₀` + no mixed triangle in the support →
      `value ≤ ν₃(treeFlower) + c₀ + 8·(n + t)`.

## Why a conditional `treeGapFull` is not reachable from the T2 inputs

`shellGapFull_of_treeGapFull` (rung Q2) turns `TreeGapFull C` into a gap bound
for **every** shell, in particular for shells with a *proper* separator
(`treeGapFull_gives_properSep` below).  The multipartite `ν₃` Props of rung T2
(`MCSCoveredNu3Ge`, `MCSSliverNu3Ge`) feed the complete multipartite shell only,
i.e. exactly the full-separator class (`shellGapFull_of_nu3Ge`, `BoundedCliqueGap.TGap`).
So a proper-separator input is a genuine missing hypothesis of any
`treeGapFull_of_…`, not a bookkeeping gap; it is named there as
`ShellGapFullProperSep` and nothing here assumes it.

No `sorry`, no new axioms, no `native_decide`; `#print axioms` at the end.
-/

namespace BoundedCliqueGap

open Finset

section TreeLift

variable {n t m : ℕ}

/-! ## The hub graph and the territories of a tree flower -/

/-- The hub–hub part of the tree flower. -/
def treeHubGraph (sub : Fin n → Finset ℕ) (S0 : Finset (Fin n)) (t : ℕ) :
    SimpleGraph (Fin n ⊕ Fin t) where
  Adj u v :=
    match u, v with
    | Sum.inl a, Sum.inl b => a ≠ b ∧ (sub a ∩ sub b).Nonempty ∧ ¬ (a ∈ S0 ∧ b ∈ S0)
    | _, _ => False
  symm := by
    intro u v h
    cases u <;> cases v
    · exact ⟨Ne.symm h.1, by rw [Finset.inter_comm]; exact h.2.1,
        fun hc => h.2.2 ⟨hc.2, hc.1⟩⟩
    · exact h.elim
    · exact h.elim
    · exact h.elim
  loopless := by
    constructor
    intro u h
    cases u
    · exact h.1 rfl
    · exact h.elim

/-! ## The structural hypotheses of the lift -/

variable (sub : Fin n → Finset ℕ) (S0 : Finset (Fin n)) (terr : Fin t → Fin m)
  (sep : Fin m → Finset (Fin n))

/-! ## The triangle classification -/

/-! ## The conditional lift -/

end TreeLift

/-! ## The mixed triangle is real -/

section Witness

end Witness

/-! ## What a conditional `treeGapFull` would still need -/

/-! ## Axiom audit -/

end BoundedCliqueGap
