import BoundedCliqueGap.QChordalTree
import BoundedCliqueGap.TTreeLift

/-
`BoundedCliqueGap.MTLift` — declaration-level extract of the Route B
triangle-packing development.  Only the declarations in the constant cone of
`BoundedCliqueGap.chordal_gap_linear_cliqueFree` were kept (plus the few that
the retained sources need in order to elaborate); the module documentation
below is the original one and may advertise results that were pruned away.
-/

/-
# MT — the lift with the mixed triangles removed, and the tree-level endpoint

`BoundedCliqueGap.MTMixed` measures the mixed mass and normalises it away with a linear
loss on two named classes.  This file consumes that:

* `sum_card_treePorts` — the port groups of a tree flower partition the ports,
  so the lift's territory error `8·∑|Pᵢ|` is exactly `8·t` (sharper than the
  `8·|V|` of `hub_territory_lift_card` used in `BoundedCliqueGap.TTreeLift`);
* `treeFlower_gap_of_hubGap_of_noMixed_ports` — the Y lift on the real tree
  flower, still conditional on `NoMixedTri`, with error `c₀ + 8·t`;
* **`treeFlower_gap_of_hubGap_bddSep`** — the same **without any mixed-triangle
  hypothesis** for flowers whose separators have size at most `d`, at error
  `c₀ + 8·t + d·t`;
* **`treeFlower_gap_of_hubGap_bddHubDegree`** — likewise for hub degree at most
  `D`, at error `c₀ + 8·t + D·(n+t)/2`.

## The hub interface and the endpoint

`TreeHubGapFull C` is the interface Prop for the *hub graphs* of subtree
families — an open Prop, stated in the open, never an axiom, and provably
weaker than `TreeGapFull` (`treeHubGapFull_of_treeGapFull`, via
`treeHubGraph_eq_treeFlower`).  From it:

* `treeGap_bddSep_of_treeHubGapFull` — the tree-flower gap on the
  bounded-separator class, constants explicit;
* **`chordal_gap_linear_of_treeHubGapFull`** — the universal consumer, for
  *every* chordal graph, with constant `C`.

The last one is the honest endpoint of this lane, and it needs *no*
mixed-triangle input: the Gavril presentation of a chordal graph
(`chordalTreePresentation`) has **no ports at all**
(`chordalTreePresentation_t`), so mixed triangles cannot occur there
(`noMixedTri_of_portFree`, `treeFlower_eq_hub_of_no_ports`).  In other words
the mixed triangle is a gate on the *interface* `TreeGapFull` (which quantifies
over flowers with territories, and is consumed by the shell/chain ladders), not
on the chordal consumer, whose only remaining gate is the hub gap itself.

Nothing here inverts `treeGapFull_gives_properSep`, claims a `ShellFamily` for
all chordal graphs (`G8_no_shellFamily`), uses the refuted `CliqueLeaveDecomp`,
or hides an open Prop inside a structure.

No `sorry`, no new axioms, no `native_decide`; `#print axioms` at the end.
-/

namespace BoundedCliqueGap

open Finset

section Ports

variable {n t m : ℕ}

end Ports

section Lift

variable {n t m : ℕ} (sub : Fin n → Finset ℕ) (S0 : Finset (Fin n)) (terr : Fin t → Fin m)
  (sep : Fin m → Finset (Fin n))

end Lift

/-! ## The hub graph as a tree flower, and the port-free case -/

section HubAsFlower

variable {n t m : ℕ} (sub : Fin n → Finset ℕ) (S0 : Finset (Fin n))

/-- The hub graph of a subtree family is itself a tree flower: take one
territory per port and an empty separator. -/
theorem treeHubGraph_eq_treeFlower :
    treeHubGraph sub S0 t
      = treeFlower sub S0 (fun x : Fin t => x) (fun _ : Fin t => (∅ : Finset (Fin n))) := by
  ext u v
  cases u with
  | inl a =>
    cases v with
    | inl b => rfl
    | inr y => simp [treeHubGraph]
  | inr x =>
    cases v with
    | inl b => simp [treeHubGraph]
    | inr y =>
      constructor
      · intro h; exact h.elim
      · rintro ⟨hne, hxy⟩; exact hne hxy

/-- A **port-free** tree flower *is* its hub graph. -/
theorem treeFlower_eq_hub_of_no_ports (terr : Fin t → Fin m) (sep : Fin m → Finset (Fin n))
    (hemp : IsEmpty (Fin t)) :
    treeFlower sub S0 terr sep = treeHubGraph sub S0 t := by
  ext u v
  cases u with
  | inl a =>
    cases v with
    | inl b => rfl
    | inr y => exact hemp.elim y
  | inr x => exact hemp.elim x

end HubAsFlower

/-! ## The hub interface -/

/-! ## The endpoint: every chordal graph -/

section Chordal

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **The Gavril presentation is port-free**, so its flower is its own hub
graph: no mixed triangle can occur in the universal consumer. -/
theorem chordalTreePresentation_flower_eq_hub {H : SimpleGraph V} {ord : V → ℕ}
    (hpes : RevPES H ord) :
    treeFlower (chordalTreePresentation hpes).sub (chordalTreePresentation hpes).S0
        (chordalTreePresentation hpes).terr (chordalTreePresentation hpes).sep
      = treeHubGraph (chordalTreePresentation hpes).sub (chordalTreePresentation hpes).S0
          (chordalTreePresentation hpes).t := by
  refine treeFlower_eq_hub_of_no_ports _ _ _ _ ?_
  rw [show (chordalTreePresentation hpes).t = 0 from rfl]
  infer_instance

end Chordal

/-! ## Calibration against the witness -/

section Calibration

end Calibration

/-! ## Axiom audit -/

end BoundedCliqueGap
