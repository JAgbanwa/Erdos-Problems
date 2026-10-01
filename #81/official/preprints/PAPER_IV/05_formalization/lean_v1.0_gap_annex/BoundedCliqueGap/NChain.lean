import BoundedCliqueGap.LInterface

/-
`BoundedCliqueGap.NChain` — declaration-level extract of the Route B
triangle-packing development.  Only the declarations in the constant cone of
`BoundedCliqueGap.chordal_gap_linear_cliqueFree` were kept (plus the few that
the retained sources need in order to elaborate); the module documentation
below is the original one and may advertise results that were pruned away.
-/

/-
# Rung N1 — the CHAIN FLOWER

The M-lane closed with a machine-checked refutation: `G10`, the 2-tree strip on
seven vertices, is chordal but carries no mixed family, because along a strip
the attachment set of a private vertex *slides* — a single hub cannot present
it.  The primitive the witness demands is a node whose hub is not one clique
but a **chain of overlapping cliques**, consecutive ones glued along a
separator.  This file builds it.

## The shape

The hub is described by *intervals*.  Each hub vertex `a : Fin n` carries a
pair `lo a ≤ hi a` of hub indices: `a` belongs to the hubs
`K_{lo a}, …, K_{hi a}` and to no others.  Two hub vertices are adjacent
exactly when they lie in a common hub, i.e. when their intervals meet.  The
gluing separator is `T_j = K_j ∩ K_{j+1}`, and `K_j ∩ K_l ⊆ T_j` for `j < l`,
so consecutive hubs are glued along `T_j` and any further overlap is contained
in the gluing separators — the chain condition, in the form that is *closed*
under the operation that produced `G10` (a vertex of the strip lies in three
consecutive triangles, so the naive "non-consecutive hubs are disjoint" is too
narrow: the interval form is the right closure, and it contains the strip, see
`BoundedCliqueGap/NPresentation.lean`).

On top of the hub sit the same two features as in the holed flower:

* a **hole** `S₀` — the parent separator, confined to the first hub
  (`∀ a ∈ S₀, lo a = 0`), whose interior edges belong to the level above;
* **territories**: private vertices `Fin t`, grouped by `terr` into `m`
  territories, each attached to the hub by its port set `sep i`.

`r = 1` (all intervals `[0,0]`) gives back exactly the holed flower
(`chainFlower_one_hub`), so the chain flower is a common generalisation of all
three primitives of the programme.

## The pieces

`chainPiece j` is the `j`-th holed hub: the edges of `K_j` that are *new* at
`j`, i.e. the pairs with at least one endpoint in

* `chainOwn j` — the vertices entering the chain at hub `j` (and not in the
  hole),

the other endpoint lying in

* `chainHole j` — `K_j ∩ (S₀ ∪ K_{j-1})`, the hole of the `j`-th piece.

Each hub edge lies in exactly one piece (`chainPiece_cover`,
`chainPiece_disjoint`), the piece is a clique-with-an-independent-hole, and the
charges add up: `∑_j |chainOwn j| = n − |S₀|` (`sum_chainOwn_card`), which is
the "each hub vertex counted once along the chain" of the rung.

## The LP ceiling

The dual weight `chainW a g c d` puts `a` on a hub edge internal to one piece,
`g` on a **gluing** edge (an edge whose endpoints enter the chain at different
hubs, or which meets the hole), `c` on a cross edge and `d` on a private edge.
Feasibility is the six-inequality system `1 ≤ 3a, 3g, a+2c, g+2c, 2c+d, 3d`
(`chainW_triangle_ge`), and the ceiling is `chainFlower_value_le`.  The
`1/2`-on-gluing-separators instance suggested by the M report is
`chainFlower_value_le_half_gluing`; the uniform `1/3` instance is what rung N2
uses.
-/

namespace BoundedCliqueGap

open Finset

section ChainDef

variable {n t m : ℕ}

variable (lo hi : Fin n → ℕ) (S0 : Finset (Fin n)) (terr : Fin t → Fin m)
  (sep : Fin m → Finset (Fin n))

/-! ## The degeneration to the holed flower -/

end ChainDef

/-! ## The pieces of the chain -/

section ChainPieces

variable {n t : ℕ}

/-- The hub vertices **entering the chain at hub `j`**: those with `lo a = j`,
outside the hole. -/
def chainOwn (lo : Fin n → ℕ) (S0 : Finset (Fin n)) (j : ℕ) : Finset (Fin n) :=
  univ.filter (fun a => lo a = j ∧ a ∉ S0)

variable (lo hi : Fin n → ℕ) (S0 : Finset (Fin n))

@[simp] lemma mem_chainOwn {a : Fin n} {j : ℕ} :
    a ∈ chainOwn lo S0 j ↔ lo a = j ∧ a ∉ S0 := by simp [chainOwn]

variable {lo hi S0}

end ChainPieces

/-! ## The charge of the chain adds up -/

section ChainCharge

variable {n : ℕ}

/-- **The charge identity of the chain**: each hub vertex outside the hole is
new at exactly one hub, so the sizes of the `chainOwn` sets add up to
`n − |S₀|`.  This is the "each hub vertex counted once along the chain" of the
rung. -/
theorem sum_chainOwn_card (lo hi : Fin n → ℕ) (S0 : Finset (Fin n)) (r : ℕ)
    (hlohi : ∀ a, lo a ≤ hi a) (hr : ∀ a, hi a < r) :
    ∑ j ∈ Finset.range r, (chainOwn lo S0 j).card = n - S0.card := by
  classical
  have hfib : (S0ᶜ : Finset (Fin n)).card
      = ∑ j ∈ Finset.range r, ((S0ᶜ : Finset (Fin n)).filter (fun a => lo a = j)).card := by
    refine Finset.card_eq_sum_card_fiberwise (f := lo) (fun a _ => ?_)
    have h1 := hlohi a
    have h2 := hr a
    exact Finset.mem_range.2 (by omega)
  have hsets : ∀ j, (S0ᶜ : Finset (Fin n)).filter (fun a => lo a = j) = chainOwn lo S0 j := by
    intro j
    ext a
    simp only [Finset.mem_filter, Finset.mem_compl, mem_chainOwn]
    tauto
  calc ∑ j ∈ Finset.range r, (chainOwn lo S0 j).card
      = ∑ j ∈ Finset.range r, ((S0ᶜ : Finset (Fin n)).filter (fun a => lo a = j)).card :=
        Finset.sum_congr rfl (fun j _ => by rw [hsets j])
    _ = (S0ᶜ : Finset (Fin n)).card := hfib.symm
    _ = n - S0.card := by rw [Finset.card_compl, Fintype.card_fin]

end ChainCharge

/-! ## The dual weight of the chain flower -/

section ChainLP

variable {n t m : ℕ}

variable (lo hi : Fin n → ℕ) (S0 : Finset (Fin n)) (terr : Fin t → Fin m)
  (sep : Fin m → Finset (Fin n)) (a g c d : ℚ)

/-! ### The edge classes of the chain flower -/

end ChainLP

/-! ## Axiom audit -/

end BoundedCliqueGap
