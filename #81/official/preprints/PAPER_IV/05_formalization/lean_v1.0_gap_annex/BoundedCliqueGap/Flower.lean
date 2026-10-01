import BoundedCliqueGap.CSLower
import BoundedCliqueGap.NuAdd

/-
`BoundedCliqueGap.Flower` — declaration-level extract of the Route B
triangle-packing development.  Only the declarations in the constant cone of
`BoundedCliqueGap.chordal_gap_linear_cliqueFree` were kept (plus the few that
the retained sources need in order to elaborate); the module documentation
below is the original one and may advertise results that were pruned away.
-/

/-
# Rung H1 — the FLOWER: one shared clique, many overlapping territories

The flower is the residual configuration named at the end of the G run: a
shared clique `K` whose edge capacity is claimed by many territories at once.
Formally, on the vertex type `Fin κ ⊕ Fin t`:

* the left part `Fin κ` is the shared clique `K`;
* each private vertex `x : Fin t` belongs to the territory `terr x : Fin m`;
* territory `i` has separator `S i ⊆ K`, and the private vertices of
  territory `i` together with `S i` form a clique.

So `p i` (the private size of territory `i`) is the number of `x` with
`terr x = i`, `s i = |S i|`, and the flower's own vertex count is `κ + t`.
Separators may overlap arbitrarily, `m` is unbounded and all sizes are
unbounded.

`flower_gap_linear` closes the rung in the regime `s i ≤ p i` (each separator
at most as large as the private part it serves):

  `value ≤ ν₃(flower) + 10·(κ + t)`,

linear in the flower's own vertex count, with an absolute constant.  The
proof is an edge-disjoint decomposition of the flower into the shared clique
`K` and the territory graphs `CS(P i, S i)` (private part a clique, separator
independent — the separator edges belong to `K`), plus the matching lower
bounds `nu3_clique_ge` (Bose) on `K` and `nu3_CS_ge` (Bose + Vizing donation)
on each territory, against the LP ceiling `value ≤ |E|/3`.  The regime
hypothesis `s i ≤ p i` is exactly what makes the territory's *own* private
edges able to absorb its cross edges, so that no separator edge has to be
donated; that is the point at which the general flower needs the list edge
colouring of rung H0 instead (see `REPORT_H.md`).
-/

namespace BoundedCliqueGap

open Finset

/-! ## The flower -/

section FlowerDef

variable {kappa t m : ℕ}

variable (terr : Fin t → Fin m) (S : Fin m → Finset (Fin kappa))

/-- The private part of territory `i`. -/
def privSet (terr : Fin t → Fin m) (i : Fin m) : Finset (Fin t) :=
  Finset.univ.filter (fun x => terr x = i)

@[simp] lemma mem_privSet_iff {terr : Fin t → Fin m} {i : Fin m} {x : Fin t} :
    x ∈ privSet terr i ↔ terr x = i := by
  simp [privSet]

/-- The number of private vertices of territory `i`. -/
def privCard (terr : Fin t → Fin m) (i : Fin m) : ℕ := (privSet terr i).card

/-- The size of the separator of territory `i`. -/
def sepCard (S : Fin m → Finset (Fin kappa)) (i : Fin m) : ℕ := (S i).card

/-! ## The edge-disjoint decomposition -/

/-! ## Transferring the two lower bounds into the flower -/

/-! ## The edge count of the flower -/

/-! ## The flower gap theorem -/

/-! ## Axiom audit -/

end FlowerDef

end BoundedCliqueGap
