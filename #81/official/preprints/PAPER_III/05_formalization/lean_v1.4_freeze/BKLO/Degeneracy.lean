/-
# Degeneracy of an edge set on `ℕ` (the parameter that controls §5 embeddings).

The absorbers built in `BKLO.AbsorberExists` live on the vertex type `ℕ`, with the vertices of the
absorbed set `H` at the bottom (`Below b H`) and all new vertices above (`b ≤ v`).  To *place* such
an absorber inside a dense host graph `G` one embeds its vertices one at a time in increasing order;
each new vertex must land in the common neighbourhood of the images of its already-embedded
neighbours.  The relevant parameter is therefore the **back-degree** in the natural order of `ℕ`:

  `NatDegen d A` — every vertex of `A` has at most `d` neighbours smaller than itself.

In a host with `δ(G) ≥ (1 - 1/(d+1) + ε)n` every `d`-set has a linear common neighbourhood, so a
`d`-degenerate absorber can be embedded greedily (`BKLO.exists_embedding`).  For the triangle
threshold `9/10` this allows `d ≤ 9`.
-/
import BKLO.HasAbs

open Finset

namespace BKLO

/-- **Absorbers with degeneracy control (the §8.1 output that §5 consumes).**

`SparseAbsorber d b H A` says: `A` is an absorber for `H` which introduces no vertex below `b`,
has no edge with both ends below `b` (so no edge inside the absorbed set), and in which every
vertex has at most `d` smaller neighbours. -/
structure SparseAbsorber (d b : ℕ) (H A : Finset (Sym2 ℕ)) : Prop where
  absorber : IsAbsorber A H
  touches : Touches b A
  supp_le : ∀ v ∈ supp A, v ∈ supp H ∨ b ≤ v
  degen : NatDegen d A

/-- **The §8.1 interface with degeneracy, over `ℕ`.**  Every loopless triangle-divisible edge set
supported below `b` has an absorber of back-degeneracy at most `d` using only vertices `≥ b`. -/
def SparseAbsorberExistence (d : ℕ) : Prop :=
  ∀ (b : ℕ) (H : Finset (Sym2 ℕ)), (∀ e ∈ H, ¬ e.IsDiag) → Below b H → TriDivisible H →
    ∃ A : Finset (Sym2 ℕ), SparseAbsorber d b H A

end BKLO
