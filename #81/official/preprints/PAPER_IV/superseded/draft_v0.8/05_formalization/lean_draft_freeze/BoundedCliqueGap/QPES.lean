import BoundedCliqueGap.Ladder

/-
`BoundedCliqueGap.QPES` — declaration-level extract of the Route B
triangle-packing development, re-expressed against this tree's own chordality
primitives.

The original module carried a second encoding of chordality (a *peeling list*
`IsPeelOrder`, and `IsChordal` as the existence of one) together with the
lemmas turning such a list into a numbering.  That encoding duplicated
`SimpleGraph.IsChordal` and `SimpleGraph.IsPEO` of `PaperIV/ChordalStructure.lean`
and `PaperIV/CliqueTree/PEO.lean`, so it was dropped: only the numbering
`RevPES` — the interface actually consumed by the clique-tree recursion —
survives here, and it is produced from `SimpleGraph.IsPEO` in
`BoundedCliqueGap/PEOBridge.lean`.
-/

/-
# Rung Q3 (part 1) — perfect elimination orderings as a numbering

For the clique-tree construction of rung Q3 chordality is used through a
**numbering** `ord : V → ℕ` of the vertices, injective and bounded by `|V|`,
with the property that the neighbours of a vertex that carry *smaller* numbers
are pairwise adjacent.  (This is the reverse of an elimination order: the
elimination peels the largest number last.)
-/

namespace BoundedCliqueGap

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## The numbering -/

/-- A **reverse perfect elimination numbering**: `ord` numbers the vertices
injectively below `|V|`, and the neighbours of any vertex that carry smaller
numbers are pairwise adjacent. -/
structure RevPES (H : SimpleGraph V) (ord : V → ℕ) : Prop where
  /-- distinct vertices get distinct numbers -/
  inj : Function.Injective ord
  /-- the numbers fit in `range |V|` -/
  lt : ∀ v, ord v < Fintype.card V
  /-- the smaller-numbered neighbours of a vertex form a clique -/
  down : ∀ v u w, H.Adj v u → H.Adj v w → ord u < ord v → ord w < ord v → u ≠ w →
    H.Adj u w

end BoundedCliqueGap
