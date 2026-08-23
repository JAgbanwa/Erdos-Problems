/-
  Part B (Phase 2) — the CORRECTED absorbing gadget.

  `Switcher.elim` refuted the single-edge toggle (a triangle family covers a multiple of 3
  edges, so no toggle can add exactly one). The correct atom absorbs a **3-divisible flexible
  unit**: an edge set carrying two *distinct* edge-disjoint triangle decompositions. The
  canonical such unit is the octahedron `K_{2,2,2}` (12 edges = 3·4, all degrees even), which
  has two triangle decompositions sharing no triangle.

  We prove `FlexUnit` is inhabited by exhibiting the octahedron on `Fin 6` — the concrete
  satisfiability contrast with `Switcher.elim` (which showed the naive model empty).
-/
import Ax2.PartB.BKLO.Defs

namespace Ax2.BKLO

open Finset Ax2

/-- A **flexible unit**: an edge set with two *distinct* edge-disjoint triangle
decompositions. This is the correct atomic absorber shape (3-divisible, unlike the refuted
single-edge switcher). -/
structure FlexUnit (V : Type*) [DecidableEq V] where
  edges : Finset (Sym2 V)
  dec1 : Finset (Finset V)
  dec2 : Finset (Finset V)
  card1 : ∀ t ∈ dec1, t.card = 3
  card2 : ∀ t ∈ dec2, t.card = 3
  disj1 : EdgeDisjoint dec1
  disj2 : EdgeDisjoint dec2
  cover1 : coveredEdges dec1 = edges
  cover2 : coveredEdges dec2 = edges
  distinct : dec1 ≠ dec2

/-- First triangle decomposition of the octahedron on `Fin 6`
(classes `{0,1}`, `{2,3}`, `{4,5}`). -/
def octaDec1 : Finset (Finset (Fin 6)) :=
  {{0, 2, 4}, {0, 3, 5}, {1, 2, 5}, {1, 3, 4}}

/-- Second triangle decomposition (the `c`-parity flip); shares no triangle with `octaDec1`. -/
def octaDec2 : Finset (Finset (Fin 6)) :=
  {{0, 2, 5}, {0, 3, 4}, {1, 2, 4}, {1, 3, 5}}

/-- **The corrected gadget is inhabited.** The octahedron on `Fin 6` is a flexible unit: its
12 edges carry two distinct edge-disjoint triangle decompositions. Contrast `Switcher.elim`. -/
theorem flexUnit_nonempty : Nonempty (FlexUnit (Fin 6)) :=
  ⟨{ edges := coveredEdges octaDec1
     dec1 := octaDec1
     dec2 := octaDec2
     card1 := by decide
     card2 := by decide
     disj1 := by unfold EdgeDisjoint; decide
     disj2 := by unfold EdgeDisjoint; decide
     cover1 := rfl
     cover2 := by decide
     distinct := by decide }⟩

end Ax2.BKLO
