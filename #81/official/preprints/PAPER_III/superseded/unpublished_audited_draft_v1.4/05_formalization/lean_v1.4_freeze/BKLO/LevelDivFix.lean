/-
# Divisibility fixing at a vortex level.

BKLO §10 runs the cover-down along a vortex `W ⊇ W' ⊇ W'' ⊇ … ⊇ U`, and the cover-down lemma is
only available at levels which induce a **triangle-divisible** edge set: this is what the repaired
input `BKLO.CoverDownK3Div` (`BKLO/CoverDownRepaired.lean`) asks for, and what the parity
counterexample `BKLO.not_coverDownK3At_ge_three` shows cannot be dispensed with.

Divisible levels are not something the level-sampling of `BKLO/LevelSampling.lean` can deliver — a
prescribed size and an even induced degree at every vertex are incompatible demands in general (a
complete host graph has no even induced subgraph of even order).  What BKLO do instead, and what
this file isolates, is *divisibility fixing*: one removes from the current edge set a **bounded
family of triangles** whose apexes lie outside the level, so that

* the removed edges inside the level are exactly a chosen set `L`, chosen to correct the parity of
  every vertex of the level and the number of edges modulo three;
* every vertex loses only a bounded number of edges, so no density hypothesis is disturbed;
* the removed triangles are part of the decomposition being built — nothing is lost.

Crucially the fixing family lies **inside the ambient set** `W` it is applied to: all three
vertices of each of its triangles are in `W`.  Removing such a family therefore leaves
`F ∩ cliqueEdges W` triangle-divisible if it was (each triangle removes three edges of it and drops
two from each of three degrees), which is what lets the recursion fix level after level without
ever destroying the divisibility already achieved one level up.

The fix is additionally required to avoid a prescribed set `Y ⊆ X` — in the recursion, the bottom
set of the vortex — so that the bottom set's own density is not eroded once per level.

## Status

`LevelDivFixProp` is stated here as an **interface**, not proved.  It is carried explicitly as a
hypothesis by everything downstream, so that the exact residual of the cover-down vehicle is
visible in the statement of every theorem that uses it.
-/
import BKLO.CoverDown
import BKLO.ClassPairing

open Finset

namespace BKLO

/-- **Divisibility fixing at one level.**  Let `X ⊆ W` be a level, at most half the size of `W`,
inside a dense edge set `F` which is also dense inside `X`, and let `Y ⊆ X` be at most a quarter of
`X` (the bottom set of the vortex).  Then a bounded family of triangles of `F`, all of whose
vertices lie in `W`, can be removed so that the edge set induced on `X` becomes triangle-divisible,
at a cost of at most `12` edges at any vertex, and without touching any edge inside `Y`. -/
def LevelDivFixProp : Prop :=
  ∀ {V : Type} [DecidableEq V] (W X Y : Finset V) (F : Finset (Sym2 V)),
    X ⊆ W → Y ⊆ X → 2 * X.card ≤ W.card → 4 * Y.card ≤ X.card → 100 ≤ X.card →
    F ⊆ cliqueEdges W →
    (∀ v ∈ W, (9 / 10 : ℝ) * (W.card : ℝ) ≤ (edeg F v : ℝ)) →
    (∀ v ∈ X, (9 / 10 : ℝ) * (X.card : ℝ) ≤ (edeg (F ∩ cliqueEdges X) v : ℝ)) →
    ∃ Q : Finset (Finset V), TriFamilyIn F Q ∧ (∀ t ∈ Q, t ⊆ W) ∧
      (∀ v : V, edeg (famEdges Q) v ≤ 12) ∧
      Disjoint (famEdges Q) (cliqueEdges Y) ∧
      TriDivisible ((F \ famEdges Q) ∩ cliqueEdges X)

end BKLO
