/-
  Part B (Phase 2) — the Transformer structure and its interface to `reroute`.

  Corrected by the `Switcher.elim` finding: a transformer absorbs a `3`-divisible config, not a
  single edge. A `Transformer` bundles a base triangle decomposition, an absorbing one, and the
  config, with `coveredEdges absorb = coveredEdges base ∪ config`. A bank of pairwise
  edge-disjoint transformers feeds `reroute` (already proved), which absorbs any sub-collection
  of their configs.

  We prove the structure is INHABITED (unlike the refuted `Switcher`): any triangle of `G` is a
  trivial transformer for its own edge set. The remaining research kernel is the existence of a
  *nontrivial* transformer bank — one transformer per possible (non-triangle) leftover config,
  reserved disjointly — which needs the genuine BKLO construction (octahedron flexibility hooked
  to an external config). We do not assert that construction, to avoid a false lemma.
-/
import Ax2.PartB.BKLO.Reroute

namespace Ax2.BKLO

open Finset Ax2 SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A **transformer**: a base triangle decomposition and an absorbing one differing by a
`3`-divisible config, `coveredEdges absorb = coveredEdges base ∪ config`. -/
structure Transformer (V : Type*) [DecidableEq V] where
  base : Finset (Finset V)
  absorb : Finset (Finset V)
  config : Finset (Sym2 V)
  baseDisj : EdgeDisjoint base
  absorbDisj : EdgeDisjoint absorb
  rel : coveredEdges absorb = coveredEdges base ∪ config

/-- **The transformer structure is inhabited** (contrast `Switcher.elim`). Any triangle `t` of
`G` is a transformer for its own edge set: empty base, absorbing decomposition `{t}`, config
`triEdges t`. -/
def trivialTransformer (t : Finset V) : Transformer V where
  base := ∅
  absorb := {t}
  config := triEdges t
  baseDisj := by intro a ha; simp at ha
  absorbDisj := by
    intro a ha b hb hab
    simp only [Finset.mem_singleton] at ha hb
    exact absurd (ha.trans hb.symm) hab
  rel := by simp [coveredEdges]

end Ax2.BKLO
