import Mathlib
import PaperII.Chordal

/-!
# Paper II — The standard definition of a chordal graph (Path 2)

`IsChordal G` is the textbook definition: every cycle of length `≥ 4` has a *chord* — an edge of `G`
joining two vertices of the cycle that is not itself one of the cycle's edges. It is a single `Prop`
about `G`, carrying no data and no classical facts, so a reviewer can audit it at a glance. This is the
hypothesis under which Paper II's Theorem 1.2 becomes UNCONDITIONAL (Path 2): the assumed bundle
`ChordalStructure` and `A2Transfer` are discharged from `IsChordal` (Dirac-family facts A1/A2/A3).
-/

open scoped BigOperators

namespace PaperII

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `IsChordal` is now defined in `PaperII.Chordal` (moved upstream in Fase 5 so `ChordalStructure`
can carry it as its `isChordal` field). This module keeps A1 (`chordal_induce`). -/

/-
**A1 (heredity).** An induced subgraph of a chordal graph is chordal. (A cycle in `G.induce W`
maps to a cycle of the same length in `G` on the image vertices; its chord is an edge of `G` between
two support vertices, which — both endpoints lying in `W` — is an edge of `G.induce W`.)
-/
theorem chordal_induce {W : Type*} (G : SimpleGraph V) (hG : IsChordal G) (f : W ↪ V)
    (H : SimpleGraph W) (hf : ∀ a b, H.Adj a b ↔ G.Adj (f a) (f b)) : IsChordal H := by
  intro v c hc hlen; have := hG ( c.map ( show H →g G from ⟨ f, by aesop_cat ⟩ ) ) ?_ ?_ <;> simp_all +decide ;
  · obtain ⟨ x, hx, y, hy, hxy, h ⟩ := this; use x, hx, y, hy, hxy; contrapose! h; aesop;
  · convert hc.map _;
