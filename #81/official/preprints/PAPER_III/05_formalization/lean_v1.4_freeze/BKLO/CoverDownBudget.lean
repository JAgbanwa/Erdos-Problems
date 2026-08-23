/-
# The slack absorbs the used edges (BKLO Lemma 10.3, part B: the budget arithmetic)

At each apex `x` of the greedy loop of Lemma 10.3, Dirac is applied to the **unused** part of the
neighbourhood — the edge set `E \ D`, where `E = H[N_H(x,V)]` and `D` is what earlier apices have
used.  For Dirac to apply, `E \ D` must have every vertex of degree `≥ |N|/2`.

Condition (ii) of Lemma 10.3 gives `δ(E) ≥ |N|/2 + γ|V|`, and the accumulated used degree stays
`≤ γ|V|` (condition (iii)).  This file records, `sorry`-free, that the slack `γ|V|` of (ii) exactly
absorbs the `γ|V|` used edges: the unused part keeps minimum degree `≥ |N|/2`.  It is a one-line
consequence of the project's edge-degree deletion bound `BKLO.edeg_le_edeg_sdiff_add_edeg`.

This is the quantitative heart of part (B); what remains to close Lemma 10.3 is the bookkeeping that
the accumulated `D` really has per-vertex degree `≤ γ|V|` (each earlier apex uses each neighbour at
most once, and a vertex is a neighbour of at most `d_H(y,U) ≤ γ|V|/2` apices — condition (iii)), and
the conversion of the unused edge set into the `SimpleGraph` `BKLO.perfectMatchingDirac_holds`
consumes (via `BKLO.exists_isMatchingAvoiding_of_dirac`).

Everything here is `sorry`-free.
-/
import BKLO.SetGraph

open Finset

namespace BKLO

variable {V : Type} [DecidableEq V]

/-- **The slack absorbs the used edges.**  If every vertex has degree `≥ h + d` in `E` (the `h + d`
of Lemma 10.3(ii), `h = |N|/2`, `d` the slack) and the used set `D` has degree `≤ d` at `v`, then the
unused part `E \ D` still has degree `≥ h` at `v` — the hypothesis Dirac needs. -/
theorem edeg_sdiff_ge_of_slack {E D : Finset (Sym2 V)} {v : V} {h d : ℕ}
    (hE : h + d ≤ edeg E v) (hD : edeg D v ≤ d) : h ≤ edeg (E \ D) v := by
  have hle := edeg_le_edeg_sdiff_add_edeg E D v
  omega

/-- **Uniform form.**  If `E` has minimum degree `≥ h + d` over a set `N` and the used set `D` has
maximum degree `≤ d` over `N`, then `E \ D` has minimum degree `≥ h` over `N`. -/
theorem edeg_sdiff_ge_of_slack_forall {E D : Finset (Sym2 V)} {N : Finset V} {h d : ℕ}
    (hE : ∀ v ∈ N, h + d ≤ edeg E v) (hD : ∀ v ∈ N, edeg D v ≤ d) :
    ∀ v ∈ N, h ≤ edeg (E \ D) v :=
  fun v hv => edeg_sdiff_ge_of_slack (hE v hv) (hD v hv)

end BKLO
