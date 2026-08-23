/-
  Part B — BKLO transfer, kept AXIOMATIC (the entire non-proved perimeter lives here).

  B. Barber, D. Kühn, A. Lo, D. Osthus, *Edge-decompositions of graphs with high minimum
  degree*, Adv. Math. 288 (2016), 337–385, Theorem 1.3, bundled with the Haxell–Rödl
  fractional→approximate bridge (P. E. Haxell, V. Rödl, Combinatorica 21 (2001), 13–38,
  Cor. 4.4 in BKLO's numbering).

  WHY AXIOMATIC: the transfer relies on the Rödl nibble, the absorbing method
  (transformers/absorbers), Hajnal–Szemerédi, and parity gadgets — none present in Mathlib
  (person-year library construction). We therefore assume the transfer as a named, cited
  external input. `#print axioms` on any downstream result will display this axiom by name,
  making the trusted surface explicit and auditable.
-/
import Ax2.Basic

namespace Ax2

open SimpleGraph

/-- **Part B (BKLO Thm 1.3 + Haxell–Rödl bridge), specialised to `K₃` (`r = 2`, so
`1 − 1/(3r) = 5/6 < 9/10`).** If min degree `≥ 9n/10` forces a *fractional* triangle
decomposition (Part A), then for every `ε > 0` all large triangle-divisible graphs with
`δ(G) ≥ (9/10 + ε)·n` have an integral triangle decomposition.

Assumed as an external axiom — see the file header for the reason and citations. -/
axiom bklo_kthree_transfer
    (hfrac : ∀ {W : Type} [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj],
        9 * Fintype.card W ≤ 10 * H.minDegree → FractionalTriangleDecomp H) :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ,
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        n₀ ≤ Fintype.card V → TriangleDivisible G →
        (9 / 10 + ε) * (Fintype.card V : ℝ) ≤ (G.minDegree : ℝ) → TriangleDecomposable G

end Ax2
