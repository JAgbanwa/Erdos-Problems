/-
# Paper III — Layer X: the two external axioms (LEDGER, "Layer X — DO NOT PROVE")

`AX1` (Haxell–Rödl / Yuster): the fractional–integral triangle packing gap is `o(n²)`,
uniformly over graphs.  Design note (§11.6 report): the ledger's `ν₃*` ("fractional
optimum") is formalized as the LP **cover** optimum `τ₃*`; by classical finite LP
duality (packing max = cover min) this is the same number, but Mathlib has no LP
strong-duality package, and all Layer-E arguments of §3–§4 are cover-side.  Weak
duality (`nu3Star_le_tau3Star`) is proved in `Duality.lean`.

`AX2` (Dross + Barber–Kühn–Lo–Osthus): exact triangle decompositions of
triangle-divisible graphs with min degree `≥ (0.9+ε)n`.

These are the ONLY two axioms of the project.
-/
import PaperIII.Duality

namespace PaperIII

/-- A triangle decomposition: a family of triangles whose edge sets partition `E(H)`. -/
def HasTriangleDecomposition {V : Type} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] : Prop :=
  ∃ T : Finset (Finset V), (∀ t ∈ T, H.IsNClique 3 t) ∧
    ∀ e ∈ H.edgeFinset, ∃! t, t ∈ T ∧ ∀ v ∈ e, v ∈ t

/-- **AX1 (Haxell–Rödl / Yuster).**  For the fixed graph `K₃`, uniformly over graphs
`G`: `ν₃*(G) − ν₃(G) = o(|V(G)|²)` (LEDGER Layer X; `ν₃*` read as `τ₃*`, see header). -/
axiom AX1 : ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ,
  ∀ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
    (G : SimpleGraph V) (_ : DecidableRel G.Adj),
    n₀ ≤ Fintype.card V →
    tau3Star G - (nu3 G : ℝ) ≤ ε * (Fintype.card V : ℝ) ^ 2

/-- **AX2 (Dross + Barber–Kühn–Lo–Osthus).**  Every triangle-divisible graph
(`|E| ≡ 0 mod 3`, all degrees even) on `n ≥ n₀` vertices with
`δ(H) ≥ (0.9+ε)·n` has an exact triangle decomposition (LEDGER Layer X). -/
axiom AX2 : ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ,
  ∀ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
    (H : SimpleGraph V) (_ : DecidableRel H.Adj),
    H.edgeFinset.card % 3 = 0 →
    (∀ v : V, Even (H.degree v)) →
    n₀ ≤ Fintype.card V →
    ((0.9 + ε) * (Fintype.card V : ℝ) ≤ (H.minDegree : ℝ)) →
    HasTriangleDecomposition H

end PaperIII
