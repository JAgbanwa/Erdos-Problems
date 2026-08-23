/-
# Paper III — Layer X: legacy compatibility interface

`AX1` (Haxell–Rödl / Yuster): the fractional–integral triangle packing gap is `o(n²)`,
uniformly over graphs.  Design note (§11.6 report): the ledger's `ν₃*` ("fractional
optimum") is formalized as the LP **cover** optimum `τ₃*`; by classical finite LP
duality (packing max = cover min) this is the same number, but Mathlib has no LP
strong-duality package, and all Layer-E arguments of §3–§4 are cover-side.  Weak
duality (`nu3Star_le_tau3Star`) is proved in `Duality.lean`.

`AX2` (Dross + Barber–Kühn–Lo–Osthus): exact triangle decompositions of
triangle-divisible graphs with min degree `≥ (0.9+ε)n`.

The clean root no longer declares these as Lean axioms.  The remaining mathematical inputs are
represented by `AX1Assumption` and `AX2Assumption` in `PaperIII.AXDefs` and are passed explicitly
through the final assembly surfaces.
-/
import PaperIII.AXDefs

namespace PaperIII

/-- **AX1 (Haxell–Rödl / Yuster).**  For the fixed graph `K₃`, uniformly over graphs
`G`: `ν₃*(G) − ν₃(G) = o(|V(G)|²)` (LEDGER Layer X; `ν₃*` read as `τ₃*`, see header).

Legacy wrapper only: callers must supply the assumption explicitly. -/
theorem AX1 (hAX1 : AX1Assumption) : AX1Assumption :=
  hAX1

/-- **AX2 (Dross + Barber–Kühn–Lo–Osthus).**  Every triangle-divisible graph
(`|E| ≡ 0 mod 3`, all degrees even) on `n ≥ n₀` vertices with
`δ(H) ≥ (0.9+ε)·n` has an exact triangle decomposition (LEDGER Layer X).

Legacy wrapper only: callers must supply the assumption explicitly. -/
theorem AX2 (hAX2 : AX2Assumption) : AX2Assumption :=
  hAX2

end PaperIII
