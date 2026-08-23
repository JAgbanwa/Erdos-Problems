/-
# Nibble — T3 interface

Standalone, Mathlib-only. The **interface** to the nibble theorem (T3): a single `Prop` capturing
"near-regular, low-codegree `r`-uniform hypergraphs have near-perfect matchings". The nibble
(Layers A–D + concentration + convergence) discharges this `Prop`; the Yuster assembly (→ AX1)
*consumes* it as a black box. This decouples the two: Yuster can be built against the interface
before the nibble's final wiring is complete.

Definitions come from `Nibble.Basic` (`IsUniform`, `IsMatching`) and `Nibble.Regular`
(`NearlyRegular`, `CodegreeBounded`).
-/
import Nibble.Basic
import Nibble.Regular

open Hypergraph

namespace Nibble

/-- **T3 interface — the nibble theorem.** For `r ≥ 2` and any target `β > 0`, there is a
near-regularity/codegree tolerance `μ > 0` such that every `r`-uniform hypergraph on a finite vertex
set that is `(1±μ)`-nearly `d`-regular with codegree `≤ μd` has a matching covering at least a
`(1-β)` fraction of the maximum possible (`|V|/r`). -/
def NibbleTheorem : Prop :=
  ∀ (r : ℕ), 2 ≤ r → ∀ (β : ℝ), 0 < β → ∃ μ : ℝ, 0 < μ ∧ ∃ d₀ : ℝ, 0 < d₀ ∧
    ∀ {V : Type} [Fintype V] [DecidableEq V] (H : Finset (Finset V)) (d : ℝ), 0 < d → d₀ ≤ d →
      IsUniform H r → NearlyRegular H d μ → CodegreeBounded H (μ * d) →
      ∃ M : Finset (Finset V), IsMatching H M ∧
        (1 - β) * ((Fintype.card V : ℝ) / r) ≤ (M.card : ℝ)

end Nibble
