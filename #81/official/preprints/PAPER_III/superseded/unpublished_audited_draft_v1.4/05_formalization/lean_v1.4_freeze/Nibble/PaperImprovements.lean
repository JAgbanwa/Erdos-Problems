/-
# Paper III — low-cost strengthenings surfaced by the formalization

Byproducts of the nibble/Freedman formalization that strengthen the paper at ~zero marginal cost.
All statements are conditional on the nibble interface `NibbleTheoremMost` (the same hypothesis the
main Yuster chain uses); none add axioms.

* `#3` **`almostPerfectMatching_uniform`** — the nibble packing theorem is `r`-uniform for every
  `r ≥ 2`; the triangle (`ν₃`) result is the `r = 3` instance composed with the edge-based encoding.
  The machinery is genuinely triangle-agnostic.
* `#4` **`nu3star_sub_nu3_le_eps_strict`** — the `ν₃*−ν₃ ≤ ε|V|²` gap holds already under STRICT
  near-`d`-regularity, obtained as a special case of the weaker MAJORITY hypothesis actually used
  (`NearlyRegularMost` ⊇ `NearlyRegular`). Documents that the paper's hypothesis can be weakened to
  "near-regular outside a small exceptional set".
* `#1` **`EffectivePackingGap`** — interface for the effective (non-`o(·)`) gap the Freedman engine
  makes available: an explicit rate `r(n)` in place of the qualitative `o(n²)`. To be discharged from
  the quantitative nibble once the residual-degree Freedman concentration lands.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.YusterMost
import Nibble.RegularMost

open Finset SimpleGraph Hypergraph

namespace Nibble.YusterE

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **#3 — general `r`-uniform almost-perfect matching.** For every `r ≥ 2`, a near-`d`-regular
low-codegree `r`-uniform hypergraph (regular outside an `η`-fraction exceptional set) has a matching
covering a `(1-β)` fraction of `|V|/r`. The triangle packing `ν₃` is the `r = 3` instance under the
edge-based encoding `triangleHypergraphSub`; the nibble is not triangle-specific. -/
theorem almostPerfectMatching_uniform (hN : NibbleTheoremMost)
    (r : ℕ) (hr : 2 ≤ r) {β : ℝ} (hβ : 0 < β) :
    ∃ μ : ℝ, 0 < μ ∧ ∃ η : ℝ, 0 < η ∧ ∃ d₀ : ℝ, 0 < d₀ ∧
    ∀ {W : Type} [Fintype W] [DecidableEq W] (H : Finset (Finset W)) (d : ℝ), 0 < d → d₀ ≤ d →
      IsUniform H r → NearlyRegularMost H d μ η → CodegreeBounded H (μ * d) →
      ∃ M : Finset (Finset W), IsMatching H M ∧
        (1 - β) * ((Fintype.card W : ℝ) / r) ≤ (M.card : ℝ) :=
  hN r hr β hβ

/-- **#4 — the `ν₃*−ν₃` gap under STRICT regularity**, obtained as a special case of the majority
form. Strict `NearlyRegular` is `NearlyRegularMost` with an empty exceptional set, so the gap bound
holds a fortiori; conversely the majority hypothesis used by `nu3star_sub_nu3_le_eps_most` is strictly
weaker, which is the actual low-cost strengthening. -/
theorem nu3star_sub_nu3_le_eps_strict (hN : NibbleTheoremMost) {ε : ℝ} (hε : 0 < ε) :
    ∃ μ : ℝ, 0 < μ ∧ ∃ η : ℝ, 0 < η ∧ ∃ d₀ : ℝ, 0 < d₀ ∧ ∀ {d : ℝ}, 0 < d → d₀ ≤ d →
      NearlyRegular (triangleHypergraphSub G) d μ →
      CodegreeBounded (triangleHypergraphSub G) (μ * d) →
      nu3star G - (nu3 G : ℝ) ≤ ε * (Fintype.card V : ℝ) ^ 2 := by
  obtain ⟨μ, hμ, η, hη, d₀, hd₀, hmain⟩ := nu3star_sub_nu3_le_eps_most G hN hε
  exact ⟨μ, hμ, η, hη, d₀, hd₀, fun {d} hd hd0 hreg hcod =>
    hmain hd hd0 (hreg.nearlyRegularMost hη.le) hcod⟩

/-- **#1 — effective packing-gap interface.** The Freedman (variance-based) concentration used by the
nibble yields an EXPLICIT exponential tail, hence an effective gap `ν₃*−ν₃ ≤ rate(|V|)` with a named
`rate` in place of the qualitative `o(|V|²)`. This `def` fixes the target shape; it is discharged from
the quantitative nibble once the residual-degree Freedman bound is wired in. -/
def EffectivePackingGap (rate : ℕ → ℝ) : Prop :=
  nu3star G - (nu3 G : ℝ) ≤ rate (Fintype.card V)

end Nibble.YusterE
