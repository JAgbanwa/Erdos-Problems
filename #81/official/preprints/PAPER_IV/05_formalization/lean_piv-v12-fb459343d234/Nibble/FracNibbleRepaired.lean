/-
# Nibble — the repaired weighted (fractional) nibble

`Nibble.FracNibbleTheorem` is false (`Nibble.not_fracNibbleTheorem`).  The defect is that its
codegree hypothesis `codeg H x y ≤ γ·D` is measured against a quantity `D` that is only an *upper*
bound for the degrees, hence can be inflated at will; the hypothesis therefore says nothing about
hypergraphs of bounded degree, and the complete `r`-uniform hypergraph on `r+1` vertices refutes the
statement.

The repair is to measure the codegree against the fractional matching itself:

`Nibble.FracNibbleWeightedTheorem` — for every `r ≥ 2` and `β > 0` there is `γ > 0` such that every
`r`-uniform hypergraph carrying a fractional matching `w` whose **weighted codegrees**
`∑_{T ⊇ {x,z}} w T` are all at most `γ` has a matching of size at least `(1-β)∑w`.

This statement is scale free (no degree parameter occurs at all), and:

* it is **not** refuted by the family of `Nibble.FracNibbleRefutation`: there the weighted codegree
  is `(r-1)/r ≥ 1/2` (`Nibble.FracRefutation.half_le_weightedCodegree_completeK`);
* it is **proved** whenever the fractional matching is near-perfect on the region it lives on
  (`Nibble.fracNibble_weightedCodegree`, `Nibble.fracNibble_weightedCodegree_on`), which is the
  concrete, non-circular witness that the remaining obligation is a genuine strengthening of proved
  material and not vacuous.

The residual gap is therefore exactly the vertices whose `w`-load `∑_{T ∋ v} w T` is far from `1`;
see `RESIDUAL.md`.

Sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.WeightedSpreadNibble

open Finset Hypergraph

namespace Nibble

/-- **The repaired weighted (fractional) nibble.**  All hypotheses are on the fractional matching:
its vertex loads are at most `1` and its *weighted codegrees* are at most `γ`.  Nothing at all is
assumed about the degrees or codegrees of the hypergraph. -/
def FracNibbleWeightedTheorem : Prop :=
  ∀ r : ℕ, 2 ≤ r → ∀ β : ℝ, 0 < β → ∃ γ : ℝ, 0 < γ ∧
    ∀ {W : Type} [Fintype W] [DecidableEq W] (H : Finset (Finset W)) (w : Finset W → ℝ),
      IsUniform H r →
      (∀ T, 0 ≤ w T) →
      (∀ v : W, ∑ T ∈ H.filter (fun T => v ∈ T), w T ≤ 1) →
      (∀ x z : W, x ≠ z → ∑ T ∈ H.filter (fun T => x ∈ T ∧ z ∈ T), w T ≤ γ) →
      ∃ M : Finset (Finset W), IsMatching H M ∧ (1 - β) * (∑ T ∈ H, w T) ≤ (M.card : ℝ)

/-- **The repaired statement, restricted to near-perfect fractional matchings, is proved.**  This is
`Nibble.fracNibble_weightedCodegree` packaged as an instance of `Nibble.FracNibbleWeightedTheorem`
with the extra hypothesis that the `w`-load is at least `1-γ` outside a set of at most `η|W|`
vertices. -/
theorem fracNibbleWeighted_nearPerfect (r : ℕ) (hr : 2 ≤ r) (β : ℝ) (hβ : 0 < β) :
    ∃ γ : ℝ, 0 < γ ∧ ∃ η : ℝ, 0 < η ∧
      ∀ {W : Type} [Fintype W] [DecidableEq W] (H : Finset (Finset W)) (w : Finset W → ℝ)
        (Exc : Finset W),
        IsUniform H r →
        (∀ T, 0 ≤ w T) →
        (∀ v : W, ∑ T ∈ H.filter (fun T => v ∈ T), w T ≤ 1) →
        (∀ v : W, v ∉ Exc → 1 - γ ≤ ∑ T ∈ H.filter (fun T => v ∈ T), w T) →
        (Exc.card : ℝ) ≤ η * (Fintype.card W : ℝ) →
        (∀ x z : W, x ≠ z → ∑ T ∈ H.filter (fun T => x ∈ T ∧ z ∈ T), w T ≤ γ) →
        ∃ M : Finset (Finset W), IsMatching H M ∧
          (1 - β) * ((Fintype.card W : ℝ) / r) ≤ (M.card : ℝ) ∧
          (1 - β) * (∑ T ∈ H, w T) ≤ (M.card : ℝ) :=
  fracNibble_weightedCodegree r hr β hβ

end Nibble
