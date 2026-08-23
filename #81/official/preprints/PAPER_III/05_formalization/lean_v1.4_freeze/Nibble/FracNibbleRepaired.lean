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
import Nibble.FracNibbleRefutation
import Nibble.WeightedNibbleRestrict

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

namespace FracRefutation

/-- The pairs of the obstruction lie in exactly the edges avoiding both, so its **weighted
codegree** is `(r-1)/r`; in particular at least `1/2`.  The refuting family of
`Nibble.not_fracNibbleAt` therefore does **not** refute `Nibble.FracNibbleWeightedTheorem`. -/
theorem half_le_weightedCodegree_completeK (r : ℕ) (hr : 2 ≤ r) (x z : Fin (r + 1)) (hxz : x ≠ z) :
    (1 : ℝ) / 2 ≤ ∑ T ∈ (completeK r).filter (fun T => x ∈ T ∧ z ∈ T), unifWeight r T := by
  classical
  have hrpos : (0 : ℝ) < r := by
    have : 0 < r := lt_of_lt_of_le (by norm_num) hr
    exact_mod_cast this
  -- the `r-1` edges omitting a vertex different from `x` and `z`
  set A : Finset (Fin (r + 1)) := (Finset.univ.erase x).erase z with hA
  have hAcard : A.card = r - 1 := by
    have hz : z ∈ Finset.univ.erase x := Finset.mem_erase.mpr ⟨fun h => hxz h.symm, mem_univ z⟩
    rw [hA, Finset.card_erase_of_mem hz, Finset.card_erase_of_mem (mem_univ x), Finset.card_univ,
      Fintype.card_fin]
    omega
  have hsub : A.image (fun a => Finset.univ.erase a)
      ⊆ (completeK r).filter (fun T => x ∈ T ∧ z ∈ T) := by
    intro T hT
    rw [Finset.mem_image] at hT
    obtain ⟨a, haA, rfl⟩ := hT
    rw [hA, Finset.mem_erase, Finset.mem_erase] at haA
    refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨a, mem_univ a, rfl⟩, ?_, ?_⟩
    · exact Finset.mem_erase.mpr ⟨fun h => haA.2.1 h.symm, mem_univ x⟩
    · exact Finset.mem_erase.mpr ⟨fun h => haA.1 h.symm, mem_univ z⟩
  have hcardim : (A.image (fun a => Finset.univ.erase a)).card = r - 1 := by
    rw [Finset.card_image_of_injective _ (erase_injective r), hAcard]
  have hsum : ∑ T ∈ A.image (fun a => Finset.univ.erase a), unifWeight r T
      = ((r : ℝ) - 1) * (1 / (r : ℝ)) := by
    have hval : ∀ T ∈ A.image (fun a => Finset.univ.erase a), unifWeight r T = 1 / (r : ℝ) := by
      intro T hT
      have hTmem : T ∈ completeK r := (Finset.mem_filter.mp (hsub hT)).1
      unfold unifWeight; simp [hTmem]
    rw [Finset.sum_congr rfl hval, Finset.sum_const, nsmul_eq_mul, hcardim]
    have hcast : ((r - 1 : ℕ) : ℝ) = (r : ℝ) - 1 := by
      have : 1 ≤ r := le_trans (by norm_num) hr
      push_cast [Nat.cast_sub this]
      ring
    rw [hcast]
  have hle : ∑ T ∈ A.image (fun a => Finset.univ.erase a), unifWeight r T
      ≤ ∑ T ∈ (completeK r).filter (fun T => x ∈ T ∧ z ∈ T), unifWeight r T :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun T _ _ => unifWeight_nonneg r T)
  refine le_trans ?_ hle
  rw [hsum]
  have hr2 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hrw : ((r : ℝ) - 1) * (1 / (r : ℝ)) = ((r : ℝ) - 1) / (r : ℝ) := by ring
  rw [hrw, le_div_iff₀ hrpos]
  linarith

end FracRefutation

end Nibble
