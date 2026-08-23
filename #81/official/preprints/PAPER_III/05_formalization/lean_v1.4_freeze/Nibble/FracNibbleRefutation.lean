/-
# Nibble — the weighted (fractional) nibble as stated in `Nibble.WeightedNibble` is FALSE

`Nibble.FracNibbleTheorem` asks, for every uniformity `r ≥ 2` and every tolerance `β > 0`, for
constants `γ > 0`, `D₀ > 0` such that **every** `r`-uniform hypergraph `H` with

* a *degree ceiling* `deg_H(v) ≤ D` for some `D ≥ D₀`,
* codegrees `≤ γ·D`,
* a fractional matching `w`,

has an integer matching of size `≥ (1-β)∑w`.

The bug is that `D` is only an **upper** bound for the degrees, so the codegree hypothesis
`codeg ≤ γD` can always be satisfied by *inflating* `D`: it puts no constraint at all on a
hypergraph whose degrees are bounded by an absolute constant.  Consequently the statement is
refuted by the smallest possible obstruction, the complete `r`-uniform hypergraph on `r+1`
vertices:

> `Nibble.FracRefutation.completeK` — all `r`-subsets of `Fin (r+1)`.  It is `r`-uniform, every
> vertex has degree `r`, every two edges meet (so `ν = 1`), and the uniform weighting `1/r` is a
> *perfect* fractional matching of total weight `(r+1)/r > 1`.

Taking `D := max D₀ (r/γ)` satisfies every hypothesis, so the conclusion would give
`(1-β)(r+1)/r ≤ 1`, i.e. `β ≥ 1/(r+1)`.

Results of this file.

* `Nibble.FracNibbleAt` — the `(r, β)`-slice of `Nibble.FracNibbleTheorem`, with
  `Nibble.fracNibbleTheorem_iff` certifying that it is literally the body of the statement.
* `Nibble.not_fracNibbleAt` — **for every `r ≥ 2` the slice fails** for every `β < 1/(r+1)`.
* `Nibble.not_fracNibbleTheorem` — hence `¬ Nibble.FracNibbleTheorem`.
* `Nibble.not_fracNibbleAt_three` — the refutation of the `r = 3` slice, which is the one the AX1
  chain `Nibble.AX1.haxellRodlGap_of_fracNibble` consumes.

Nothing in `Nibble.WeightedNibble` becomes false: the implications proved there
(`Nibble.AX1.haxellRodlGap_of_fracNibble`, `Nibble.AX1.coreGapResidual_of_fracNibble`) remain valid
implications — they are simply implications from a false hypothesis, so they cannot be used to
close AX1.  See `RESIDUAL.md` and `Nibble.FracNibbleLocal` for the repaired obligation.

Sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.WeightedNibble

open Finset Hypergraph

namespace Nibble

/-! ### The `(r, β)`-slice of the weighted nibble -/

/-- The `(r, β)`-slice of `Nibble.FracNibbleTheorem`: the statement obtained by fixing the
uniformity `r` and the tolerance `β`. -/
def FracNibbleAt (r : ℕ) (β : ℝ) : Prop :=
  ∃ γ : ℝ, 0 < γ ∧ ∃ D₀ : ℝ, 0 < D₀ ∧
    ∀ {W : Type} [Fintype W] [DecidableEq W] (H : Finset (Finset W)) (w : Finset W → ℝ) (D : ℝ),
      D₀ ≤ D → IsUniform H r →
      (∀ T, 0 ≤ w T) → (∀ T ∉ H, w T = 0) →
      (∀ v : W, ∑ T ∈ H.filter (fun T => v ∈ T), w T ≤ 1) →
      (∀ v : W, (Hypergraph.degree H v : ℝ) ≤ D) →
      (∀ x y : W, x ≠ y → (Hypergraph.codegree H x y : ℝ) ≤ γ * D) →
      ∃ M : Finset (Finset W), IsMatching H M ∧ (1 - β) * (∑ T ∈ H, w T) ≤ (M.card : ℝ)

/-- `Nibble.FracNibbleTheorem` is exactly the conjunction of all its slices. -/
theorem fracNibbleTheorem_iff :
    FracNibbleTheorem ↔ ∀ r : ℕ, 2 ≤ r → ∀ β : ℝ, 0 < β → FracNibbleAt r β := Iff.rfl

namespace FracRefutation

/-! ### The complete `r`-uniform hypergraph on `r+1` vertices -/

/-- **The extremal obstruction**: all `r`-subsets of an `(r+1)`-set, presented as the complements
of the singletons. -/
def completeK (r : ℕ) : Finset (Finset (Fin (r + 1))) :=
  Finset.image (fun x : Fin (r + 1) => Finset.univ.erase x) Finset.univ

theorem erase_injective (r : ℕ) :
    Function.Injective (fun x : Fin (r + 1) => (Finset.univ.erase x)) := by
  intro a b hab
  have hab' : (Finset.univ.erase a : Finset (Fin (r + 1))) = Finset.univ.erase b := hab
  by_contra hne
  have h1 : b ∈ (Finset.univ.erase a : Finset (Fin (r + 1))) :=
    Finset.mem_erase.mpr ⟨fun h => hne h.symm, Finset.mem_univ b⟩
  rw [hab'] at h1
  simp at h1

/-- The obstruction has exactly `r+1` edges. -/
theorem card_completeK (r : ℕ) : (completeK r).card = r + 1 := by
  rw [completeK, Finset.card_image_of_injective _ (erase_injective r), Finset.card_univ,
    Fintype.card_fin]

/-- The obstruction is `r`-uniform. -/
theorem isUniform_completeK (r : ℕ) : IsUniform (completeK r) r := by
  intro e he
  rw [completeK] at he
  simp only [Finset.mem_image, Finset.mem_univ, true_and] at he
  obtain ⟨x, rfl⟩ := he
  rw [Finset.card_erase_of_mem (Finset.mem_univ x), Finset.card_univ, Fintype.card_fin]
  omega

/-- Every vertex of the obstruction has degree at most `r` (in fact exactly `r`). -/
theorem degree_completeK_le (r : ℕ) (v : Fin (r + 1)) : Hypergraph.degree (completeK r) v ≤ r := by
  have hss : (completeK r).filter (fun T => v ∈ T) ⊂ completeK r := by
    refine (Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)).mpr ?_
    refine ⟨Finset.univ.erase v, Finset.mem_image.mpr ⟨v, Finset.mem_univ v, rfl⟩, ?_⟩
    simp
  have h := Finset.card_lt_card hss
  rw [card_completeK] at h
  have : Hypergraph.degree (completeK r) v = ((completeK r).filter (fun T => v ∈ T)).card := rfl
  omega

/-- Every codegree of the obstruction is at most `r`. -/
theorem codegree_completeK_le (r : ℕ) (x y : Fin (r + 1)) :
    Hypergraph.codegree (completeK r) x y ≤ r := by
  have hsub : (completeK r).filter (fun T => x ∈ T ∧ y ∈ T)
      ⊆ (completeK r).filter (fun T => x ∈ T) := by
    intro T hT
    rw [Finset.mem_filter] at hT ⊢
    exact ⟨hT.1, hT.2.1⟩
  have h := Finset.card_le_card hsub
  exact le_trans h (degree_completeK_le r x)

/-- **Any two edges of the obstruction meet.** -/
theorem not_disjoint_completeK (r : ℕ) (hr : 2 ≤ r) {e f : Finset (Fin (r + 1))}
    (he : e ∈ completeK r) (hf : f ∈ completeK r) (hef : e ≠ f) : ¬ Disjoint e f := by
  simp only [completeK, Finset.mem_image, Finset.mem_univ, true_and] at he hf
  obtain ⟨a, rfl⟩ := he
  obtain ⟨b, rfl⟩ := hf
  have hcard : ({a, b} : Finset (Fin (r + 1))).card < (Finset.univ : Finset (Fin (r+1))).card := by
    have h1 := Finset.card_insert_le a ({b} : Finset (Fin (r + 1)))
    have h1' : ({a, b} : Finset (Fin (r + 1))).card ≤ 2 := by simpa using h1
    have h2 : (Finset.univ : Finset (Fin (r + 1))).card = r + 1 := by simp
    omega
  obtain ⟨z, -, hz⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  intro hdisj
  have hz1 : z ∈ Finset.univ.erase a :=
    Finset.mem_erase.mpr ⟨fun h => hz (by simp [h]), Finset.mem_univ z⟩
  have hz2 : z ∈ Finset.univ.erase b :=
    Finset.mem_erase.mpr ⟨fun h => hz (by simp [h]), Finset.mem_univ z⟩
  exact (Finset.disjoint_left.mp hdisj hz1) hz2

/-- **The matching number of the obstruction is at most `1`.** -/
theorem card_le_one_of_isMatching (r : ℕ) (hr : 2 ≤ r) {M : Finset (Finset (Fin (r + 1)))}
    (hM : IsMatching (completeK r) M) : M.card ≤ 1 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨e, he, f, hf, hef⟩ := Finset.one_lt_card.mp hcon
  exact not_disjoint_completeK r hr (hM.subset he) (hM.subset hf) hef (hM.disjoint e he f hf hef)

/-- The uniform weighting `1/r` of the obstruction. -/
noncomputable def unifWeight (r : ℕ) : Finset (Fin (r + 1)) → ℝ :=
  fun T => if T ∈ completeK r then 1 / (r : ℝ) else 0

theorem unifWeight_nonneg (r : ℕ) (T : Finset (Fin (r + 1))) : 0 ≤ unifWeight r T := by
  unfold unifWeight
  split
  · positivity
  · exact le_rfl

theorem unifWeight_zero (r : ℕ) {T : Finset (Fin (r + 1))} (hT : T ∉ completeK r) :
    unifWeight r T = 0 := by
  unfold unifWeight; simp [hT]

/-- The uniform weighting is a fractional matching: every vertex carries total weight
`degree/r ≤ 1`. -/
theorem unifWeight_vertex_le (r : ℕ) (hr : 2 ≤ r) (v : Fin (r + 1)) :
    ∑ T ∈ (completeK r).filter (fun T => v ∈ T), unifWeight r T ≤ 1 := by
  have hrpos : (0 : ℝ) < r := by
    have : 0 < r := lt_of_lt_of_le (by norm_num) hr
    exact_mod_cast this
  have hval : ∀ T ∈ (completeK r).filter (fun T => v ∈ T), unifWeight r T = 1 / (r : ℝ) := by
    intro T hT
    have := (Finset.mem_filter.mp hT).1
    unfold unifWeight; simp [this]
  rw [Finset.sum_congr rfl hval, Finset.sum_const, nsmul_eq_mul]
  have hdeg : (((completeK r).filter (fun T => v ∈ T)).card : ℝ) ≤ (r : ℝ) := by
    have := degree_completeK_le r v
    have h' : ((completeK r).filter (fun T => v ∈ T)).card ≤ r := this
    exact_mod_cast h'
  rw [mul_one_div, div_le_one hrpos]
  exact hdeg

/-- The total weight of the uniform weighting is `(r+1)/r`. -/
theorem unifWeight_total (r : ℕ) :
    ∑ T ∈ completeK r, unifWeight r T = ((r : ℝ) + 1) / (r : ℝ) := by
  have hval : ∀ T ∈ completeK r, unifWeight r T = 1 / (r : ℝ) := by
    intro T hT; unfold unifWeight; simp [hT]
  rw [Finset.sum_congr rfl hval, Finset.sum_const, nsmul_eq_mul, card_completeK]
  push_cast
  ring

end FracRefutation

/-! ### The refutation -/

/-- **For every uniformity `r ≥ 2`, the `r`-slice of the weighted nibble fails for every tolerance
`β < 1/(r+1)`.**  The witness is the complete `r`-uniform hypergraph on `r+1` vertices, whose
degrees are `r` — an absolute constant — while `D` may be inflated at will, so that the codegree
hypothesis `codeg ≤ γD` is satisfied vacuously. -/
theorem not_fracNibbleAt (r : ℕ) (hr : 2 ≤ r) (β : ℝ) (hβ : β < 1 / ((r : ℝ) + 1)) :
    ¬ FracNibbleAt r β := by
  rintro ⟨γ, hγ, D₀, hD₀, hmain⟩
  have hrpos : (0 : ℝ) < r := by
    have : 0 < r := lt_of_lt_of_le (by norm_num) hr
    exact_mod_cast this
  set D : ℝ := max D₀ (max ((r : ℝ) / γ) (r : ℝ)) with hDdef
  have hD₀D : D₀ ≤ D := le_max_left _ _
  have hrD : (r : ℝ) / γ ≤ D := le_trans (le_max_left _ _) (le_max_right _ _)
  have hrD' : (r : ℝ) ≤ D := le_trans (le_max_right _ _) (le_max_right _ _)
  have hcodD : (r : ℝ) ≤ γ * D := by
    rw [div_le_iff₀ hγ] at hrD
    linarith
  have hdegD : ∀ v : Fin (r + 1), (Hypergraph.degree (FracRefutation.completeK r) v : ℝ) ≤ D := by
    intro v
    have h1 : (Hypergraph.degree (FracRefutation.completeK r) v : ℝ) ≤ (r : ℝ) := by
      exact_mod_cast FracRefutation.degree_completeK_le r v
    linarith
  obtain ⟨M, hM, hMcard⟩ := hmain (FracRefutation.completeK r) (FracRefutation.unifWeight r) D
    hD₀D (FracRefutation.isUniform_completeK r) (FracRefutation.unifWeight_nonneg r)
    (fun T hT => FracRefutation.unifWeight_zero r hT)
    (FracRefutation.unifWeight_vertex_le r hr)
    hdegD
    (fun x y _ => by
      have h1 : (Hypergraph.codegree (FracRefutation.completeK r) x y : ℝ) ≤ (r : ℝ) := by
        exact_mod_cast FracRefutation.codegree_completeK_le r x y
      linarith)
  rw [FracRefutation.unifWeight_total r] at hMcard
  have hM1 : (M.card : ℝ) ≤ 1 := by
    exact_mod_cast FracRefutation.card_le_one_of_isMatching r hr hM
  -- `(1-β)(r+1)/r > 1` because `β < 1/(r+1)`
  have hkey : 1 < (1 - β) * (((r : ℝ) + 1) / (r : ℝ)) := by
    have hr1 : (0 : ℝ) < (r : ℝ) + 1 := by linarith
    rw [lt_div_iff₀ hr1] at hβ
    have hrw : (1 - β) * (((r : ℝ) + 1) / (r : ℝ)) = ((1 - β) * ((r : ℝ) + 1)) / (r : ℝ) := by
      ring
    rw [hrw, lt_div_iff₀ hrpos]
    nlinarith
  linarith

/-- **The weighted nibble `Nibble.FracNibbleTheorem`, as stated, is false.** -/
theorem not_fracNibbleTheorem : ¬ FracNibbleTheorem := by
  intro h
  exact not_fracNibbleAt 2 le_rfl (1 / 4) (by norm_num) (h 2 le_rfl (1 / 4) (by norm_num))

/-- **The `r = 3` slice — the one the AX1 chain consumes — is false as well**: the four triangles
of `K₄`, weighted `1/3` each, form a perfect fractional matching of weight `4/3` in a `3`-uniform
hypergraph of maximum matching `1`. -/
theorem not_fracNibbleAt_three : ¬ FracNibbleAt 3 (1 / 8) :=
  not_fracNibbleAt 3 (by norm_num) (1 / 8) (by norm_num)

end Nibble
