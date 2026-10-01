import Mathlib

/-!
# Selecting a heavy fixed-cardinality subfamily

The lemma in this file is the exact finite averaging fact needed by the
padded RD09 phase-I construction.  Among `c` nonnegative integral weights,
one can select `p ≤ c` distinct entries whose total is at least the fraction
`p / c` of the total.  The proof chooses a maximum-weight `p`-set and uses
literal exchanges; no probability or asymptotic statement is involved.
-/

namespace PaperIV.FiniteHeavySelection

open Finset

variable {Color : Type*} [Fintype Color] [DecidableEq Color]

/-- A maximum-weight `p`-subset has at least the ambient average weight.
The cross-multiplied natural-number form avoids division and coercions. -/
theorem exists_subset_card_mul_sum_le_card_mul_sum
    (weight : Color → ℕ) (p : ℕ) (hp : p ≤ Fintype.card Color) :
    ∃ S : Finset Color,
      S.card = p ∧
      p * (∑ x : Color, weight x) ≤
        Fintype.card Color * ∑ x ∈ S, weight x := by
  classical
  let choices : Finset (Finset Color) := Finset.univ.powersetCard p
  have hchoices : choices.Nonempty := by
    change (Finset.univ.powersetCard p).Nonempty
    rw [Finset.powersetCard_nonempty]
    simpa using hp
  obtain ⟨S, hSchoice, hSmax⟩ :=
    Finset.exists_max_image choices (fun T => ∑ x ∈ T, weight x) hchoices
  have hS : S ⊆ (Finset.univ : Finset Color) ∧ S.card = p := by
    simpa [choices] using (Finset.mem_powersetCard.mp hSchoice)
  have hexchange : ∀ x ∈ S, ∀ y ∉ S, weight y ≤ weight x := by
    intro x hx y hy
    let T := insert y (S.erase x)
    have hyerase : y ∉ S.erase x := by simp [hy]
    have hp_pos : 0 < p := by
      rw [← hS.2]
      exact Finset.card_pos.mpr ⟨x, hx⟩
    have hTcard : T.card = p := by
      simp [T, hyerase, Finset.card_erase_of_mem hx, hS.2,
        Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hp_pos))]
    have hTchoice : T ∈ choices := by
      change T ∈ Finset.univ.powersetCard p
      rw [Finset.mem_powersetCard]
      exact ⟨by simp, hTcard⟩
    have hmax := hSmax T hTchoice
    have hsumS : (∑ z ∈ S, weight z) =
        weight x + ∑ z ∈ S.erase x, weight z := by
      rw [Nat.add_comm]
      exact (Finset.sum_erase_add _ weight hx).symm
    simp only [T, sum_insert hyerase] at hmax
    rw [hsumS] at hmax
    omega
  let R : Finset Color := Finset.univ \ S
  have houtside :
      p * (∑ y ∈ R, weight y) ≤ R.card * (∑ x ∈ S, weight x) := by
    calc
      p * (∑ y ∈ R, weight y) = ∑ y ∈ R, p * weight y := by
        simp [Finset.mul_sum]
      _ ≤ ∑ _y ∈ R, ∑ x ∈ S, weight x := by
        refine Finset.sum_le_sum fun y hyR => ?_
        have hy : y ∉ S := by simpa [R] using hyR
        calc
          p * weight y = ∑ _x ∈ S, weight y := by simp [hS.2]
          _ ≤ ∑ x ∈ S, weight x :=
            Finset.sum_le_sum fun x hx => hexchange x hx y hy
      _ = R.card * (∑ x ∈ S, weight x) := by simp
  have hRcard : R.card = Fintype.card Color - p := by
    simp [R, Finset.card_sdiff, hS.2]
  have htotal :
      (∑ y ∈ R, weight y) + (∑ x ∈ S, weight x) =
        ∑ x : Color, weight x := by
    simpa [R] using (Finset.sum_sdiff hS.1 (f := weight))
  refine ⟨S, hS.2, ?_⟩
  rw [← htotal]
  rw [hRcard] at houtside
  calc
    p * ((∑ y ∈ R, weight y) + ∑ x ∈ S, weight x) =
        p * (∑ y ∈ R, weight y) + p * (∑ x ∈ S, weight x) :=
      Nat.mul_add _ _ _
    _ ≤ (Fintype.card Color - p) * (∑ x ∈ S, weight x) +
        p * (∑ x ∈ S, weight x) := Nat.add_le_add_right houtside _
    _ = ((Fintype.card Color - p) + p) * (∑ x ∈ S, weight x) := by
      rw [Nat.add_mul]
    _ = Fintype.card Color * (∑ x ∈ S, weight x) := by
      rw [Nat.sub_add_cancel hp]

/-- Functional form: the selected entries are indexed injectively by
`Fin p`, exactly as required for assigning them to `p` physical roots. -/
theorem exists_injective_card_mul_sum_le_card_mul_sum
    (weight : Color → ℕ) (p : ℕ) (hp : p ≤ Fintype.card Color) :
    ∃ select : Fin p → Color,
      Function.Injective select ∧
      p * (∑ x : Color, weight x) ≤
        Fintype.card Color * ∑ i : Fin p, weight (select i) := by
  classical
  obtain ⟨S, hScard, hheavy⟩ :=
    exists_subset_card_mul_sum_le_card_mul_sum weight p hp
  have hcard : Fintype.card (Fin p) = Fintype.card S := by
    simp [hScard]
  let e : Fin p ≃ S := Fintype.equivOfCardEq hcard
  let select : Fin p → Color := fun i => (e i : Color)
  have hinj : Function.Injective select := by
    intro i j hij
    exact e.injective (Subtype.ext hij)
  refine ⟨select, hinj, ?_⟩
  have hsum : (∑ i : Fin p, weight (select i)) = ∑ x ∈ S, weight x := by
    calc
      (∑ i : Fin p, weight (select i)) = ∑ x : S, weight (x : Color) := by
        simpa [select] using (e.sum_comp (fun x : S => weight (x : Color)))
      _ = ∑ x ∈ S, weight x := Finset.sum_coe_sort S weight
  simpa [hsum] using hheavy

end PaperIV.FiniteHeavySelection
