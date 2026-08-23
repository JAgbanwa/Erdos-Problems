/-
# Nibble — McDiarmid's bounded-differences inequality (complete)

Standalone, Mathlib-only. The capstone of the McDiarmid layer: composing M6.5 (marginalization ⇒ a.e.
Doob-increment bound), M6 (increment ⇒ conditionally sub-Gaussian), and M7 (Azuma ⇒ tail), we obtain
**McDiarmid's inequality from the pointwise bounded-difference hypothesis alone**, with no abstract
intermediate hypotheses:

  if `f` on a finite product probability space has bounded differences (`|f ω − f ω'| ≤ c j` when `ω`
  and `ω'` differ only in coordinate `j`), then
  `ℙ(ε ≤ f − E[f]) ≤ exp(−ε² / (2 ∑_j c j²))`.

McDiarmid's inequality is not in Mathlib; this is an upstreamable result. It is also the concentration
engine for the nibble's residual degree (M8), replacing the too-weak Chebyshev bound.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.McDiarmidMarginal
import Nibble.McDiarmidStep
import Nibble.McDiarmidTail
import Nibble.Prelude

open MeasureTheory ProbabilityTheory Finset
open scoped NNReal

namespace Nibble

variable {n : ℕ} {α : Fin n → Type*} [∀ i, MeasurableSpace (α i)]

/-- **McDiarmid's bounded-differences inequality.** For `f` with bounded differences (coefficient
`c j` in coordinate `j`) on the finite product probability space `Measure.pi ν`,
`ℙ(ε ≤ f − E[f]) ≤ exp(−ε² / (2 ∑_{j<n} c j²))`. -/
theorem mcdiarmid [∀ i, StandardBorelSpace (α i)] [StandardBorelSpace (∀ i, α i)]
    (ν : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (ν i)]
    (f : (∀ i, α i) → ℝ) (hf : StronglyMeasurable f) (hfi : Integrable f (Measure.pi ν))
    {c : ℕ → ℝ}
    (hbd : ∀ (j : Fin n) (ω ω' : ∀ i, α i),
      (∀ i, i ≠ j → ω i = ω' i) → |f ω - f ω'| ≤ c (j : ℕ))
    {ε : ℝ} (hε : 0 ≤ ε) :
    (Measure.pi ν).real {ω | ε ≤ f ω - ∫ x, f x ∂(Measure.pi ν)}
      ≤ Real.exp (-ε ^ 2 / (2 * ∑ i ∈ Finset.range n, (c i) ^ 2)) := by
  have h := mcdiarmid_upper (Measure.pi ν) f hf hfi
    (fun k => ⟨(c (k - 1)) ^ 2, by positivity⟩)
    (fun k hk => doob_increment_hasCondSubgaussianMGF (Measure.pi ν) f
      (fun j hj => doob_increment_ae_bound ν f hf hfi hbd j hj) k hk) hε
  simpa [NNReal.coe_sum, NNReal.coe_mk, Nat.add_sub_cancel] using h

/-- **Two-sided McDiarmid.** `ℙ(ε ≤ |f − E[f]|) ≤ 2·exp(−ε²/(2 ∑_j c j²))` — the deviation of `f`
from its mean in either direction. This is the form the residual-degree near-regularity uses. -/
theorem mcdiarmid_two_sided [∀ i, StandardBorelSpace (α i)] [StandardBorelSpace (∀ i, α i)]
    (ν : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (ν i)]
    (f : (∀ i, α i) → ℝ) (hf : StronglyMeasurable f) (hfi : Integrable f (Measure.pi ν))
    {c : ℕ → ℝ}
    (hbd : ∀ (j : Fin n) (ω ω' : ∀ i, α i),
      (∀ i, i ≠ j → ω i = ω' i) → |f ω - f ω'| ≤ c (j : ℕ))
    {ε : ℝ} (hε : 0 ≤ ε) :
    (Measure.pi ν).real {ω | ε ≤ |f ω - ∫ x, f x ∂(Measure.pi ν)|}
      ≤ 2 * Real.exp (-ε ^ 2 / (2 * ∑ i ∈ Finset.range n, (c i) ^ 2)) := by
  have hup := mcdiarmid ν f hf hfi hbd hε
  have hlo := mcdiarmid ν (fun x => -f x) hf.neg hfi.neg
    (fun j ω ω' h => by
      rw [show -f ω - -f ω' = -(f ω - f ω') from by ring, abs_neg]; exact hbd j ω ω' h) hε
  have hsub : {ω | ε ≤ |f ω - ∫ x, f x ∂(Measure.pi ν)|}
      ⊆ {ω | ε ≤ f ω - ∫ x, f x ∂(Measure.pi ν)}
        ∪ {ω | ε ≤ (fun x => -f x) ω - ∫ x, (fun x => -f x) x ∂(Measure.pi ν)} := by
    intro ω hω
    rw [Set.mem_setOf_eq, le_abs] at hω
    rcases hω with h | h
    · exact Or.inl h
    · refine Or.inr ?_
      rw [Set.mem_setOf_eq, integral_neg]
      simp only
      linarith only [h]
  calc (Measure.pi ν).real {ω | ε ≤ |f ω - ∫ x, f x ∂(Measure.pi ν)|}
      ≤ (Measure.pi ν).real ({ω | ε ≤ f ω - ∫ x, f x ∂(Measure.pi ν)}
          ∪ {ω | ε ≤ (fun x => -f x) ω - ∫ x, (fun x => -f x) x ∂(Measure.pi ν)}) :=
        measureReal_mono hsub
    _ ≤ (Measure.pi ν).real {ω | ε ≤ f ω - ∫ x, f x ∂(Measure.pi ν)}
        + (Measure.pi ν).real {ω | ε ≤ (fun x => -f x) ω
            - ∫ x, (fun x => -f x) x ∂(Measure.pi ν)} := measureReal_union_le _ _
    _ ≤ Real.exp (-ε ^ 2 / (2 * ∑ i ∈ Finset.range n, (c i) ^ 2))
        + Real.exp (-ε ^ 2 / (2 * ∑ i ∈ Finset.range n, (c i) ^ 2)) := add_le_add hup hlo
    _ = 2 * Real.exp (-ε ^ 2 / (2 * ∑ i ∈ Finset.range n, (c i) ^ 2)) := by ring

/-- **Two-sided McDiarmid over an arbitrary finite index** (constant coordinate type). Reindexes the
`Fintype` index `δ` to `Fin (card δ)` via `piCongrLeft` (measure-preserving) and applies
`mcdiarmid_two_sided`. This is the form the nibble uses: index = edges, coordinate type `γ = Bool`. -/
theorem mcdiarmid_two_sided_const {δ : Type*} [Fintype δ] [DecidableEq δ]
    {γ : Type*} [MeasurableSpace γ] [StandardBorelSpace γ]
    (ν : Measure γ) [IsProbabilityMeasure ν]
    (f : (δ → γ) → ℝ) (hf : StronglyMeasurable f)
    (hfi : Integrable f (Measure.pi (fun _ : δ => ν)))
    {c : δ → ℝ}
    (hbd : ∀ (j : δ) (ω ω' : δ → γ), (∀ i, i ≠ j → ω i = ω' i) → |f ω - f ω'| ≤ c j)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (Measure.pi (fun _ : δ => ν)).real
        {ω | ε ≤ |f ω - ∫ x, f x ∂(Measure.pi (fun _ : δ => ν))|}
      ≤ 2 * Real.exp (-ε ^ 2 / (2 * ∑ j : δ, (c j) ^ 2)) := by
  classical
  set e : Fin (Fintype.card δ) ≃ δ := (Fintype.equivFin δ).symm with he
  set φ : (Fin (Fintype.card δ) → γ) ≃ᵐ (δ → γ) :=
    MeasurableEquiv.piCongrLeft (fun _ => γ) e with hφ
  have hmp : MeasurePreserving φ (Measure.pi (fun _ : Fin (Fintype.card δ) => ν))
      (Measure.pi (fun _ : δ => ν)) := measurePreserving_piCongrLeft (fun _ : δ => ν) e
  have hgmeas : StronglyMeasurable (f ∘ φ) := hf.comp_measurable φ.measurable
  have hgint : Integrable (f ∘ φ) (Measure.pi (fun _ : Fin (Fintype.card δ) => ν)) :=
    hmp.integrable_comp_of_integrable hfi
  set c' : ℕ → ℝ := fun m => if h : m < Fintype.card δ then c (e ⟨m, h⟩) else 0 with hc'
  have hcc : ∀ i : Fin (Fintype.card δ), c' (i : ℕ) = c (e i) := by
    intro i; simp only [hc']; rw [dif_pos i.isLt, Fin.eta]
  have hgbd : ∀ (i : Fin (Fintype.card δ)) (a a' : Fin (Fintype.card δ) → γ),
      (∀ k, k ≠ i → a k = a' k) → |(f ∘ φ) a - (f ∘ φ) a'| ≤ c' (i : ℕ) := by
    intro i a a' hk
    rw [hcc i]
    refine hbd (e i) (φ a) (φ a') (fun j hj => ?_)
    have hji : e.symm j ≠ i := fun h => hj (by rw [← h, e.apply_symm_apply])
    show (φ a) j = (φ a') j
    simp only [hφ, MeasurableEquiv.piCongrLeft, MeasurableEquiv.coe_mk,
      Equiv.piCongrLeft_apply, hk (e.symm j) hji]
  have hmcd := mcdiarmid_two_sided (fun _ : Fin (Fintype.card δ) => ν) (f ∘ φ) hgmeas hgint hgbd hε
  have hsumeq : ∑ i ∈ Finset.range (Fintype.card δ), (c' i) ^ 2 = ∑ j : δ, (c j) ^ 2 := by
    rw [← Fin.sum_univ_eq_sum_range (fun m => (c' m) ^ 2), ← Equiv.sum_comp e (fun j => (c j) ^ 2)]
    exact Finset.sum_congr rfl (fun i _ => by rw [hcc i])
  have hint : ∫ x, (f ∘ φ) x ∂(Measure.pi (fun _ : Fin (Fintype.card δ) => ν))
      = ∫ x, f x ∂(Measure.pi (fun _ : δ => ν)) := hmp.integral_comp φ.measurableEmbedding f
  have hSmeas : MeasurableSet {ω : δ → γ | ε ≤ |f ω - ∫ x, f x ∂(Measure.pi (fun _ : δ => ν))|} :=
    measurableSet_le measurable_const ((hf.measurable.sub measurable_const).abs)
  have hev : {a : Fin (Fintype.card δ) → γ | ε ≤
        |(f ∘ φ) a - ∫ x, (f ∘ φ) x ∂(Measure.pi (fun _ : Fin (Fintype.card δ) => ν))|}
      = φ ⁻¹' {ω : δ → γ | ε ≤ |f ω - ∫ x, f x ∂(Measure.pi (fun _ : δ => ν))|} := by
    rw [hint]; ext a; simp only [Set.mem_setOf_eq, Set.mem_preimage, Function.comp_apply]
  calc (Measure.pi (fun _ : δ => ν)).real
        {ω | ε ≤ |f ω - ∫ x, f x ∂(Measure.pi (fun _ : δ => ν))|}
      = (Measure.pi (fun _ : Fin (Fintype.card δ) => ν)).real
          (φ ⁻¹' {ω | ε ≤ |f ω - ∫ x, f x ∂(Measure.pi (fun _ : δ => ν))|}) := by
        rw [measureReal_def, measureReal_def, hmp.measure_preimage hSmeas.nullMeasurableSet]
    _ = (Measure.pi (fun _ : Fin (Fintype.card δ) => ν)).real
          {a | ε ≤ |(f ∘ φ) a - ∫ x, (f ∘ φ) x ∂(Measure.pi (fun _ : Fin (Fintype.card δ) => ν))|} := by
        rw [hev]
    _ ≤ 2 * Real.exp (-ε ^ 2 / (2 * ∑ i ∈ Finset.range (Fintype.card δ), (c' i) ^ 2)) := hmcd
    _ = 2 * Real.exp (-ε ^ 2 / (2 * ∑ j : δ, (c j) ^ 2)) := by rw [hsumeq]

end Nibble
