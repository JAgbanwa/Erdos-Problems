/-
# Nibble — McDiarmid M6.5 : marginalization (pointwise bounded diff ⇒ a.e. increment bound)

Standalone, Mathlib-only. The load-bearing bridge of McDiarmid, isolated as the obligation of M6's
`hbd` hypothesis. On a PRODUCT measure `Measure.pi ν` (independent coordinates), the Doob increment
of the exposure filtration is bounded a.e. by the pointwise bounded-difference coefficient.
-/
import Nibble.McDiarmid
import Nibble.Prelude

open MeasureTheory ProbabilityTheory Finset

namespace Nibble

variable {n : ℕ} {α : Fin n → Type*} [∀ i, MeasurableSpace (α i)]

/-- Replace all coordinates at or after `k` by those of `y`. -/
def tailSplice (k : ℕ) (ω y : ∀ i, α i) : ∀ i, α i :=
  fun i => if (i : ℕ) < k then ω i else y i

/-- Integrate a function over the coordinates at or after `k`, leaving the prefix fixed. -/
noncomputable def tailMarginal (ν : ∀ i, Measure (α i))
    (f : (∀ i, α i) → ℝ) (k : ℕ) (ω : ∀ i, α i) : ℝ :=
  ∫ y, f (tailSplice k ω y) ∂(Measure.pi ν)

private lemma exposureσ_eq_comap_prefix (k : ℕ) :
    exposureσ (α := α) k =
      MeasurableSpace.comap (fun ω => fun i : {i : Fin n // (i : ℕ) < k} => ω i) inferInstance := by
  simp [exposureσ]
  apply le_antisymm
  · apply iSup_le
    intro i
    simp (config := { decide := true })
    intro h
    set g : (∀ j, α j) → (∀ j : {j : Fin n // (j : ℕ) < k}, α ↑j) := fun ω j => ω ↑j with hg
    set eval_i : (∀ j : {j : Fin n // (j : ℕ) < k}, α ↑j) → α i := fun x => x ⟨i, h⟩ with heval
    have hcomp : (fun ω : ∀ j, α j => ω i) = eval_i ∘ g := rfl
    rw [hcomp]
    have heq : MeasurableSpace.comap (eval_i ∘ g) inferInstance = 
           MeasurableSpace.comap g (MeasurableSpace.comap eval_i inferInstance) := by
      ext s
      simp
    rw [heq]
    apply MeasurableSpace.comap_mono
    rw [MeasurableSpace.comap_le_iff_le_map]
    rw [← MeasurableSpace.comap_le_iff_le_map]
    have hj : (⟨i, h⟩ : {j : Fin n // (j : ℕ) < k}) = ⟨i, h⟩ := rfl
    exact (measurable_iff_comap_le).mp (measurable_pi_apply (⟨i, h⟩ : {j : Fin n // (j : ℕ) < k}))
  · rw [MeasurableSpace.comap_eq_generateFrom]
    apply MeasurableSpace.generateFrom_le
    intro t ht
    obtain ⟨s, hs, rfl⟩ := ht
    set F : (∀ j, α j) → (∀ j : {j : Fin n // (j : ℕ) < k}, α ↑j) := fun ω j => ω ↑j with hF
    -- s is measurable in the Pi-type on the subtype
    -- We need to show F⁻¹(s) is measurable in sup
    -- Use induction on measurable sets
    let sup := ⨆ (i : Fin n), ⨆ (_ : (i : ℕ) < k), MeasurableSpace.comap (fun (ω : ∀ j, α j) => ω i) inferInstance
    have measurable_F : Measurable F := by
      rw [measurable_pi_iff]
      intro a
      rw [measurable_iff_comap_le]
      exact le_iSup_of_le a.val (le_iSup_of_le (a.property) le_rfl)
    have help : ∀ t : Set (∀ j : {j : Fin n // (j : ℕ) < k}, α ↑j),
        @MeasurableSet _ MeasurableSpace.pi t →
        @MeasurableSet _ sup (F ⁻¹' t) := by
      intro t ht
      exact measurable_F ht
    exact help s hs

private lemma tailMarginal_stronglyMeasurable
    (ν : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (ν i)]
    {f : (∀ i, α i) → ℝ} (hf : StronglyMeasurable f) (k : ℕ) :
    StronglyMeasurable[exposureσ k] (tailMarginal ν f k) := by
  -- exposureσ k = comap π where π extracts coordinates < k
  have exposureσ_eq_comap_prefix : exposureσ (α := α) k =
      MeasurableSpace.comap (fun ω : (∀ i, α i) => (fun i : {i : Fin n // (i : ℕ) < k} => ω i)) inferInstance := by
    unfold exposureσ
    refine le_antisymm ?_ ?_
    · refine iSup₂_le fun i hi => ?_
      rw [← measurable_iff_comap_le]
      have : (fun ω : (∀ i, α i) => ω i) = (fun ω' : (∀ j : {j : Fin n // (j : ℕ) < k}, α j) => ω' ⟨i, hi⟩) ∘
          (fun ω : (∀ i, α i) => fun j : {j : Fin n // (j : ℕ) < k} => ω ↑j) := rfl
      rw [this]
      have h_meas_pi : @Measurable (∀ i, α i) (∀ j : {j : Fin n // (j : ℕ) < k}, α j)
          (MeasurableSpace.comap (fun ω : (∀ i, α i) => fun j : {j : Fin n // (j : ℕ) < k} => ω ↑j) inferInstance)
          (MeasurableSpace.pi) (fun ω j => ω ↑j) :=
        Measurable.of_comap_le le_rfl
      exact (measurable_pi_apply (a := (⟨i, hi⟩ : {i : Fin n // (i : ℕ) < k}))).comp h_meas_pi
    · rw [MeasurableSpace.comap_le_iff_le_map]
      -- Goal: MeasurableSpace.pi ≤ map π (⨆ i, ⨆ (_ : i < k), comap (fun ω => ω i))
      -- MeasurableSpace.pi = ⨆ j, comap (fun b => b j)
      have h_pi : MeasurableSpace.pi = ⨆ (j : {j : Fin n // (j : ℕ) < k}),
          MeasurableSpace.comap (fun b : (∀ j : {j : Fin n // (j : ℕ) < k}, α j) => b j) inferInstance := rfl
      rw [h_pi]
      exact iSup_le fun j => by
        rw [← MeasurableSpace.comap_le_iff_le_map]
        -- Goal: comap π (comap proj_j) ≤ ⨆ i, ⨆ (_ : i < k), comap (fun ω => ω i)
        -- Note: comap π (comap proj_j) = comap (proj_j ∘ π) = comap (fun ω => ω j)
        rw [MeasurableSpace.comap_comp]
        -- Goal: comap (proj_j ∘ π) ≤ ⨆ i, ⨆ (_ : i < k), comap (fun ω => ω i)
        -- Note: proj_j ∘ π = fun ω => ω j
        have h_eq : (fun b : (∀ j : {j : Fin n // (j : ℕ) < k}, α j) => b j) ∘
            (fun ω : (∀ i, α i) => fun i : {i : Fin n // (i : ℕ) < k} => ω ↑i) =
          (fun ω : (∀ i, α i) => ω ↑j) := rfl
        rw [h_eq]
        exact le_iSup₂_of_le j.val j.property le_rfl
  unfold tailMarginal
  apply Measurable.stronglyMeasurable
  -- First show the function is measurable w.r.t. the full product σ-algebra
  have hjoint : StronglyMeasurable (Function.uncurry fun ω y => f (tailSplice k ω y)) := by
    have heq : Function.uncurry (fun ω y => f (tailSplice k ω y)) = f ∘ (fun p => tailSplice k p.1 p.2) := rfl
    rw [heq]
    exact hf.comp_measurable (by
      apply measurable_pi_lambda
      intro a
      simp only [tailSplice]
      by_cases hk : (a : ℕ) < k
      · simp only [hk]
        exact (measurable_pi_apply a).comp measurable_fst
      · simp only [hk]
        exact (measurable_pi_apply a).comp measurable_snd)
  have h_meas : Measurable (fun ω => ∫ y, f (tailSplice k ω y) ∂Measure.pi ν) :=
    (StronglyMeasurable.integral_prod_right (ν := Measure.pi ν) hjoint).measurable
  -- The function factors through the projection to the first k coordinates
  have h_factor : ∀ ω ω' : (∀ i, α i),
      (∀ i : {i : Fin n // (i : ℕ) < k}, ω i = ω' i) →
      ∫ y, f (tailSplice k ω y) ∂Measure.pi ν = ∫ y, f (tailSplice k ω' y) ∂Measure.pi ν := by
    intro ω ω' h_ωω'
    congr 1
    funext y
    congr 1
    funext i
    by_cases hi : (i : ℕ) < k
    · have := h_ωω' ⟨i, hi⟩
      simp [tailSplice, hi, this]
    · simp [tailSplice, hi]
  -- Define π
  let π : ((∀ i, α i) → (∀ i : {i : Fin n // (i : ℕ) < k}, α i)) := fun ω i => ω i
  -- Define extend: pick any default value
  have h_nonempty : ∀ i : Fin n, Nonempty (α i) := fun i => by
    haveI : IsProbabilityMeasure (ν i) := ‹∀ i, IsProbabilityMeasure (ν i)› i
    exact MeasureTheory.nonempty_of_isProbabilityMeasure (ν i)
  let a₀ : ∀ i : Fin n, α i := fun i => (h_nonempty i).some
  let extend : (∀ i : {i : Fin n // (i : ℕ) < k}, α i) → (∀ i : Fin n, α i) :=
    fun ω' i => if hi : (i : ℕ) < k then ω' ⟨i, hi⟩ else a₀ i
  -- h' = h ∘ extend is measurable
  let h' : (∀ i : {i : Fin n // (i : ℕ) < k}, α i) → ℝ := fun ω' => ∫ y, f (tailSplice k (extend ω') y) ∂Measure.pi ν
  have h_extend_meas : Measurable extend := by
    apply measurable_pi_lambda
    intro i
    by_cases hi : (i : ℕ) < k
    · simp only [extend, hi]
      exact measurable_pi_apply _
    · simp only [extend, hi]
      exact measurable_const
  have h_meas_ext_fst : Measurable (extend ∘ Prod.fst : (∀ i : {i : Fin n // (i : ℕ) < k}, α i) × (∀ i : Fin n, α i) → ∀ i : Fin n, α i) := h_extend_meas.comp measurable_fst
  have h'_meas : Measurable h' := by
    have hjoint' : StronglyMeasurable (Function.uncurry fun ω' y => f (tailSplice k (extend ω') y)) := by
      have heq : Function.uncurry (fun ω' y => f (tailSplice k (extend ω') y)) =
          f ∘ (fun p => tailSplice k (extend p.1) p.2) := rfl
      rw [heq]
      exact hf.comp_measurable (by
        apply measurable_pi_lambda
        intro a
        simp only [tailSplice]
        by_cases hak : (a : ℕ) < k
        · simp only [hak]
          exact (measurable_pi_apply a).comp h_meas_ext_fst
        · simp only [hak]
          exact (measurable_pi_apply a).comp measurable_snd)
    exact (StronglyMeasurable.integral_prod_right (ν := Measure.pi ν) hjoint').measurable
  -- Show π '' h⁻¹(s) = h'⁻¹(s)
  have h_image_eq : ∀ s : Set ℝ, π '' ((fun ω => ∫ y, f (tailSplice k ω y) ∂Measure.pi ν) ⁻¹' s) = h' ⁻¹' s := by
    intro t
    ext ω'
    simp only [Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨ω, hωt, hπω'⟩
      have h_eq : h' ω' = ∫ y, f (tailSplice k ω y) ∂Measure.pi ν := by
        apply h_factor (extend ω') ω
        intro i
        have h := congr_fun hπω' i
        simp only [π] at h
        rw [h]
        simp [extend, i.2]
      rw [h_eq]
      exact hωt
    · intro ht
      refine ⟨extend ω', ht, ?_⟩
      ext i
      simp only [π, extend]
      simp [i.2]
  rw [exposureσ_eq_comap_prefix]
  -- Show measurability w.r.t. comap π
  intro s hs
  have h_preimage : MeasurableSet ((fun ω => ∫ y, f (tailSplice k ω y) ∂Measure.pi ν) ⁻¹' s) := h_meas hs
  have h_preimage' : MeasurableSet (h' ⁻¹' s) := h'_meas hs
  have h_eq : (fun ω => ∫ y, f (tailSplice k ω y) ∂Measure.pi ν) ⁻¹' s =
      π ⁻¹' (h' ⁻¹' s) := by
    rw [← h_image_eq s]
    ext ω
    simp only [Set.mem_preimage, Set.mem_image]
    constructor
    · intro hωs
      exact ⟨ω, hωs, rfl⟩
    · rintro ⟨ω', hω's, hπω'ω⟩
      rw [← h_factor ω' ω (fun i => congr_fun hπω'ω i)]
      exact hω's
  rw [h_eq]
  rw [MeasurableSpace.measurableSet_comap]
  exact ⟨h' ⁻¹' s, h_preimage', rfl⟩

private lemma measurePreserving_tailSplice
    (ν : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (ν i)] (k : ℕ) :
    MeasurePreserving (fun p : (∀ i, α i) × (∀ i, α i) => tailSplice k p.1 p.2)
      ((Measure.pi ν).prod (Measure.pi ν)) (Measure.pi ν) := by
  refine ⟨?_, ?_⟩
  · apply measurable_pi_lambda
    intro i
    by_cases hi : (i : ℕ) < k
    · simpa [tailSplice, hi] using (measurable_pi_apply i).comp measurable_fst
    · simpa [tailSplice, hi] using (measurable_pi_apply i).comp measurable_snd
  · symm
    apply Measure.pi_eq
    intro s hs
    rw [Measure.map_apply]
    · have hpre : (fun p : (∀ i, α i) × (∀ i, α i) => tailSplice k p.1 p.2) ⁻¹'
          Set.pi Set.univ s =
          (Set.pi Set.univ fun i : Fin n => if (i : ℕ) < k then s i else Set.univ) ×ˢ
          (Set.pi Set.univ fun i : Fin n => if (i : ℕ) < k then Set.univ else s i) := by
        ext p
        simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_prod]
        constructor
        · intro h
          constructor <;> intro i
          · by_cases hi : (i : ℕ) < k
            · simpa [tailSplice, hi] using h i
            · simp [hi]
          · by_cases hi : (i : ℕ) < k
            · simp [hi]
            · simpa [tailSplice, hi] using h i
        · rintro ⟨h₁, h₂⟩ i
          by_cases hi : (i : ℕ) < k
          · simpa [tailSplice, hi] using h₁ i
          · simpa [tailSplice, hi] using h₂ i
      rw [hpre, Measure.prod_prod, Measure.pi_pi, Measure.pi_pi]
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i _
      by_cases hi : (i : ℕ) < k <;> simp [hi]
    · apply measurable_pi_lambda
      intro i
      by_cases hi : (i : ℕ) < k
      · simpa [tailSplice, hi] using (measurable_pi_apply i).comp measurable_fst
      · simpa [tailSplice, hi] using (measurable_pi_apply i).comp measurable_snd
    · exact MeasurableSet.pi Set.countable_univ (fun i _ => hs i)

private lemma tailMarginal_integrable
    (ν : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (ν i)]
    {f : (∀ i, α i) → ℝ} (hfi : Integrable f (Measure.pi ν)) (k : ℕ) :
    Integrable (tailMarginal ν f k) (Measure.pi ν) := by
  -- Strategy: Use that tailSplice is measure-preserving
  -- Then ∫ ω, |tailMarginal ω| ≤ ∫ ω, ∫ y, |f (tailSplice k ω y)| = ∫ z, |f z| < ∞
  set μ := Measure.pi ν with hμ
  -- The composed function on the product space
  let F : (∀ i, α i) × (∀ i, α i) → ℝ := fun p => f (tailSplice k p.1 p.2)
  -- F is integrable because tailSplice is measure-preserving
  have hF_int : Integrable F ((Measure.pi ν).prod (Measure.pi ν)) := by
    have hmp := measurePreserving_tailSplice ν k
    exact hmp.integrable_comp hfi.aestronglyMeasurable |>.mpr hfi
  -- By Fubini: if F is integrable on product, then ω ↦ ∫ y, F(ω, y) is integrable
  have := MeasureTheory.Integrable.integral_prod_left hF_int
  convert this using 1

private lemma exposure_measurableSet_tailSplice_mem_iff
    (k : ℕ) {s : Set (∀ i, α i)} (hs : MeasurableSet[exposureσ k] s)
    (ω y : ∀ i, α i) : tailSplice k ω y ∈ s ↔ ω ∈ s := by
  have hagree : ∀ i : {i : Fin n // (i : ℕ) < k}, tailSplice k ω y i = ω i := by
    intro ⟨i, hi⟩
    simp [tailSplice, hi]
  -- exposureσ k = comap π where π extracts coordinates < k
  rw [exposureσ_eq_comap_prefix] at hs
  -- Define π
  let π : ((∀ i, α i) → (∀ i : {i : Fin n // (i : ℕ) < k}, α i)) := fun ω i => ω i
  -- π(ω) = π(tailSplice k ω y) because they agree on coordinates < k
  have hpi_eq : π ω = π (tailSplice k ω y) := funext (fun i => (hagree i).symm)
  -- For comap, measurable sets are preimages, so points with same π-value are indistinguishable
  rw [MeasurableSpace.measurableSet_comap] at hs
  obtain ⟨t, ht, rfl⟩ := hs
  change π (tailSplice k ω y) ∈ t ↔ π ω ∈ t
  rw [← hpi_eq]

private lemma setIntegral_tailMarginal_eq
    (ν : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (ν i)]
    {f : (∀ i, α i) → ℝ}
    (hfi : Integrable f (Measure.pi ν)) (k : ℕ)
    {s : Set (∀ i, α i)} (hs : MeasurableSet[exposureσ k] s) :
    ∫ ω in s, tailMarginal ν f k ω ∂(Measure.pi ν) =
      ∫ ω in s, f ω ∂(Measure.pi ν) := by
  let μ := Measure.pi ν
  have hs_full : MeasurableSet s := (exposureσ_le k) s hs
  have hi : Integrable (s.indicator f) μ := hfi.indicator hs_full
  have hcomp : Integrable
      (fun p : (∀ i, α i) × (∀ i, α i) =>
        s.indicator f (tailSplice k p.1 p.2)) (μ.prod μ) := by
    have hmp := measurePreserving_tailSplice ν k
    exact (hmp.integrable_comp hi.aestronglyMeasurable).mpr hi
  rw [← integral_indicator hs_full, ← integral_indicator hs_full]
  have hpoint : s.indicator (tailMarginal ν f k) =
      fun ω => ∫ y, s.indicator f (tailSplice k ω y) ∂μ := by
    funext ω
    by_cases hω : ω ∈ s
    · simp only [Set.indicator_of_mem hω, tailMarginal, μ]
      apply integral_congr_ae
      filter_upwards [] with y
      rw [Set.indicator_of_mem ((exposure_measurableSet_tailSplice_mem_iff k hs ω y).2 hω)]
    · simp only [Set.indicator_of_notMem hω]
      have hnot : ∀ y, tailSplice k ω y ∉ s := fun y hy =>
        hω ((exposure_measurableSet_tailSplice_mem_iff k hs ω y).1 hy)
      simp only [Set.indicator_of_notMem (hnot _), integral_zero]
  rw [hpoint]
  rw [← integral_prod _ hcomp]
  have hmp := measurePreserving_tailSplice ν k
  rw [← hmp.map_eq]
  symm
  apply integral_map hmp.aemeasurable
  rw [hmp.map_eq]
  exact hi.aestronglyMeasurable

/-- Marginalization identity for the exposure filtration of a finite product measure. -/
theorem doob_ae_eq_tailMarginal
    (ν : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (ν i)]
    (f : (∀ i, α i) → ℝ) (hf : StronglyMeasurable f)
    (hfi : Integrable f (Measure.pi ν)) (k : ℕ) :
    doob (Measure.pi ν) f k =ᵐ[Measure.pi ν] tailMarginal ν f k := by
  -- Use uniqueness of conditional expectation
  -- Need: tailMarginal is strongly measurable, integrable, and has correct integrals
  have h_meas : StronglyMeasurable[exposureσ (α := α) k] (tailMarginal ν f k) := tailMarginal_stronglyMeasurable ν hf k
  have h_int := tailMarginal_integrable ν hfi k
  -- Unfold doob to condExp
  simp only [doob]
  -- We need: condExp f | m] =ᵐ tailMarginal
  -- Use: condExp_tail =ᵐ tailMarginal (since tailMarginal is m-measurable)
  have h_tail_eq : (Measure.pi ν)[tailMarginal ν f k | exposureσ k] =ᵐ[Measure.pi ν] tailMarginal ν f k := by
    exact Filter.Eventually.of_forall (fun x => (condExp_of_stronglyMeasurable (exposureσ_le k) h_meas h_int).symm ▸ rfl)
  -- Both condExp f and tailMarginal satisfy: ∫ s, g = ∫ s, f for m-measurable s
  -- By uniqueness, they are a.e. equal
  have h_condExp_integral : ∀ s : Set ((i : Fin n) → α i),
      MeasurableSet[exposureσ k] s →
        ∫ ω in s, (Measure.pi ν)[f | exposureσ k] ω ∂(Measure.pi ν) = ∫ ω in s, f ω ∂(Measure.pi ν) := by
    intro s hs
    exact MeasureTheory.setIntegral_condExp (μ := Measure.pi ν) (m := exposureσ k) (exposureσ_le k) hfi hs
  -- Now use uniqueness: both have equal integrals over all m-measurable sets
  -- And both are m-measurable and integrable
  -- Both condExp f and tailMarginal are exposureσ k-measurable and integrable
  -- and have the same integral over all exposureσ k-measurable sets
  -- Hence they are a.e. equal
  have h_condExp_meas : StronglyMeasurable[exposureσ k] ((Measure.pi ν)[f | exposureσ k]) := doob_stronglyMeasurable _ _ k
  have h_tail_meas : StronglyMeasurable[exposureσ k] (tailMarginal ν f k) := h_meas
  have h_condExp_int : Integrable ((Measure.pi ν)[f | exposureσ k]) (Measure.pi ν) :=
    integrable_condExp (μ := Measure.pi ν) (m := exposureσ k)
  -- Show they have equal integrals on all exposureσ k-measurable sets
  have h_eq_integrals' : ∀ s : Set ((i : Fin n) → α i),
      MeasurableSet[exposureσ k] s →
        (Measure.pi ν) s < ⊤ →
          ∫ ω in s, (Measure.pi ν)[f | exposureσ k] ω ∂(Measure.pi ν) =
            ∫ ω in s, tailMarginal ν f k ω ∂(Measure.pi ν) := by
    intro s hs _
    rw [setIntegral_condExp (μ := Measure.pi ν) (m := exposureσ k) (exposureσ_le k) hfi hs]
    exact (setIntegral_tailMarginal_eq ν hfi k hs).symm
  -- Apply uniqueness using the approach: show condExp f = condExp (tailMarginal) =ᵐ tailMarginal
  have h_condExp_eq : (Measure.pi ν)[f | exposureσ k] =ᵐ[Measure.pi ν] (Measure.pi ν)[tailMarginal ν f k | exposureσ k] := by
    have h_int_eq_sub : ∀ s : Set ((i : Fin n) → α i),
        MeasurableSet[exposureσ k] s → 
          (Measure.pi ν) s < ⊤ →
          ∫ ω in s, (Measure.pi ν)[f | exposureσ k] ω ∂(Measure.pi ν) =
          ∫ ω in s, (Measure.pi ν)[tailMarginal ν f k | exposureσ k] ω ∂(Measure.pi ν) := by
      intro s hs hs_inf
      rw [setIntegral_condExp (μ := Measure.pi ν) (m := exposureσ k) (exposureσ_le k) hfi hs,
          setIntegral_condExp (μ := Measure.pi ν) (m := exposureσ k) (exposureσ_le k) h_int hs]
      rw [setIntegral_tailMarginal_eq ν hfi k hs]
    -- Use ae equality via the trimmed measure
    have hm : exposureσ (α := α) k ≤ MeasurableSpace.pi := exposureσ_le k
    -- In the trimmed measure, all sets are exposureσ k-measurable
    have h_trim_eq : ∀ᵐ ω ∂(Measure.pi ν).trim hm, 
        (Measure.pi ν)[f | exposureσ (α := α) k] ω = (Measure.pi ν)[tailMarginal ν f k | exposureσ (α := α) k] ω := by
      -- In the trimmed measure, all sets are exposureσ k-measurable
      -- Both functions are integrable w.r.t. the trimmed measure
      have h_int_trim_f : MeasureTheory.Integrable ((Measure.pi ν)[f | exposureσ k]) ((Measure.pi ν).trim hm) := 
        (integrable_condExp (μ := Measure.pi ν) (m := exposureσ k)).trim hm h_condExp_meas
      have h_int_trim_g : MeasureTheory.Integrable ((Measure.pi ν)[tailMarginal ν f k | exposureσ k]) ((Measure.pi ν).trim hm) := 
        (integrable_condExp (μ := Measure.pi ν) (m := exposureσ k)).trim hm (doob_stronglyMeasurable _ _ _)
      -- Use uniqueness for the trimmed measure
      exact MeasureTheory.Integrable.ae_eq_of_forall_setIntegral_eq 
        (α := ∀ i, α i) (E := ℝ) (μ := (Measure.pi ν).trim hm)
        (f := (Measure.pi ν)[f | exposureσ k])
        (g := (Measure.pi ν)[tailMarginal ν f k | exposureσ k])
        h_int_trim_f h_int_trim_g (fun s hs _ => by
          have h1 : ∫ x in s, (Measure.pi ν)[f | exposureσ k] x ∂(Measure.pi ν).trim hm = 
                    ∫ x in s, (Measure.pi ν)[f | exposureσ k] x ∂Measure.pi ν := 
            (MeasureTheory.setIntegral_trim hm (f := (Measure.pi ν)[f | exposureσ k]) h_condExp_meas hs).symm
          have h2 : ∫ x in s, (Measure.pi ν)[tailMarginal ν f k | exposureσ k] x ∂(Measure.pi ν).trim hm = 
                    ∫ x in s, (Measure.pi ν)[tailMarginal ν f k | exposureσ k] x ∂Measure.pi ν := 
            (MeasureTheory.setIntegral_trim hm (f := (Measure.pi ν)[tailMarginal ν f k | exposureσ k]) (doob_stronglyMeasurable _ _ _) hs).symm
          rw [h1, h2]
          exact h_int_eq_sub s hs (MeasureTheory.measure_lt_top _ _))
    exact MeasureTheory.ae_of_ae_trim hm h_trim_eq
  exact h_condExp_eq.trans h_tail_eq

private lemma tailSplice_succ_and_self_differ_only_at
    (k : ℕ) (hk : k < n) (ω y : ∀ i, α i) :
    ∀ i, i ≠ (⟨k, hk⟩ : Fin n) →
      tailSplice (k + 1) ω y i = tailSplice k ω y i := by
  intro i hi
  simp only [tailSplice]
  split_ifs with h1 h2 <;> try rfl
  · -- case: i.val < k + 1 and ¬(i.val < k), so i.val = k
    exfalso
    apply hi
    ext
    simp only
    omega
  · -- case: ¬(i.val < k + 1) and i.val < k, contradiction
    omega

private lemma tailMarginal_increment_bound
    (ν : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (ν i)]
    (f : (∀ i, α i) → ℝ) (hf : StronglyMeasurable f)
    {c : ℕ → ℝ}
    (hbd : ∀ (j : Fin n) (ω ω' : ∀ i, α i),
      (∀ i, i ≠ j → ω i = ω' i) → |f ω - f ω'| ≤ c (j : ℕ))
    (j : ℕ) (hj : j < n) (ω : ∀ i, α i) :
    |tailMarginal ν f (j + 1) ω - tailMarginal ν f j ω| ≤ c j := by
  -- The splice functions differ only at index j
  have hdiff : ∀ y : ∀ i, α i, ∀ i : Fin n, i ≠ ⟨j, hj⟩ →
      tailSplice (j + 1) ω y i = tailSplice j ω y i := fun y => tailSplice_succ_and_self_differ_only_at j hj ω y
  -- Therefore f values differ by at most c j
  have hbound : ∀ y : ∀ i, α i, |f (tailSplice (j + 1) ω y) - f (tailSplice j ω y)| ≤ c j := by
    intro y
    apply hbd ⟨j, hj⟩ (tailSplice (j + 1) ω y) (tailSplice j ω y)
    intro i hi
    exact hdiff y i hi
  -- Unfold tailMarginal
  simp only [tailMarginal]
  -- Handle empty space case
  -- The space is non-empty because each α i carries a probability measure
  have hne : Nonempty (∀ i, α i) := by
    have : ∀ i, Nonempty (α i) := fun i => by
      have hprov : (ν i) Set.univ = 1 := IsProbabilityMeasure.measure_univ
      by_contra hempty
      haveI : IsEmpty (α i) := by simpa using hempty
      have hZero : (ν i) Set.univ = 0 := by
        simp [Set.eq_empty_of_isEmpty]
      rw [hprov] at hZero
      exact ne_of_gt zero_lt_one hZero
    exact ⟨fun i => (this i).some⟩
  -- The difference function is bounded
  have hdiff_bound : ∀ y, |f (tailSplice (j + 1) ω y) - f (tailSplice j ω y)| ≤ c j := hbound
  -- c j ≥ 0 since |...| ≥ 0
  have hc : 0 ≤ c j := by
    obtain ⟨y⟩ := hne
    exact le_trans (abs_nonneg _) (hbound y)
  -- If one is integrable, so is the other (bounded difference)
  have hIntegrable_eq : Integrable (fun y => f (tailSplice (j + 1) ω y)) (Measure.pi ν) ↔
                       Integrable (fun y => f (tailSplice j ω y)) (Measure.pi ν) := by
    have hdiff_integrable : MeasureTheory.Integrable
        (fun y => f (tailSplice (j + 1) ω y) - f (tailSplice j ω y)) (Measure.pi ν) := by
      refine MeasureTheory.Integrable.mono' (MeasureTheory.integrable_const (c j)) ?_ ?_
      · refine MeasureTheory.AEStronglyMeasurable.sub ?_ ?_
        · have hm1 : Measurable (tailSplice (j + 1) ω) := by
            rw [measurable_pi_iff]
            intro i
            simp only [tailSplice]
            split_ifs with h
            · exact measurable_const
            · exact measurable_pi_apply i
          exact StronglyMeasurable.aestronglyMeasurable (hf.comp_measurable hm1)
        · have hm2 : Measurable (tailSplice j ω) := by
            rw [measurable_pi_iff]
            intro i
            simp only [tailSplice]
            split_ifs with h
            · exact measurable_const
            · exact measurable_pi_apply i
          exact StronglyMeasurable.aestronglyMeasurable (hf.comp_measurable hm2)
      · exact MeasureTheory.ae_of_all _ (fun y => by simpa [Real.norm_eq_abs] using hdiff_bound y)
    constructor
    · intro hg
      have : (fun y => f (tailSplice j ω y)) = (fun y => f (tailSplice (j + 1) ω y) -
          (f (tailSplice (j + 1) ω y) - f (tailSplice j ω y))) := by funext y; ring
      rw [this]
      exact Integrable.sub hg hdiff_integrable
    · intro hh
      have : (fun y => f (tailSplice (j + 1) ω y)) = (fun y => f (tailSplice j ω y) +
          (f (tailSplice (j + 1) ω y) - f (tailSplice j ω y))) := by funext y; ring
      rw [this]
      exact Integrable.add hh hdiff_integrable
  -- Bound the difference of integrals
  by_cases hInt : Integrable (fun y => f (tailSplice (j + 1) ω y)) (Measure.pi ν)
  · -- Both integrable case
    have hInt' := (hIntegrable_eq.mp hInt)
    have hsub := integral_sub hInt hInt'
    calc |∫ y, f (tailSplice (j + 1) ω y) ∂Measure.pi ν - ∫ y, f (tailSplice j ω y) ∂Measure.pi ν|
        = |∫ y, (f (tailSplice (j + 1) ω y) - f (tailSplice j ω y)) ∂Measure.pi ν| := by rw [hsub]
      _ ≤ ∫ y, |f (tailSplice (j + 1) ω y) - f (tailSplice j ω y)| ∂Measure.pi ν := by
        simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (μ := Measure.pi ν) (f := fun y => f (tailSplice (j + 1) ω y) - f (tailSplice j ω y))
      _ ≤ ∫ _ : ∀ i, α i, c j ∂Measure.pi ν := by
        apply MeasureTheory.integral_mono_of_nonneg
        · exact MeasureTheory.ae_of_all _ (fun _ => abs_nonneg _)
        · exact MeasureTheory.integrable_const _
        · exact MeasureTheory.ae_of_all _ hdiff_bound
      _ = c j := by
        simp [MeasureTheory.integral_const]
  · -- Neither integrable case: both integrals are 0
    have hInt' : ¬Integrable (fun y => f (tailSplice j ω y)) (Measure.pi ν) := mt (hIntegrable_eq.mpr) hInt
    simp [MeasureTheory.integral_undef hInt, MeasureTheory.integral_undef hInt']
    exact hc

/-- **M6.5 — the Doob increment is a.e. bounded by the bounded-difference coefficient.** On a product
measure, if `f` has bounded differences (toggling coordinate `j` changes `f` by `≤ c j`), then the
exposure-filtration Doob increment is bounded a.e. by `c j`. -/
theorem doob_increment_ae_bound
    (ν : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (ν i)]
    (f : (∀ i, α i) → ℝ) (hf : StronglyMeasurable f) (hfi : Integrable f (Measure.pi ν))
    {c : ℕ → ℝ}
    (hbd : ∀ (j : Fin n) (ω ω' : ∀ i, α i),
      (∀ i, i ≠ j → ω i = ω' i) → |f ω - f ω'| ≤ c (j : ℕ))
    (j : ℕ) (hj : j < n) :
    ∀ᵐ ω ∂(Measure.pi ν),
      |doob (Measure.pi ν) f (j + 1) ω - doob (Measure.pi ν) f j ω| ≤ c j := by
  -- Get a.e. equality of doob with tailMarginal
  have h_j : doob (Measure.pi ν) f j =ᵐ[Measure.pi ν] tailMarginal ν f j :=
    doob_ae_eq_tailMarginal ν f hf hfi j
  have h_j1 : doob (Measure.pi ν) f (j + 1) =ᵐ[Measure.pi ν] tailMarginal ν f (j + 1) :=
    doob_ae_eq_tailMarginal ν f hf hfi (j + 1)
  -- The increment of tailMarginal is bounded pointwise
  have hbound : ∀ ω, |tailMarginal ν f (j + 1) ω - tailMarginal ν f j ω| ≤ c j :=
    tailMarginal_increment_bound ν f hf hbd j hj
  -- Transform the goal using a.e. equality
  filter_upwards [h_j1, h_j] with ω hω1 hω2
  rw [hω1, hω2]
  exact hbound ω

end Nibble
