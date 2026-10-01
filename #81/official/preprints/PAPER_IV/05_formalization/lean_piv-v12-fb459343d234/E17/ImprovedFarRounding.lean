import E17.Cleanup
import E17.FarBudget
import PaperIV.RC01TriangleTransfer
import PaperIV.RC01UniformDenseGate
import PaperIV.RC01DenseAssembly
import PaperIV.RC01TriangleSchedule

/- Source: Bridge/FaceTransfer.lean. Research validation bundle. -/

/-! Literal F1 transfer on a selected family of real K4 copies. Contributions
to a common triangle are summed, not chosen or identified by cardinality. -/
namespace E17Bridge
open Finset PaperIV.FarRounding E17.Cleanup
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

private theorem sum_faces (K : Finset V) (hK : K ∈ items G) (h4 : K.card = 4)
    (f : Finset V → ℚ) :
    (∑ T ∈ items G, f T * ∑ c ∈ K, if T = K.erase c then (1/2 : ℚ) else 0) =
      ∑ c ∈ K, f (K.erase c) * (1/2 : ℚ) := by
  simp only [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro c hc
  have ht : K.erase c ∈ items G := mem_items_of_subset hK (erase_subset _ _)
    (by rw [card_erase_of_mem hc, h4])
  simp only [mul_ite, mul_zero, sum_ite_eq', if_pos ht]

open Classical in
/-- Convert selected K4 copies to all four half-weight faces; retain others. -/
noncomputable def faceTransfer (S : Finset (Finset V))
    (hS : ∀ K ∈ S, K.card = 4) : Transfer G where
  a K T := if K ∈ S then ∑ c ∈ K, if T = K.erase c then (1/2 : ℚ) else 0
    else if T = K then 1 else 0
  nonneg K T := by split_ifs <;> positivity
  sub K hK T hT hne := by
    split_ifs at hne with hs ht
    · obtain ⟨c, hc, hn⟩ := exists_ne_zero_of_sum_ne_zero hne
      have he : T = K.erase c := by by_contra he; simp [he] at hn
      rw [he]; exact erase_subset _ _
    · subst T; exact subset_rfl
    · exact (hne rfl).elim
  row K hK e he := by
    by_cases hs : K ∈ S
    · simp only [if_pos hs]
      have hh := sum_faces K hK (hS K hs) (fun T => if e ∈ pairs T then 1 else 0)
      simp only [ite_mul, one_mul, zero_mul] at hh
      rw [hh]
      simpa only [ite_mul, one_mul, zero_mul] using (f1_loads (hS K hs) (1 : ℚ) he).le
    · simp only [if_neg hs]
      calc
        _ ≤ ∑ T ∈ items G, (if T = K then (1 : ℚ) else 0) := by
          apply sum_le_sum; intro T hT; split_ifs <;> norm_num
        _ = 1 := by simp [hK]

/-- The loss is exactly one unit of gain per unit mass of converted K4s. -/
theorem faceTransfer_loss (S : Finset (Finset V))
    (hS : ∀ K ∈ S, K.card = 4) (hSi : S ⊆ items G) (x : FracPacking G ℚ) :
    x.value - ((faceTransfer S hS).apply x).value = ∑ K ∈ S, x.weight K := by
  classical
  rw [Transfer.loss_eq]
  have hrow : ∀ K ∈ items G,
      gainF ℚ K - ∑ T ∈ items G, gainF ℚ T * (faceTransfer (G := G) S hS).a K T =
        if K ∈ S then 1 else 0 := by
    intro K hK
    by_cases hs : K ∈ S
    · simp only [faceTransfer, if_pos hs]
      rw [sum_faces K hK (hS K hs)]
      have hh := f1_value (hS K hs) (1 : ℚ)
      norm_num only [one_div] at hh ⊢
      rw [hh, gainF, hS K hs]
      norm_num [Nat.choose]
    · simp [faceTransfer, hs, hK]
  rw [sum_congr rfl (fun K hK => congrArg (fun t : ℚ => x.weight K * t) (hrow K hK))]
  simp only [mul_ite, mul_one, mul_zero]
  rw [sum_ite_mem, inter_eq_right.mpr hSi]

/-- Every four-vertex target is unchanged unless selected, in which case its
weight is zero. No face of a real K4 can introduce another K4. -/
theorem faceTransfer_weight_four (S : Finset (Finset V))
    (hS : ∀ K ∈ S, K.card = 4) (x : FracPacking G ℚ)
    {T : Finset V} (hTi : T ∈ items G) (hT : T.card = 4) :
    ((faceTransfer S hS).apply x).weight T = if T ∈ S then 0 else x.weight T := by
  classical
  change (∑ K ∈ items G, x.weight K * (faceTransfer S hS).a K T) = _
  have hc : ∀ K ∈ items G, (faceTransfer (G := G) S hS).a K T =
      if K = T then (if T ∈ S then 0 else 1) else 0 := by
    intro K hK
    by_cases hs : K ∈ S
    · have hf : ∀ c ∈ K, T ≠ K.erase c := by
        intro c hc he
        have ht := congrArg Finset.card he
        rw [card_erase_of_mem hc, hS K hs, hT] at ht
        omega
      simp only [faceTransfer, if_pos hs, sum_eq_zero (fun c hc => if_neg (hf c hc))]
      by_cases he : K = T
      · subst K; simp [hs]
      · simp [he]
    · simp only [faceTransfer, if_neg hs]
      by_cases he : K = T
      · subst K; simp [hs]
      · simp [he, Ne.symm he]
  rw [sum_congr rfl (fun K hK => congrArg (fun t : ℚ => x.weight K * t) (hc K hK))]
  simp only [mul_ite, mul_zero]
  rw [sum_ite_eq', if_pos hTi]
  split_ifs <;> simp

/-- Subcopy transfers preserve avoidance of every forbidden physical edge. -/
theorem transfer_avoids (τ : Transfer G) (x : FracPacking G ℚ)
    (B : Finset (Sym2 V))
    (hx : ∀ K ∈ items G, x.weight K ≠ 0 → Disjoint (pairs K) B)
    {T : Finset V} (hTi : T ∈ items G) (hT : (τ.apply x).weight T ≠ 0) :
    Disjoint (pairs T) B := by
  obtain ⟨K, hK, hne⟩ := exists_ne_zero_of_sum_ne_zero hT
  have hw : x.weight K ≠ 0 := (mul_ne_zero_iff.mp hne).1
  have ha : τ.a K T ≠ 0 := (mul_ne_zero_iff.mp hne).2
  exact (hx K hK hw).mono_left (pairs_mono (τ.sub K hK T hTi ha))

#print axioms faceTransfer_loss
#print axioms faceTransfer_weight_four
#print axioms transfer_avoids
end E17Bridge



/- Source: Bridge/ProfileCleanup.lean. Research validation bundle. -/

/-! Physical profile cleanup. Convert complete light K4 fibres first, then
aggregate and drop complete light triangle fibres. No packing oracle. -/
namespace E17Bridge
open Finset PaperIV.FarRounding E17.Cleanup
open PaperIV.RegularityFormat PaperIV.RC01MixedPatterns
  PaperIV.RC01CanonicalSlots PaperIV.RC01K3Pool PaperIV.RC01CanonicalProfile
  PaperIV.RC01CanonicalFiberProfile PaperIV.RC01CleanFiber
  PaperIV.RC01PatternCapacity PaperIV.RC01ResidualCoverage
  PaperIV.RC01CanonicalValueAccounting
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

open Classical in
noncomputable def dropCopies (x : FracPacking G ℚ) (D : Finset (Finset V)) :
    FracPacking G ℚ where
  weight K := if K ∈ D then 0 else x.weight K
  weight_nonneg K := by split_ifs; exact le_rfl; exact x.weight_nonneg K
  capacity e he := by
    refine le_trans (sum_le_sum fun K hK => ?_) (x.capacity e he)
    split_ifs <;> simp_all [x.weight_nonneg]

theorem dropCopies_loss (x : FracPacking G ℚ) (D : Finset (Finset V))
    (hDi : D ⊆ items G) (hD3 : ∀ K ∈ D, K.card = 3) :
    x.value - (dropCopies x D).value = 2 * ∑ K ∈ D, x.weight K := by
  classical
  have hf : (items G).filter (fun K => K ∈ D) = D := by
    ext K; simp only [mem_filter]; exact ⟨And.right, fun h => ⟨hDi h, h⟩⟩
  have hsplit := sum_filter_add_sum_filter_not (items G) (fun K => K ∈ D)
    (fun K => gainF ℚ K * x.weight K)
  have he : (dropCopies x D).value =
      ∑ K ∈ (items G).filter (fun K => K ∉ D), gainF ℚ K * x.weight K := by
    simp only [FracPacking.value, dropCopies, sum_filter]
    apply sum_congr rfl; intro K hK; split_ifs <;> simp_all
  rw [hf] at hsplit
  have hg : (∑ K ∈ D, gainF ℚ K * x.weight K) = 2 * ∑ K ∈ D, x.weight K := by
    rw [mul_sum]; apply sum_congr rfl; intro K hK
    norm_num [gainF, hD3 K hK]
  change (∑ K ∈ items G, gainF ℚ K * x.weight K) - _ = _
  rw [he]; linarith

open Classical in
noncomputable def lightUnion {I : Type*} [DecidableEq I] (P : Finset I)
    (F : I → Finset (Finset V)) (x : FracPacking G ℚ) (θ : ℚ) :=
  (P.filter (fun σ => rawMass x F σ < θ)).biUnion F

theorem mem_lightUnion_iff {I : Type*} [DecidableEq I] (P : Finset I)
    (F : I → Finset (Finset V)) (hdis : Set.PairwiseDisjoint (P : Set I) F)
    (x : FracPacking G ℚ) (θ : ℚ) {σ : I} (hσ : σ ∈ P)
    {K : Finset V} (hK : K ∈ F σ) :
    K ∈ lightUnion P F x θ ↔ rawMass x F σ < θ := by
  classical
  constructor
  · intro h
    obtain ⟨τ, hτ, hKt⟩ := mem_biUnion.mp h
    have he : τ = σ := by
      by_contra hn
      exact (disjoint_left.mp (hdis (mem_filter.mp hτ).1 hσ hn)) hKt hK
    subst τ; exact (mem_filter.mp hτ).2
  · intro h; exact mem_biUnion.mpr ⟨σ, mem_filter.mpr ⟨hσ, h⟩, hK⟩

theorem lightUnion_mass_le {I : Type*} [DecidableEq I] (P : Finset I)
    (F : I → Finset (Finset V)) (hdis : Set.PairwiseDisjoint (P : Set I) F)
    (x : FracPacking G ℚ) (θ : ℚ) (hθ : 0 ≤ θ) :
    ∑ K ∈ lightUnion P F x θ, x.weight K ≤ (P.card : ℚ) * θ := by
  classical
  rw [lightUnion, sum_biUnion (fun σ hσ τ hτ hn =>
    hdis (mem_filter.mp hσ).1 (mem_filter.mp hτ).1 hn)]
  calc
    _ ≤ ∑ _σ ∈ P.filter (fun σ => rawMass x F σ < θ), θ :=
      sum_le_sum fun σ hσ => (mem_filter.mp hσ).2.le
    _ = ((P.filter (fun σ => rawMass x F σ < θ)).card : ℚ) * θ := by
      rw [sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast card_filter_le P _) hθ

private theorem slot3_mem {δ : ℚ} (R : EqualRegularity G δ) {S}
    (hS : S ∈ goodK3Slots R) : Sum.inl S ∈ mixedPatterns R :=
  mem_mixedPatterns_iff.mpr (Or.inl ⟨S, hS, rfl⟩)
private theorem slot4_mem {δ : ℚ} (R : EqualRegularity G δ) {S}
    (hS : S ∈ goodK4Slots R) : Sum.inr S ∈ mixedPatterns R :=
  mem_mixedPatterns_iff.mpr (Or.inr ⟨S, hS, rfl⟩)

theorem fiber3_card {δ : ℚ} (R : EqualRegularity G δ) {S K}
    (hS : S ∈ goodK3Slots R) (hK : K ∈ mixedFiber R (Sum.inl S)) : K.card = 3 := by
  have h := (mem_profileFiber.mp
    ((mem_mixedFiber_iff_mem_profileFiber R (slot3_mem R hS)).mp hK)).2.2
  rw [card_profileOfMixed R (slot3_mem R hS)] at h
  exact h

theorem fiber4_card {δ : ℚ} (R : EqualRegularity G δ) {S K}
    (hS : S ∈ goodK4Slots R) (hK : K ∈ mixedFiber R (Sum.inr S)) : K.card = 4 := by
  have h := (mem_profileFiber.mp
    ((mem_mixedFiber_iff_mem_profileFiber R (slot4_mem R hS)).mp hK)).2.2
  rw [card_profileOfMixed R (slot4_mem R hS)] at h
  exact h

theorem fibers3_disjoint {δ : ℚ} (R : EqualRegularity G δ) :
    Set.PairwiseDisjoint (goodK3Slots R : Set (Finset (Finset V)))
      (fun S => mixedFiber R (Sum.inl S)) := by
  intro S hS T hT hn
  exact mixedFiber_pairwiseDisjoint R (slot3_mem R hS) (slot3_mem R hT)
    (fun h => hn (Sum.inl.inj h))
theorem fibers4_disjoint {δ : ℚ} (R : EqualRegularity G δ) :
    Set.PairwiseDisjoint (goodK4Slots R : Set (Finset (Finset V)))
      (fun S => mixedFiber R (Sum.inr S)) := by
  intro S hS T hT hn
  exact mixedFiber_pairwiseDisjoint R (slot4_mem R hS) (slot4_mem R hT)
    (fun h => hn (Sum.inr.inj h))

noncomputable def smallFours {δ : ℚ} (R : EqualRegularity G δ)
    (x : FracPacking G ℚ) (θ : ℚ) :=
  lightUnion (goodK4Slots R) (fun S => mixedFiber R (Sum.inr S)) x θ

theorem smallFours_spec {δ : ℚ} (R : EqualRegularity G δ)
    (x : FracPacking G ℚ) (θ : ℚ) {K} (hK : K ∈ smallFours R x θ) :
    K ∈ items G ∧ K.card = 4 := by
  obtain ⟨S, hS, hK⟩ := mem_biUnion.mp hK
  have hs := (mem_filter.mp hS).1
  exact ⟨mixedFiber_subset_items R (slot4_mem R hs) hK, fiber4_card R hs hK⟩

noncomputable def convertLightFours {δ : ℚ} (R : EqualRegularity G δ)
    (x : FracPacking G ℚ) (θ : ℚ) : FracPacking G ℚ :=
  (faceTransfer (smallFours R x θ) (fun _ hK => (smallFours_spec R x θ hK).2)).apply x

noncomputable def smallThrees {δ : ℚ} (R : EqualRegularity G δ)
    (x : FracPacking G ℚ) (θ : ℚ) :=
  lightUnion (goodK3Slots R) (fun S => mixedFiber R (Sum.inl S)) x θ

theorem smallThrees_spec {δ : ℚ} (R : EqualRegularity G δ)
    (x : FracPacking G ℚ) (θ : ℚ) {K} (hK : K ∈ smallThrees R x θ) :
    K ∈ items G ∧ K.card = 3 := by
  obtain ⟨S, hS, hK⟩ := mem_biUnion.mp hK
  have hs := (mem_filter.mp hS).1
  exact ⟨mixedFiber_subset_items R (slot3_mem R hs) hK, fiber3_card R hs hK⟩

/-- The actual packing used by B7: faces are aggregated before light triangles
are discarded. Both stages act on literal copies in the original graph. -/
noncomputable def profileCleanup {δ : ℚ} (R : EqualRegularity G δ)
    (x : FracPacking G ℚ) (θ : ℚ) : FracPacking G ℚ :=
  let z := convertLightFours R x θ
  dropCopies z (smallThrees R z θ)

theorem profileCleanup_loss {δ : ℚ} (R : EqualRegularity G δ)
    (x : FracPacking G ℚ) (θ : ℚ) (hθ : 0 ≤ θ) :
    x.value - (profileCleanup R x θ).value ≤
      ((E17.FarBudget.N4 R : ℚ) + 2 * E17.FarBudget.N3 R) * θ := by
  have h4 := faceTransfer_loss (G := G) (smallFours R x θ)
    (fun _ hK => (smallFours_spec R x θ hK).2)
    (fun _ hK => (smallFours_spec R x θ hK).1) x
  have h4b := lightUnion_mass_le (goodK4Slots R) _ (fibers4_disjoint R) x θ hθ
  let z := convertLightFours R x θ
  have h3 := dropCopies_loss z (smallThrees R z θ)
    (fun _ hK => (smallThrees_spec R z θ hK).1)
    (fun _ hK => (smallThrees_spec R z θ hK).2)
  have h3b := lightUnion_mass_le (goodK3Slots R) _ (fibers3_disjoint R) z θ hθ
  change x.value - z.value = _ at h4
  change x.value - (dropCopies z (smallThrees R z θ)).value ≤ _
  change (∑ K ∈ smallFours R x θ, x.weight K) ≤ _ at h4b
  change (∑ K ∈ smallThrees R z θ, z.weight K) ≤ _ at h3b
  unfold E17.FarBudget.N4 E17.FarBudget.N3
  nlinarith only [h4, h3, h4b, h3b]

theorem profileCleanup_mass_three {δ : ℚ} (R : EqualRegularity G δ)
    (x : FracPacking G ℚ) (θ : ℚ) {S} (hS : S ∈ goodK3Slots R) :
    let z := convertLightFours R x θ
    rawMass (profileCleanup R x θ) (mixedFiber R) (Sum.inl S) =
      if rawMass z (mixedFiber R) (Sum.inl S) < θ then 0
      else rawMass z (mixedFiber R) (Sum.inl S) := by
  classical
  dsimp only
  let z := convertLightFours R x θ
  have hm : ∀ K ∈ mixedFiber R (Sum.inl S),
      K ∈ smallThrees R z θ ↔ rawMass z (mixedFiber R) (Sum.inl S) < θ := by
    intro K hK
    exact mem_lightUnion_iff _ _ (fibers3_disjoint R) z θ hS hK
  change (∑ K ∈ mixedFiber R (Sum.inl S),
    if K ∈ smallThrees R z θ then 0 else z.weight K) = _
  by_cases h : rawMass z (mixedFiber R) (Sum.inl S) < θ
  · rw [if_pos h]; apply sum_eq_zero; intro K hK; rw [if_pos ((hm K hK).mpr h)]
  · rw [if_neg h]; apply sum_congr rfl; intro K hK; rw [if_neg (fun hk => h ((hm K hK).mp hk))]

theorem profileCleanup_mass_four {δ : ℚ} (R : EqualRegularity G δ)
    (x : FracPacking G ℚ) (θ : ℚ) {S} (hS : S ∈ goodK4Slots R) :
    rawMass (profileCleanup R x θ) (mixedFiber R) (Sum.inr S) =
      if rawMass x (mixedFiber R) (Sum.inr S) < θ then 0
      else rawMass x (mixedFiber R) (Sum.inr S) := by
  classical
  let z := convertLightFours R x θ
  have hm : ∀ K ∈ mixedFiber R (Sum.inr S),
      K ∈ smallFours R x θ ↔ rawMass x (mixedFiber R) (Sum.inr S) < θ := by
    intro K hK
    exact mem_lightUnion_iff _ _ (fibers4_disjoint R) x θ hS hK
  have hw : ∀ K ∈ mixedFiber R (Sum.inr S),
      (profileCleanup R x θ).weight K = if K ∈ smallFours R x θ then 0 else x.weight K := by
    intro K hK
    have h4 := fiber4_card R hS hK
    have hn : K ∉ smallThrees R z θ := by
      intro hh; have := (smallThrees_spec R z θ hh).2; omega
    change (if K ∈ smallThrees R z θ then 0 else z.weight K) = _
    rw [if_neg hn]
    exact faceTransfer_weight_four _ _ x (mixedFiber_subset_items R (slot4_mem R hS) hK) h4
  unfold rawMass
  rw [sum_congr rfl hw]
  change (∑ K ∈ mixedFiber R (Sum.inr S), if K ∈ smallFours R x θ then 0 else x.weight K) =
    if rawMass x (mixedFiber R) (Sum.inr S) < θ then 0
    else rawMass x (mixedFiber R) (Sum.inr S)
  by_cases h : rawMass x (mixedFiber R) (Sum.inr S) < θ
  · rw [if_pos h]; apply sum_eq_zero; intro K hK; rw [if_pos ((hm K hK).mpr h)]
  · rw [if_neg h]; apply sum_congr rfl; intro K hK; rw [if_neg (fun hk => h ((hm K hK).mp hk))]

/-- No profile has a positive mass below the threshold after cleanup. -/
theorem profileCleanup_zero_or_heavy {δ : ℚ} (R : EqualRegularity G δ)
    (x : FracPacking G ℚ) (θ : ℚ) {σ} (hσ : σ ∈ mixedPatterns R) :
    rawMass (profileCleanup R x θ) (mixedFiber R) σ = 0 ∨
      θ ≤ rawMass (profileCleanup R x θ) (mixedFiber R) σ := by
  rcases mem_mixedPatterns_iff.mp hσ with ⟨S,hS,rfl⟩ | ⟨S,hS,rfl⟩
  · rw [profileCleanup_mass_three R x θ hS]
    split_ifs with h; exact Or.inl rfl; exact Or.inr (le_of_not_gt h)
  · rw [profileCleanup_mass_four R x θ hS]
    split_ifs with h; exact Or.inl rfl; exact Or.inr (le_of_not_gt h)

theorem profileCleanup_avoids {δ : ℚ} (R : EqualRegularity G δ)
    (x : FracPacking G ℚ) (θ : ℚ) (B : Finset (Sym2 V))
    (hx : ∀ K ∈ items G, x.weight K ≠ 0 → Disjoint (pairs K) B)
    {K} (hK : K ∈ items G) (hw : (profileCleanup R x θ).weight K ≠ 0) :
    Disjoint (pairs K) B := by
  classical
  let z := convertLightFours R x θ
  have hz : z.weight K ≠ 0 := by
    change (if K ∈ smallThrees R z θ then 0 else z.weight K) ≠ 0 at hw
    split_ifs at hw; exact (hw rfl).elim; exact hw
  exact transfer_avoids _ x B hx hK hz

/-- Clean support plus zero-or-heavy fibres makes the old residual exactly zero. -/
theorem offCanonicalValue_eq_zero_of_pure {δ : ℚ} (R : EqualRegularity G δ)
    (y : FracPacking G ℚ) (d θ : ℚ)
    (havoid : ∀ K ∈ items G, y.weight K ≠ 0 →
      Disjoint (pairs K) (discardEdges G R (garbage R) d))
    (hpure : ∀ σ ∈ mixedPatterns R, rawMass y (mixedFiber R) σ = 0 ∨
      θ ≤ rawMass y (mixedFiber R) σ) :
    offCanonicalValue R y (denseHeavyPatterns R y d θ) = 0 := by
  classical
  apply sum_eq_zero
  intro K hK
  have hKi := (mem_filter.mp hK).1
  have hnot := (mem_filter.mp hK).2
  by_cases hw : y.weight K = 0
  · rw [hw, mul_zero]
  · obtain ⟨σ,hσ,hKs,hdense⟩ := exists_dense_mixedPattern_of_avoids_discards
      R (garbage R) d (fun _ hv => cover_of_notMem_garbage R hv) hKi
      (fun e he heK => (disjoint_left.mp (havoid K hKi hw)) heK he)
    have hm : y.weight K ≤ rawMass y (mixedFiber R) σ :=
      single_le_sum (fun J _ => y.weight_nonneg J) hKs
    have hheavy : θ ≤ rawMass y (mixedFiber R) σ := by
      rcases hpure σ hσ with hz | hh
      · rw [hz] at hm; exact (hw (le_antisymm hm (y.weight_nonneg K))).elim
      · exact hh
    exact (hnot (mem_biUnion.mpr ⟨σ, mem_filter.mpr ⟨hσ,hdense,hheavy⟩,hKs⟩)).elim

theorem profileCleanup_offCanonical_zero {δ : ℚ} (R : EqualRegularity G δ)
    (x : FracPacking G ℚ) (d θ : ℚ)
    (hx : ∀ K ∈ items G, x.weight K ≠ 0 →
      Disjoint (pairs K) (discardEdges G R (garbage R) d)) :
    offCanonicalValue R (profileCleanup R x θ)
      (denseHeavyPatterns R (profileCleanup R x θ) d θ) = 0 :=
  offCanonicalValue_eq_zero_of_pure R _ d θ
    (fun _ hi hw => profileCleanup_avoids R x θ _ hx hi hw)
    (fun _ hs => profileCleanup_zero_or_heavy R x θ hs)

#print axioms profileCleanup_loss
#print axioms profileCleanup_zero_or_heavy
#print axioms profileCleanup_offCanonical_zero
end E17Bridge



/- Source: Bridge/TriangleMass.lean. Research validation bundle. -/

/-! Research candidate: this file is not part of the verified four-theorem
bridge audit. Compile it separately before assigning any PASS status. -/
namespace E17Bridge
open Finset PaperIV.FarRounding E17.Cleanup

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Every selected family loses at most the total capacity of the forbidden
edges. In particular the selected family can be all triangles. -/
theorem selected_mass_le_r3_add_card (x : FracPacking G ℚ)
    (B : Finset (Sym2 V)) (hB : ∀ e ∈ B, e ∈ G.edgeFinset)
    (D : Finset (Finset V)) (hD : ∀ K ∈ D, K ∈ items G) :
    ∑ K ∈ D, x.weight K ≤
      (∑ K ∈ D, ((r3 (G := G) B).apply x).weight K) + (B.card : ℚ) := by
  classical
  let y := (r3 (G := G) B).apply x
  have hkeep : ∀ K ∈ D, Disjoint (pairs K) B → x.weight K ≤ y.weight K := by
    intro K hK hclean
    have hself : (r3 (G := G) B).a K K = 1 := by
      simp [r3, ofTarget, r3Target, hclean]
    have h := Finset.single_le_sum
      (f := fun J => x.weight J * (r3 (G := G) B).a J K)
      (fun J _ => mul_nonneg (x.weight_nonneg J) ((r3 (G := G) B).nonneg J K))
      (hD K hK)
    dsimp only at h
    rw [hself, mul_one] at h
    exact h
  have hgood : (∑ K ∈ D.filter (fun K => Disjoint (pairs K) B), x.weight K)
      ≤ ∑ K ∈ D, y.weight K := by
    calc
      _ ≤ ∑ K ∈ D.filter (fun K => Disjoint (pairs K) B), y.weight K :=
        Finset.sum_le_sum (fun K hK => hkeep K (mem_filter.mp hK).1 (mem_filter.mp hK).2)
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
        (fun K _ _ => y.weight_nonneg K)
  have hbad : (∑ K ∈ D.filter (fun K => ¬ Disjoint (pairs K) B), x.weight K)
      ≤ (B.card : ℚ) := by
    apply PaperIV.PatternMass.sum_weight_le_card_of_meets x B hB
    · intro K hK
      exact hD K (mem_filter.mp hK).1
    · intro K hK
      obtain ⟨e, heK, heB⟩ := Finset.not_disjoint_iff.mp (mem_filter.mp hK).2
      exact ⟨e, heB, heK⟩
  have hsplit := Finset.sum_filter_add_sum_filter_not D
    (fun K => Disjoint (pairs K) B) x.weight
  change (∑ K ∈ D, x.weight K) ≤ (∑ K ∈ D, y.weight K) + (B.card : ℚ)
  linarith

/-- R3 can change triangle mass, but its decrease costs at most |B|. -/
theorem triangle_mass_le_r3_add_card (x : FracPacking G ℚ)
    (B : Finset (Sym2 V)) (hB : ∀ e ∈ B, e ∈ G.edgeFinset) :
    PaperIV.LowTriangleReduction.triMass (PaperIV.MixedRoundingAdapter.ofFarFrac x) ≤
      PaperIV.LowTriangleReduction.triMass (PaperIV.MixedRoundingAdapter.ofFarFrac
        ((r3 (G := G) B).apply x)) + (B.card : ℚ) := by
  have h := selected_mass_le_r3_add_card x B hB
    ((items G).filter (fun K => K.card = 3))
    (fun _ hK => (mem_filter.mp hK).1)
  simpa only [PaperIV.LowTriangleReduction.triMass,
    PaperIV.MixedRoundingAdapter.ofFarFrac, PaperIV.MixedRoundingAdapter.items_eq] using h

#print axioms selected_mass_le_r3_add_card
#print axioms triangle_mass_le_r3_add_card

def triangleMassF (x : FracPacking G ℚ) : ℚ :=
  ∑ K ∈ (items G).filter (fun K => K.card = 3), x.weight K

theorem faceTransfer_triangleMass_ge (S : Finset (Finset V))
    (hS : ∀ K ∈ S, K.card = 4) (x : FracPacking G ℚ) :
    triangleMassF x ≤ triangleMassF ((faceTransfer S hS).apply x) := by
  classical
  apply sum_le_sum
  intro K hK
  have hKi := (mem_filter.mp hK).1
  have h3 := (mem_filter.mp hK).2
  have hn : K ∉ S := by intro h; have := hS K h; omega
  have hself : (faceTransfer (G := G) S hS).a K K = 1 := by
    simp [faceTransfer, hn]
  have h := single_le_sum
    (f := fun J => x.weight J * (faceTransfer (G := G) S hS).a J K)
    (fun J _ => mul_nonneg (x.weight_nonneg J) ((faceTransfer S hS).nonneg J K)) hKi
  dsimp only at h
  rw [hself, mul_one] at h
  exact h

theorem dropCopies_triangleMass_loss (x : FracPacking G ℚ) (D : Finset (Finset V))
    (hDi : D ⊆ items G) (hD3 : ∀ K ∈ D, K.card = 3) :
    triangleMassF x - triangleMassF (dropCopies x D) = ∑ K ∈ D, x.weight K := by
  classical
  let T := (items G).filter (fun K => K.card = 3)
  have hf : T.filter (fun K => K ∈ D) = D := by
    ext K
    simp only [mem_filter]
    exact ⟨And.right, fun h => ⟨mem_filter.mpr ⟨hDi h, hD3 K h⟩,h⟩⟩
  have hs := sum_filter_add_sum_filter_not T (fun K => K ∈ D) x.weight
  rw [hf] at hs
  have he : triangleMassF (dropCopies x D) = ∑ K ∈ T.filter (fun K => K ∉ D), x.weight K := by
    simp only [triangleMassF, dropCopies, T, sum_filter]
    apply sum_congr rfl; intro K hK; split_ifs <;> simp_all
  change (∑ K ∈ T, x.weight K) - _ = _
  rw [he]; linarith

theorem profileCleanup_triangleMass_loss {δ : ℚ}
    (R : PaperIV.RegularityFormat.EqualRegularity G δ)
    (x : FracPacking G ℚ) (θ : ℚ) (hθ : 0 ≤ θ) :
    triangleMassF x - triangleMassF (profileCleanup R x θ) ≤
      (E17.FarBudget.N3 R : ℚ) * θ := by
  let z := convertLightFours R x θ
  have hge := faceTransfer_triangleMass_ge (smallFours R x θ)
    (fun _ h => (smallFours_spec R x θ h).2) x
  have hdrop := dropCopies_triangleMass_loss z (smallThrees R z θ)
    (fun _ h => (smallThrees_spec R z θ h).1)
    (fun _ h => (smallThrees_spec R z θ h).2)
  have hb := lightUnion_mass_le (PaperIV.RC01K3Pool.goodK3Slots R) _
    (fibers3_disjoint R) z θ hθ
  change triangleMassF x ≤ triangleMassF z at hge
  change (∑ K ∈ smallThrees R z θ, z.weight K) ≤ _ at hb
  change triangleMassF x - triangleMassF (dropCopies z (smallThrees R z θ)) ≤ _
  change _ ≤ ((PaperIV.RC01K3Pool.goodK3Slots R).card : ℚ) * θ
  linarith

#print axioms profileCleanup_triangleMass_loss
end E17Bridge



/- Source: Bridge/ProfileGate.lean. Research validation bundle. -/

/-! The B7 physical interface on the literal R3/F1/reprofiled packing.
The hypotheses are those of the uniform dense gate, not an assumed realization.
This file does not assert the complementary low-mass schedule. -/
namespace E17Bridge
open Finset PaperIV.RegularityFormat PaperIV.PartitionBridge
  PaperIV.RC01CleanedGate PaperIV.RC01CleanFiber PaperIV.RC01RootwiseReference
  PaperIV.RC01ResidualTransferClosure PaperIV.RC01DenseRootwiseRetention
  PaperIV.RC01MixedPatterns PaperIV.PatternTransfer PaperIV.RC01ResidualCoverage
  PaperIV.DiscardCounts PaperIV.RC01CanonicalTransferBridge

noncomputable def cleanedR3 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {δ : ℚ} (R : EqualRegularity G δ) (x : PaperIV.FarRounding.FracPacking G ℚ)
    (d θ : ℚ) : PaperIV.FarRounding.FracPacking G ℚ :=
  profileCleanup R ((E17.Cleanup.r3 (G := G)
    (discardEdges G R (garbage R) d)).apply x) θ

theorem cleanedR3_value_le_profiles {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] {δ : ℚ} (R : EqualRegularity G δ)
    (x : PaperIV.FarRounding.FracPacking G ℚ) (d θ : ℚ) :
    let y := cleanedR3 R x d θ
    let z := PaperIV.MixedRoundingAdapter.ofFarFrac y
    y.value ≤ ∑ H ∈ denseActiveProfiles R z d θ,
      patternGain H * psiT z (partOf R) H := by
  dsimp only
  let y := cleanedR3 R x d θ
  let z := PaperIV.MixedRoundingAdapter.ofFarFrac y
  have hoff := profileCleanup_offCanonical_zero R
    ((E17.Cleanup.r3 (G := G) (discardEdges G R (garbage R) d)).apply x) d θ
    (fun K _ hw => E17.Cleanup.r3_avoids x _ hw)
  have hr := value_sub_residual_le_transferred R z
    (denseHeavyPatterns R y d θ) (denseHeavyPatterns_subset R y d θ) 0 hoff.le
  rw [sub_zero, PaperIV.MixedRoundingAdapter.value_ofFarFrac] at hr
  rw [sum_denseActiveProfiles_eq R z d θ]
  exact hr

/-- B7 in the dense high-mass regime, with its literal fractional witness and
physical packing both constructed. The profile cost is N4 + 2 N3, not 5|H|. -/
theorem exists_improvedGateGap_of_high_mass (ζ : ℚ) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) :
    ∃ gam : ℝ, 0 < gam ∧ ∃ Cst : ℝ, 0 < Cst ∧ ∃ D : ℝ, 0 < D ∧
      ∀ (n : ℕ) [NeZero n] (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
        {δ d θ u v gamma : ℚ} (R : EqualRegularity G δ)
        (x : PaperIV.FarRounding.FracPacking G ℚ),
        ∀ (hδ : 0 ≤ δ) (hd : 0 ≤ d) (hθ : 0 ≤ θ) (hu : 0 < u) (hv : 0 ≤ v)
        (huv : u + v ≤ 1)
        (hc3 : 0 < d ^ 3 - 3 * δ) (hc4 : 0 < d ^ 6 - 6 * δ)
        (hchoice3 : 33 * δ ≤ v * u ^ 2 * (d ^ 3 - 3 * δ) ^ 3)
        (hchoice4 : 138 * δ ≤ v * u ^ 2 * (d ^ 6 - 6 * δ) ^ 3),
        let z := PaperIV.MixedRoundingAdapter.ofFarFrac (cleanedR3 R x d θ);
        ((denseActiveProfiles R z d θ).card : ℚ) * (d ^ 6 - 6 * δ) +
            ((denseActiveProfiles R z d θ).card : ℚ) * (d ^ 3 - 3 * δ)
          ≤ gamma * (d ^ 3 - 3 * δ) * (d ^ 6 - 6 * δ) * (R.size : ℚ) →
        (gamma : ℝ) ≤ gam →
        12 + 10 * D ≤ (ζ : ℝ) * (n : ℝ) ^ 2 →
        Cst ≤ PaperIV.JointTwoQuotaPhysical.triangleMass
          (cleanedPacking z (partOf R) (denseActiveProfiles R z d θ)
            (rootwiseReference (G := G) (partOf R))
            (profileVolume (G := G) (partOf R)) u hu.le
            (denseActiveProfiles_profileVolume_pos hδ hd hc3 hc4 R z)
            (fun H _ f => rootwiseReference_volume_budget (G := G) (partOf R) H f)) →
        ∃ P : PaperIV.FarRounding.Packing G,
          E17.FarBudget.ImprovedGateGap R x P d θ u v ζ := by
  obtain ⟨gam, hgam, Cst, hCst, D, hD, hgate⟩ :=
    PaperIV.RC01UniformDenseGate.exists_packing_mass_loss_le_denseActive_uniform
      (ζ : ℝ) (by exact_mod_cast hζ) (by exact_mod_cast hζ1)
  refine ⟨gam, hgam, Cst, hCst, D, hD, ?_⟩
  intro n _ G _ δ d θ u v gamma R x hδ hd hθ hu hv huv hc3 hc4 hchoice3 hchoice4
  dsimp only
  intro hthreshold hgamma hsize hmass
  let y := cleanedR3 R x d θ
  let z := PaperIV.MixedRoundingAdapter.ofFarFrac y
  obtain ⟨P, hP⟩ := hgate n G R z hδ hd hu hv hc3 hc4 hchoice3 hchoice4
    hthreshold hgamma hsize hmass
  refine ⟨PaperIV.MixedRoundingAdapter.toFarPacking P, y, ?_, ?_⟩
  · exact profileCleanup_loss R _ θ hθ
  · have hval := cleanedR3_value_le_profiles R x d θ
    have hret := mul_le_mul_of_nonneg_left hval (show 0 ≤ 1 - u - v by linarith)
    have hr : (1 - u - v) * (∑ H ∈ denseActiveProfiles R z d θ,
        patternGain H * psiT z (partOf R) H) - (P.gain : ℚ) ≤ ζ * (n : ℚ)^2 := by
      exact_mod_cast hP
    change (1 - u - v) * y.value - (P.gain : ℚ) ≤ _
    linarith

#print axioms exists_improvedGateGap_of_high_mass
end E17Bridge



/- Source: Bridge/UniformInputs.lean. Research validation bundle. -/

/-! Inputs to the existing uniform schedule, recomputed from the R3/F1 packing.
No conclusion of RC01Final is imported. -/
namespace E17Bridge
open Finset PaperIV.RegularityFormat PaperIV.PartitionBridge
  PaperIV.RC01ResidualTransferClosure PaperIV.RC01ResidualCoverage
  PaperIV.RC01MixedPatterns PaperIV.RC01CanonicalValueAccounting
  PaperIV.RC01CleanedGate PaperIV.PatternTransfer PaperIV.DiscardCounts

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {δ : ℚ}

theorem cleanedR3_loss (R : EqualRegularity G δ)
    (x : PaperIV.FarRounding.FracPacking G ℚ) (d θ : ℚ)
    (hδ : 0 ≤ δ) (hd : 0 ≤ d) (hθ : 0 ≤ θ)
    {k₀ : ℕ} (hk₀ : 0 < k₀) (hk : k₀ ≤ R.parts.card) :
    x.value - (cleanedR3 R x d θ).value ≤
      3 * ((3 * δ + 1 / (k₀ : ℚ) + d) * (n : ℚ)^2) +
      ((E17.FarBudget.N4 R : ℚ) + 2 * E17.FarBudget.N3 R) * θ := by
  have hc := (E17.FarBudget.improved_copy_budget hδ R x d hd hk₀ hk).1
  rw [Fintype.card_fin] at hc
  have hp := profileCleanup_loss R
    ((E17.Cleanup.r3 (G := G) (discardEdges G R (garbage R) d)).apply x) θ hθ
  change _ - (cleanedR3 R x d θ).value ≤ _ at hp
  linarith

theorem cleanedR3_original_value_le_profiles_oldBudget (R : EqualRegularity G δ)
    (x : MixedRounding.FracPacking G) (d θ : ℚ)
    (hδ : 0 ≤ δ) (hd : 0 ≤ d) (hθ : 0 ≤ θ)
    {k₀ : ℕ} (hk₀ : 0 < k₀) (hk : k₀ ≤ R.parts.card) :
    let z := PaperIV.MixedRoundingAdapter.ofFarFrac
      (cleanedR3 R (PaperIV.MixedRoundingAdapter.toFarFrac x) d θ)
    x.value - (5 * ((3 * δ + 1 / (k₀ : ℚ) + d) * (n : ℚ)^2) +
      5 * (((mixedPatterns R).card : ℚ) * θ)) ≤
      ∑ H ∈ denseActiveProfiles R z d θ, patternGain H * psiT z (partOf R) H := by
  have hl := cleanedR3_loss R (PaperIV.MixedRoundingAdapter.toFarFrac x) d θ
    hδ hd hθ hk₀ hk
  have hv := cleanedR3_value_le_profiles R (PaperIV.MixedRoundingAdapter.toFarFrac x) d θ
  have hb := E17.FarBudget.improved_le_old R
    ((3 * δ + 1 / (k₀ : ℚ) + d) * (n : ℚ)^2) θ (by positivity) hθ
  rw [PaperIV.MixedRoundingAdapter.value_toFarFrac] at hl
  dsimp only at hv ⊢
  linarith

theorem triangleMassF_eq (x : PaperIV.FarRounding.FracPacking G ℚ) :
    triangleMassF x = PaperIV.LowTriangleReduction.triMass
      (PaperIV.MixedRoundingAdapter.ofFarFrac x) := by
  simp only [triangleMassF, PaperIV.LowTriangleReduction.triMass,
    PaperIV.MixedRoundingAdapter.ofFarFrac, PaperIV.MixedRoundingAdapter.items_eq]

theorem cleanedR3_original_triangle_le_profiles_oldBudget (R : EqualRegularity G δ)
    (x : MixedRounding.FracPacking G) (d θ : ℚ)
    (hδ : 0 ≤ δ) (hd : 0 ≤ d) (hθ : 0 ≤ θ)
    {k₀ : ℕ} (hk₀ : 0 < k₀) (hk : k₀ ≤ R.parts.card) :
    let z := PaperIV.MixedRoundingAdapter.ofFarFrac
      (cleanedR3 R (PaperIV.MixedRoundingAdapter.toFarFrac x) d θ)
    PaperIV.LowTriangleReduction.triMass x ≤
      (∑ H ∈ (denseActiveProfiles R z d θ).filter (fun H => H.card = 3),
        psiT z (partOf R) H) +
      (5 * ((3 * δ + 1 / (k₀ : ℚ) + d) * (n : ℚ)^2) +
      5 * (((mixedPatterns R).card : ℚ) * θ)) := by
  let xf := PaperIV.MixedRoundingAdapter.toFarFrac x
  let B := discardEdges G R (garbage R) d
  let r := (E17.Cleanup.r3 (G := G) B).apply xf
  let y := cleanedR3 R xf d θ
  let z := PaperIV.MixedRoundingAdapter.ofFarFrac y
  have hr := triangle_mass_le_r3_add_card xf B
    (fun _ he => discardEdges_subset_edgeFinset R (garbage R) d he)
  have hp := profileCleanup_triangleMass_loss R r θ hθ
  rw [triangleMassF_eq, triangleMassF_eq] at hp
  have hz := PaperIV.RC01TriangleTransfer.triMass_le_denseActive_triangles_add_offCanonical
    R z d θ
  have hoff := profileCleanup_offCanonical_zero R r d θ
    (fun K _ hw => E17.Cleanup.r3_avoids xf B hw)
  change offCanonicalValue R y (denseHeavyPatterns R y d θ) = 0 at hoff
  change PaperIV.LowTriangleReduction.triMass z ≤ _ +
    offCanonicalValue R y (denseHeavyPatterns R y d θ) at hz
  rw [hoff, add_zero] at hz
  have hb := E17.FarBudget.card_discardEdges_budget hδ R d hd hk₀ hk
  rw [Fintype.card_fin] at hb
  have ha : 0 ≤ ((3 * δ + 1 / (k₀ : ℚ) + d) * (n : ℚ)^2) := by positivity
  have hn3 : (E17.FarBudget.N3 R : ℚ) ≤ (mixedPatterns R).card := by
    rw [E17.FarBudget.card_mixedPatterns]; push_cast
    exact le_add_of_nonneg_right (Nat.cast_nonneg _)
  have ht := mul_le_mul_of_nonneg_right hn3 hθ
  have ht0 : 0 ≤ ((mixedPatterns R).card : ℚ) * θ := by positivity
  change PaperIV.LowTriangleReduction.triMass x ≤
    PaperIV.LowTriangleReduction.triMass (PaperIV.MixedRoundingAdapter.ofFarFrac r) +
      (B.card : ℚ) at hr
  change PaperIV.LowTriangleReduction.triMass (PaperIV.MixedRoundingAdapter.ofFarFrac r) -
    PaperIV.LowTriangleReduction.triMass z ≤ _ at hp
  dsimp only
  change PaperIV.LowTriangleReduction.triMass x ≤
    (∑ H ∈ (denseActiveProfiles R z d θ).filter (fun H => H.card = 3),
      psiT z (partOf R) H) + _
  change (B.card : ℚ) ≤ _ at hb
  linarith

#print axioms cleanedR3_loss
#print axioms cleanedR3_original_value_le_profiles_oldBudget
#print axioms cleanedR3_original_triangle_le_profiles_oldBudget
end E17Bridge



/- Source: Bridge/UniformRounding.lean. Research validation bundle. -/

/-!
# RC01: the final assembly

This module closes the RC01 route: for every positive rational `ε`, the uniform
rounding target `MixedRounding.UniformRoundingTarget ε` holds.

Nothing new is proved about the geometry or about the nibble.  The module fixes
one rational hierarchy `δ, d, θ, u, v, k₀` from `ε`, one order threshold `N`
large enough for regularity, for the cluster scale, for the additive nibble
constant `12 + 10 D` and for the triangle threshold, and then chains the pieces
that are already available:

* `RegularityFormat.exists_equalRegularity` produces the partition;
* `RC01GlobalSchedule` discharges the codegree and light-profile accounts from
  the polynomial profile cardinality bounds;
* `RC01TriangleTransfer` turns a large triangle mass of the input into a large
  triangle mass of the cleaned packing, which is the last hypothesis of the
  physical gate;
* `RC01UniformDenseGate` runs the gate and `RC01DenseAssembly` charges the whole
  deterministic ledger to `ε n² / 2`;
* `RC01TriangleSchedule` joins that high-mass branch with the low-triangle
  branch of `TriangleSwap`.
-/

namespace E17Bridge.UniformSchedule

open Finset
open MixedRounding
open PaperIV.PatternTransfer
open PaperIV.PartitionBridge
open PaperIV.RegularityFormat
open PaperIV.RC01CleanedGate
open PaperIV.RC01CleanFiber
open PaperIV.RC01RootwiseReference
open PaperIV.RC01ResidualTransferClosure
open PaperIV.RC01DenseRootwiseRetention
open PaperIV.RC01MixedPatterns

/-! ## 1. The one-parameter rational hierarchy -/

/-- The scale parameter of the hierarchy: `d = u = v = s`. -/
theorem exists_scale (ε : ℚ) (hε : 0 < ε) :
    ∃ s : ℚ, 0 < s ∧ s ≤ 1 / 10 ∧ 15 * s ≤ ε / 300 := by
  refine ⟨min (ε / 4500) (1 / 10), ?_, min_le_right _ _, ?_⟩
  · exact lt_min (by linarith) (by norm_num)
  · have h : min (ε / 4500) (1 / 10) ≤ ε / 4500 := min_le_left _ _
    linarith

section Hierarchy

variable {s : ℚ}

/-- The regularity parameter attached to the scale `s`. -/
def deltaOf (s : ℚ) : ℚ := s ^ 21 / 2208

theorem deltaOf_pos (hs : 0 < s) : 0 < deltaOf s := by
  have : 0 < s ^ 21 := pow_pos hs 21
  rw [deltaOf]; positivity

theorem deltaOf_le (hs : 0 < s) (hs1 : s ≤ 1 / 10) : deltaOf s ≤ s := by
  have h1 : s ^ 21 ≤ s ^ 1 := pow_le_pow_of_le_one hs.le (by linarith) (by norm_num)
  rw [deltaOf]
  simp only [pow_one] at h1
  linarith

theorem deltaOf_le_pow3 (hs : 0 < s) (hs1 : s ≤ 1 / 10) :
    deltaOf s ≤ s ^ 3 / 2208 := by
  have h1 : s ^ 21 ≤ s ^ 3 := pow_le_pow_of_le_one hs.le (by linarith) (by norm_num)
  rw [deltaOf]
  linarith

theorem deltaOf_le_pow6 (hs : 0 < s) (hs1 : s ≤ 1 / 10) :
    deltaOf s ≤ s ^ 6 / 2208 := by
  have h1 : s ^ 21 ≤ s ^ 6 := pow_le_pow_of_le_one hs.le (by linarith) (by norm_num)
  rw [deltaOf]
  linarith

theorem deltaOf_le_pow12 (hs : 0 < s) (hs1 : s ≤ 1 / 10) :
    deltaOf s ≤ s ^ 12 / 2208 := by
  have h1 : s ^ 21 ≤ s ^ 12 := pow_le_pow_of_le_one hs.le (by linarith) (by norm_num)
  rw [deltaOf]
  linarith

theorem pow3_half_le (hs : 0 < s) (hs1 : s ≤ 1 / 10) :
    s ^ 3 / 2 ≤ s ^ 3 - 3 * deltaOf s := by
  have h := deltaOf_le_pow3 hs hs1
  have h3 : 0 < s ^ 3 := pow_pos hs 3
  linarith

theorem pow6_half_le (hs : 0 < s) (hs1 : s ≤ 1 / 10) :
    s ^ 6 / 2 ≤ s ^ 6 - 6 * deltaOf s := by
  have h := deltaOf_le_pow6 hs hs1
  have h6 : 0 < s ^ 6 := pow_pos hs 6
  linarith

theorem cube3_pos (hs : 0 < s) (hs1 : s ≤ 1 / 10) : 0 < s ^ 3 - 3 * deltaOf s := by
  have h := pow3_half_le hs hs1
  have h3 : 0 < s ^ 3 := pow_pos hs 3
  linarith

theorem cube4_pos (hs : 0 < s) (hs1 : s ≤ 1 / 10) : 0 < s ^ 6 - 6 * deltaOf s := by
  have h := pow6_half_le hs hs1
  have h6 : 0 < s ^ 6 := pow_pos hs 6
  linarith

theorem choice3 (hs : 0 < s) (hs1 : s ≤ 1 / 10) :
    33 * deltaOf s ≤ s * s ^ 2 * (s ^ 3 - 3 * deltaOf s) ^ 3 := by
  have hcube : (s ^ 3 / 2) ^ 3 ≤ (s ^ 3 - 3 * deltaOf s) ^ 3 := by
    refine pow_le_pow_left₀ ?_ (pow3_half_le hs hs1) 3
    have : 0 < s ^ 3 := pow_pos hs 3
    linarith
  have hs3 : (0 : ℚ) < s ^ 3 := pow_pos hs 3
  have hmul : s ^ 3 * (s ^ 3 / 2) ^ 3 ≤ s ^ 3 * (s ^ 3 - 3 * deltaOf s) ^ 3 :=
    mul_le_mul_of_nonneg_left hcube hs3.le
  have hlhs : 33 * deltaOf s ≤ s ^ 12 / 8 := by
    have h := deltaOf_le_pow12 hs hs1
    have h12 : (0 : ℚ) ≤ s ^ 12 := by positivity
    linarith
  have hchain : s ^ 12 / 8 ≤ s ^ 3 * (s ^ 3 - 3 * deltaOf s) ^ 3 := by
    calc s ^ 12 / 8 = s ^ 3 * (s ^ 3 / 2) ^ 3 := by ring
      _ ≤ s ^ 3 * (s ^ 3 - 3 * deltaOf s) ^ 3 := hmul
  have hid2 : s * s ^ 2 * (s ^ 3 - 3 * deltaOf s) ^ 3
      = s ^ 3 * (s ^ 3 - 3 * deltaOf s) ^ 3 := by ring
  rw [hid2]
  linarith

theorem choice4 (hs : 0 < s) (hs1 : s ≤ 1 / 10) :
    138 * deltaOf s ≤ s * s ^ 2 * (s ^ 6 - 6 * deltaOf s) ^ 3 := by
  have hcube : (s ^ 6 / 2) ^ 3 ≤ (s ^ 6 - 6 * deltaOf s) ^ 3 := by
    refine pow_le_pow_left₀ ?_ (pow6_half_le hs hs1) 3
    have : 0 < s ^ 6 := pow_pos hs 6
    linarith
  have hs3 : (0 : ℚ) < s ^ 3 := pow_pos hs 3
  have hmul : s ^ 3 * (s ^ 6 / 2) ^ 3 ≤ s ^ 3 * (s ^ 6 - 6 * deltaOf s) ^ 3 :=
    mul_le_mul_of_nonneg_left hcube hs3.le
  have hlhs : 138 * deltaOf s ≤ s ^ 21 / 16 := by
    rw [deltaOf]; linarith
  have hchain : s ^ 21 / 8 ≤ s ^ 3 * (s ^ 6 - 6 * deltaOf s) ^ 3 := by
    calc s ^ 21 / 8 = s ^ 3 * (s ^ 6 / 2) ^ 3 := by ring
      _ ≤ s ^ 3 * (s ^ 6 - 6 * deltaOf s) ^ 3 := hmul
  have hid2 : s * s ^ 2 * (s ^ 6 - 6 * deltaOf s) ^ 3
      = s ^ 3 * (s ^ 6 - 6 * deltaOf s) ^ 3 := by ring
  have h21 : (0 : ℚ) < s ^ 21 := pow_pos hs 21
  rw [hid2]
  linarith

/-- The retained triangular mass after the transfer budget. -/
theorem retained_mass_bound {cst Sum tri budget bud : ℚ}
    (hs : 0 < s) (hs1 : s ≤ 1 / 10) (hcst : 0 ≤ cst)
    (htrans : tri ≤ Sum + budget) (hbudget : budget ≤ bud)
    (htri : 2 * cst + bud ≤ tri) :
    cst ≤ (1 - s - s) * Sum := by
  have h1 : 2 * cst ≤ Sum := by linarith
  have h2 : (1 / 2 : ℚ) * (2 * cst) ≤ (1 - s - s) * Sum :=
    mul_le_mul (by linarith) h1 (by linarith) (by linarith)
  linarith

end Hierarchy

/-! ## 2. The final theorem -/

set_option maxHeartbeats 1600000 in
/-- Research replacement using the literal R3/F1 cleanup. The numerical schedule
is copied unchanged from RC01Final; no theorem from that namespace is invoked.
For every positive rational `ε`, every large graph and every
mixed fractional packing have a physical packing that loses at most `ε n²`. -/
theorem uniformRoundingTarget_via_r3_f1 (ε : ℚ) (hε : 0 < ε) :
    MixedRounding.UniformRoundingTarget ε := by
  classical
  obtain ⟨s, hs0, hs1, hsbudget⟩ := exists_scale ε hε
  set δ : ℚ := deltaOf s with hδdef
  have hδ0 : 0 < δ := deltaOf_pos hs0
  have hδs : δ ≤ s := deltaOf_le hs0 hs1
  have hc3 : 0 < s ^ 3 - 3 * δ := cube3_pos hs0 hs1
  have hc4 : 0 < s ^ 6 - 6 * δ := cube4_pos hs0 hs1
  have hchoice3 : 33 * δ ≤ s * s ^ 2 * (s ^ 3 - 3 * δ) ^ 3 := choice3 hs0 hs1
  have hchoice4 : 138 * δ ≤ s * s ^ 2 * (s ^ 6 - 6 * δ) ^ 3 := choice4 hs0 hs1
  -- the gate slack
  set zq : ℚ := min (ε / 10) 1 with hzqdef
  have hzq0 : 0 < zq := lt_min (by linarith) one_pos
  have hzq1 : zq ≤ 1 := min_le_right _ _
  have hzqε : zq ≤ ε / 10 := min_le_left _ _
  have hzqR0 : (0 : ℝ) < ((zq : ℚ) : ℝ) := by exact_mod_cast hzq0
  have hzqR1 : ((zq : ℚ) : ℝ) ≤ 1 := by exact_mod_cast hzq1
  obtain ⟨gam, hgam, Cst, hCst, D, hD, hgate⟩ :=
    PaperIV.RC01UniformDenseGate.exists_packing_mass_loss_le_denseActive_uniform
      ((zq : ℚ) : ℝ) hzqR0 hzqR1
  obtain ⟨gamma, hgamma0, hgammagam⟩ : ∃ q : ℚ, 0 < q ∧ (q : ℝ) ≤ gam := by
    obtain ⟨q, hq0, hqgam⟩ := exists_rat_btwn hgam
    exact ⟨q, by exact_mod_cast hq0, hqgam.le⟩
  set cst : ℚ := (⌈Cst⌉₊ : ℚ) with hcstdef
  have hcstR : Cst ≤ ((cst : ℚ) : ℝ) := by
    rw [hcstdef]; push_cast; exact Nat.le_ceil Cst
  have hcst0 : (0 : ℚ) ≤ cst := by rw [hcstdef]; positivity
  set k₀ : ℕ := ⌈(1500 / ε : ℚ)⌉₊ + 1 with hk₀def
  have hk₀pos : 0 < k₀ := Nat.succ_pos _
  have hk₀Q : (1500 / ε : ℚ) ≤ (k₀ : ℚ) := by
    have h := Nat.le_ceil (1500 / ε : ℚ)
    rw [hk₀def]
    push_cast
    linarith
  have hk₀Qpos : (0 : ℚ) < (k₀ : ℚ) := by exact_mod_cast hk₀pos
  have hk₀ε : 5 / (k₀ : ℚ) ≤ ε / 300 := by
    have h1500 : (1500 : ℚ) ≤ ε * (k₀ : ℚ) := by
      rw [div_le_iff₀ hε] at hk₀Q
      linarith [hk₀Q]
    rw [div_le_iff₀ hk₀Qpos]
    linarith
  obtain ⟨B, hBdef⟩ : ∃ B : ℕ,
      SzemerediRegularity.bound (((δ / 8 : ℚ) : ℝ)) k₀ = B := ⟨_, rfl⟩
  set light : ℚ := ε / 300 with hlightdef
  set a : ℚ := s ^ 3 - 3 * δ with hadef
  set b : ℚ := s ^ 6 - 6 * δ with hbdef
  set scaleBound : ℚ := 4 * (B : ℚ) ^ 5 * (a + b) / (gamma * a * b) with hscaledef
  set massBound : ℚ := 50 * (1 + 2 * cst) / ε with hmassdef
  set N : ℕ :=
    max (max k₀ ⌈(B : ℚ) / δ⌉₊)
      (max ⌈(12 + 10 * D) / ((zq : ℚ) : ℝ)⌉₊ (max ⌈scaleBound⌉₊ ⌈massBound⌉₊)) + 1
    with hNdef
  refine ⟨N, ?_⟩
  intro n hn G _ x
  -- unpacking the threshold
  have hn1 : 1 ≤ n := le_trans (Nat.le_add_left 1 _) hn
  haveI : NeZero n := ⟨by omega⟩
  have hnk₀ : k₀ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _))
    (le_trans (Nat.le_add_right _ 1) hn)
  have hnB : ⌈(B : ℚ) / δ⌉₊ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _))
    (le_trans (Nat.le_add_right _ 1) hn)
  have hnD : ⌈(12 + 10 * D) / ((zq : ℚ) : ℝ)⌉₊ ≤ n :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
      (le_trans (Nat.le_add_right _ 1) hn)
  have hnS : ⌈scaleBound⌉₊ ≤ n :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _))
      (le_trans (Nat.le_add_right _ 1) hn)
  have hnM : ⌈massBound⌉₊ ≤ n :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _))
      (le_trans (Nat.le_add_right _ 1) hn)
  have hnQ : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hn1
  -- the regularity partition
  have hcardfin : Fintype.card (Fin n) = n := Fintype.card_fin n
  have hregn : ((SzemerediRegularity.bound (((δ / 8 : ℚ) : ℝ)) k₀ : ℕ) : ℚ)
      ≤ δ * (Fintype.card (Fin n) : ℚ) := by
    rw [hcardfin, hBdef]
    have h1 : ((B : ℚ) / δ) ≤ (n : ℚ) := by
      refine le_trans (Nat.le_ceil ((B : ℚ) / δ)) ?_
      exact_mod_cast hnB
    rw [div_le_iff₀ hδ0] at h1
    linarith
  obtain ⟨R, hkl, hkL⟩ := PaperIV.RegularityFormat.exists_equalRegularity (G := G)
    hδ0 hk₀pos (by rw [hcardfin]; exact hnk₀) hregn
  rw [hBdef] at hkL
  set k : ℕ := R.parts.card with hkdef
  have hk1 : 1 ≤ k := le_trans hk₀pos hkl
  have hBk : (k : ℚ) ≤ (B : ℚ) := by exact_mod_cast hkL
  have hB1 : (1 : ℚ) ≤ (B : ℚ) := le_trans (by exact_mod_cast hk1) hBk
  set θ : ℚ := light * (n : ℚ) ^ 2 / (10 * (B : ℚ) ^ 4) with hθdef
  have hθ0 : 0 ≤ θ := by
    rw [hθdef]
    have : (0:ℚ) ≤ light * (n:ℚ)^2 := by positivity
    positivity
  -- the size of a cluster
  have hsizeQ : (0 : ℚ) < (R.size : ℚ) := by exact_mod_cast R.size_pos
  have hsizelow : (n : ℚ) / (2 * (B : ℚ)) ≤ (R.size : ℚ) := by
    have hg := R.garbage
    rw [hcardfin] at hg
    rw [← hkdef] at hg
    have hδhalf : δ ≤ 1 / 2 := by linarith
    have hBpos : (0 : ℚ) < 2 * (B : ℚ) := by linarith
    rw [div_le_iff₀ hBpos]
    linarith [mul_le_mul_of_nonneg_left hBk hsizeQ.le, mul_le_mul_of_nonneg_right hδhalf hnQ.le]
  -- the codegree scale inequality
  have hscale : (2 * (k : ℚ) ^ 4) * (a + b) ≤ gamma * a * b * (R.size : ℚ) := by
    have hn' : scaleBound ≤ (n : ℚ) := by
      refine le_trans (Nat.le_ceil scaleBound) ?_
      exact_mod_cast hnS
    have habpos : (0 : ℚ) < gamma * a * b := by positivity
    rw [hscaledef, div_le_iff₀ habpos] at hn'
    have hk4 : (k : ℚ) ^ 4 ≤ (B : ℚ) ^ 4 := pow_le_pow_left₀ (by positivity) hBk 4
    have hBpos : (0 : ℚ) < 2 * (B : ℚ) := by linarith
    have hkey : 2 * (B : ℚ) ^ 4 * (a + b)
        ≤ gamma * a * b * ((n : ℚ) / (2 * (B : ℚ))) := by
      rw [← mul_div_assoc, le_div_iff₀ hBpos]
      have hring : 2 * (B : ℚ) ^ 4 * (a + b) * (2 * (B : ℚ))
          = 4 * (B : ℚ) ^ 5 * (a + b) := by ring
      rw [hring]
      linarith
    have hab0 : (0 : ℚ) ≤ 2 * (a + b) := by linarith
    linarith [mul_le_mul_of_nonneg_right hk4 hab0, mul_le_mul_of_nonneg_left hsizelow habpos.le]
  -- the light-profile account
  have hlightterm : 5 * (((mixedPatterns R).card : ℚ)) * θ ≤ light * (n : ℚ) ^ 2 := by
    refine PaperIV.RC01GlobalSchedule.five_mul_mixedPatterns_theta_le R
      (by exact_mod_cast hk1) hθ0 ?_
    rw [← hkdef, hθdef]
    have hB4 : (0 : ℚ) < 10 * (B : ℚ) ^ 4 := by positivity
    have hk4 : (k : ℚ) ^ 4 ≤ (B : ℚ) ^ 4 := pow_le_pow_left₀ (by positivity) hBk 4
    have hln : (0 : ℚ) ≤ light * (n : ℚ) ^ 2 := by positivity
    rw [← mul_div_assoc, div_le_iff₀ hB4]
    linarith [mul_le_mul_of_nonneg_right hk4 hln]
  -- the additive nibble constant
  have hsizeD : 12 + 10 * D ≤ ((zq : ℚ) : ℝ) * (n : ℝ) ^ 2 := by
    have h1 : (12 + 10 * D) / ((zq : ℚ) : ℝ) ≤ (n : ℝ) := by
      refine le_trans (Nat.le_ceil ((12 + 10 * D) / ((zq : ℚ) : ℝ))) ?_
      exact_mod_cast hnD
    rw [div_le_iff₀ hzqR0] at h1
    linarith [mul_le_mul_of_nonneg_left (le_self_pow₀ (by exact_mod_cast hn1 : (1 : ℝ) ≤ n) two_ne_zero) hzqR0.le]
  -- the triangle threshold
  set C : ℕ := ⌊ε * (n : ℚ) ^ 2 / 30⌋₊ with hCdef
  have hCle : 30 * (C : ℚ) ≤ ε * (n : ℚ) ^ 2 := by
    have h := Nat.floor_le (a := ε * (n : ℚ) ^ 2 / 30) (by positivity)
    rw [hCdef]
    linarith
  have hCge : ε * (n : ℚ) ^ 2 / 30 - 1 ≤ (C : ℚ) := by
    have h := Nat.sub_one_lt_floor (ε * (n : ℚ) ^ 2 / 30)
    rw [hCdef]
    linarith [h.le]
  -- the residual budget of the triangular transfer
  have hΔ : 5 * ((3 * δ + 1 / (k₀ : ℚ) + s) * (n : ℚ) ^ 2)
      + 5 * (((mixedPatterns R).card : ℚ) * θ) ≤ (ε / 75) * (n : ℚ) ^ 2 := by
    have h1 : 5 * (3 * δ + 1 / (k₀ : ℚ) + s) ≤ ε / 100 := by
      have hδterm : 15 * δ ≤ ε / 300 := by linarith
      have hsterm : 5 * s ≤ ε / 300 := by linarith
      have : 5 * (3 * δ + 1 / (k₀ : ℚ) + s) = 15 * δ + 5 / (k₀ : ℚ) + 5 * s := by
        field_simp
        ring
      rw [this]
      linarith
    have h2 : (0 : ℚ) ≤ (n : ℚ) ^ 2 := by positivity
    have h3 := mul_le_mul_of_nonneg_right h1 h2
    have h4 : 5 * (((mixedPatterns R).card : ℚ) * θ) ≤ light * (n : ℚ) ^ 2 := by
      linarith [hlightterm]
    rw [hlightdef] at h4
    linarith
  have hn1Q : (1 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn1
  have hn2 : (n : ℚ) ≤ (n : ℚ) ^ 2 := le_self_pow₀ hn1Q two_ne_zero
  have hbound : 50 * (1 + 2 * cst) ≤ ε * (n : ℚ) ^ 2 := by
    have hmassn : massBound ≤ (n : ℚ) := by
      refine le_trans (Nat.le_ceil massBound) ?_
      exact_mod_cast hnM
    rw [hmassdef, div_le_iff₀ hε] at hmassn
    linarith [mul_le_mul_of_nonneg_left hn2 hε.le]
  -- the six deterministic accounts
  have huv0 : (0 : ℚ) ≤ s + s := by linarith
  have hbud1 : 15 * δ ≤ ε / 100 := by linarith
  have hbud2 : 5 * s ≤ ε / 10 := by linarith
  have hbud3 : (5 / 6 : ℚ) * (s + s) ≤ ε / 10 := by linarith
  have hbud4 : 5 / (k₀ : ℚ) ≤ ε / 10 := by linarith
  have hbud5 : light ≤ ε / 20 := by rw [hlightdef]; linarith
  -- the high-triangle branch
  have hgateT : ∀ z : FracPacking G, ((C : ℕ) : ℝ) ≤
      PaperIV.JointTwoQuotaPhysical.triangleMass z →
      ∃ Pk : Packing G, ((z.value : ℚ) : ℝ) - (Pk.gain : ℝ)
        ≤ (((ε / 2 : ℚ) : ℝ)) * (n : ℝ) ^ 2 := by
    intro original hz
    let z := PaperIV.MixedRoundingAdapter.ofFarFrac
      (E17Bridge.cleanedR3 R (PaperIV.MixedRoundingAdapter.toFarFrac original) s θ)
    have hzQ : (C : ℚ) ≤ PaperIV.LowTriangleReduction.triMass original := by
      have := PaperIV.Corollary73Assembly.triMass_cast original
      rw [← this] at hz
      exact_mod_cast hz
    -- the triangular transfer
    have htrans := E17Bridge.cleanedR3_original_triangle_le_profiles_oldBudget
      R original s θ hδ0.le hs0.le hθ0 hk₀pos hkl
    have htri : 2 * cst + (ε / 75) * (n : ℚ) ^ 2
        ≤ PaperIV.LowTriangleReduction.triMass original := by
      linarith only [hzQ, hCge, hbound]
    have hpsi3 : cst ≤ (1 - s - s) *
        (∑ H ∈ (denseActiveProfiles R z s θ).filter (fun H => H.card = 3),
          psiT z (partOf R) H) :=
      retained_mass_bound hs0 hs1 hcst0 htrans hΔ htri
    -- the geometric data of the gate
    have hvolpos := denseActiveProfiles_profileVolume_pos (θ := θ) hδ0.le hs0.le hc3 hc4 R z
    have hvolb : ∀ H ∈ denseActiveProfiles R z s θ, ∀ f : Sym2 (Fin n),
        rootwiseReference (G := G) (partOf R) H (partsOf (partOf R) f)
            * densT G (partOf R) f
          ≤ profileVolume (G := G) (partOf R) H :=
      fun H _ f => rootwiseReference_volume_budget (G := G) (partOf R) H f
    have hclean := denseActiveProfiles_clean_retention (θ := θ) hδ0.le hs0.le hs0 hs0.le
      hc3 hc4 (by exact hchoice3) (by exact hchoice4) R z
    have hmassclean := PaperIV.CleanedTriangleMass.cleanedPacking_triMass_ge z (partOf R)
      (denseActiveProfiles R z s θ) (rootwiseReference (G := G) (partOf R))
      (profileVolume (G := G) (partOf R)) s hs0.le hvolpos hvolb s hs0.le hclean
    have hmassR : Cst ≤ PaperIV.JointTwoQuotaPhysical.triangleMass
        (cleanedPacking z (partOf R) (denseActiveProfiles R z s θ)
          (rootwiseReference (G := G) (partOf R))
          (profileVolume (G := G) (partOf R)) s hs0.le hvolpos hvolb) := by
      have hQ : cst ≤ PaperIV.LowTriangleReduction.triMass
          (cleanedPacking z (partOf R) (denseActiveProfiles R z s θ)
            (rootwiseReference (G := G) (partOf R))
            (profileVolume (G := G) (partOf R)) s hs0.le hvolpos hvolb) :=
        le_trans hpsi3 hmassclean
      have hcast := PaperIV.Corollary73Assembly.triMass_cast
        (cleanedPacking z (partOf R) (denseActiveProfiles R z s θ)
          (rootwiseReference (G := G) (partOf R))
          (profileVolume (G := G) (partOf R)) s hs0.le hvolpos hvolb)
      rw [← hcast]
      refine le_trans hcstR ?_
      exact_mod_cast hQ
    -- the codegree hypothesis
    have hthreshold := PaperIV.RC01GlobalSchedule.dense_codegree_threshold_of_scale
      (d := s) (θ := θ) (gamma := gamma) R z (by exact_mod_cast hk1) hc3.le hc4.le
      (by exact hscale)
    obtain ⟨Pk, hPk⟩ := hgate n G R z hδ0.le hs0.le hs0 hs0.le hc3 hc4
      (by exact hchoice3) (by exact hchoice4)
      hthreshold hgammagam hsizeD hmassR
    refine ⟨Pk, ?_⟩
    -- the deterministic ledger
    set S : ℚ := ∑ H ∈ denseActiveProfiles R z s θ,
      patternGain H * psiT z (partOf R) H with hSdef
    have hround : (1 - s - s) * S - (Pk.gain : ℚ) ≤ zq * (n : ℚ) ^ 2 := by
      have h1 : ((((1 - s - s) * S - (Pk.gain : ℚ)) : ℚ) : ℝ)
          ≤ (((zq * (n : ℚ) ^ 2 : ℚ)) : ℝ) := by
        push_cast
        push_cast at hPk
        linarith
      exact_mod_cast h1
    have hret := E17Bridge.cleanedR3_original_value_le_profiles_oldBudget
      R original s θ hδ0.le hs0.le hθ0 hk₀pos hkl
    have hfin := PaperIV.RC01DenseAssembly.loss_le_of_retained_round
      huv0 hret (denseProfileValue_le R z s θ) hround
    have hfinal : original.value - (Pk.gain : ℚ) ≤ ε / 2 * (n : ℚ)^2 := by
      have hgatecost := mul_le_mul_of_nonneg_right
        (show zq + (5 / 6 : ℚ) * (s+s) ≤ ε / 5 by linarith) (sq_nonneg (n : ℚ))
      nlinarith only [hfin, hΔ, hgatecost, mul_nonneg hε.le (sq_nonneg (n : ℚ))]
    have hfinalR : ((original.value - (Pk.gain : ℚ) : ℚ) : ℝ)
        ≤ (((ε / 2 * (n : ℚ) ^ 2 : ℚ)) : ℝ) := by
      exact_mod_cast hfinal
    push_cast at hfinalR ⊢
    linarith
  -- joining the two branches
  obtain ⟨P, hP⟩ := PaperIV.RC01TriangleSchedule.lowTriangle_branch_free_scheduled
    (ε := ((ε : ℚ) : ℝ)) (ζ := (((ε / 2 : ℚ) : ℝ))) x C hgateT
    (by push_cast; linarith)
    (by
      have : ((30 * (C : ℚ) : ℚ) : ℝ) ≤ ((ε * (n : ℚ) ^ 2 : ℚ) : ℝ) := by exact_mod_cast hCle
      push_cast at this ⊢
      linarith)
  refine ⟨P, ?_⟩
  have : ((x.value - (P.gain : ℚ) : ℚ) : ℝ) ≤ ((ε * (n : ℚ) ^ 2 : ℚ) : ℝ) := by
    push_cast
    linarith
  exact_mod_cast this

end E17Bridge.UniformSchedule



#print axioms E17Bridge.UniformSchedule.uniformRoundingTarget_via_r3_f1




/- Source: Bridge/ClosedGate.lean. Research validation bundle. -/

/-! Eventual B7, including low triangle mass. This corollary uses the uniform
rounding theorem proved with R3/F1 in this research branch, never RC01Final.
Unlike the same-partition high-mass gate, the uniform rounder may choose its
own additional regularity partition. The fractional witness is still exactly
the literal cleanedR3 packing of the supplied partition. -/
namespace E17Bridge
open Finset PaperIV.RegularityFormat PaperIV.FarRounding
  PaperIV.RC01ResidualCoverage PaperIV.DiscardCounts

/-- Complete eventual discharge of the B7 predicate, for every supplied
regularity partition and every feasible fractional packing. The threshold is
chosen from zeta before the graph, its packing, or its partition. -/
theorem exists_improvedGateGap_eventually (ζ : ℚ) (hζ : 0 < ζ) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      ∀ {δ : ℚ} (R : EqualRegularity G δ) (x : FracPacking G ℚ)
        (d θ u v : ℚ), 0 ≤ θ → 0 ≤ u + v →
      ∃ P : Packing G, E17.FarBudget.ImprovedGateGap R x P d θ u v ζ := by
  obtain ⟨N, hN⟩ := UniformSchedule.uniformRoundingTarget_via_r3_f1 ζ hζ
  refine ⟨N, ?_⟩
  intro n hn G _ δ R x d θ u v hθ huv
  let y := cleanedR3 R x d θ
  obtain ⟨P,hP⟩ := hN n hn G (PaperIV.MixedRoundingAdapter.ofFarFrac y)
  have hy : 0 ≤ y.value := by
    apply sum_nonneg
    intro K hK
    exact mul_nonneg (E17.Cleanup.gainF_nonneg_of_item hK) (y.weight_nonneg K)
  rw [PaperIV.MixedRoundingAdapter.value_ofFarFrac] at hP
  refine ⟨PaperIV.MixedRoundingAdapter.toFarPacking P, y,
    profileCleanup_loss R _ θ hθ, ?_⟩
  change (1-u-v) * y.value - (P.gain : ℚ) ≤ ζ * (n : ℚ)^2
  nlinarith [mul_nonneg huv hy]

/-- The advertised complete B7 loss, now with existence of a physical packing
instead of ImprovedGateGap as an unresolved hypothesis. -/
theorem improved_far_loss_eventually (ζ : ℚ) (hζ : 0 < ζ) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      ∀ {δ : ℚ} (hδ : 0 ≤ δ) (R : EqualRegularity G δ) (x : FracPacking G ℚ)
        (d θ u v : ℚ), 0 ≤ d → 0 ≤ θ → 0 ≤ u+v →
      ∀ k₀ : ℕ, 0 < k₀ → k₀ ≤ R.parts.card →
      ∃ P : Packing G, x.value - (P.gain : ℚ) ≤
        3 * ((3*δ + 1/(k₀ : ℚ) + d) * (n : ℚ)^2) +
        ((E17.FarBudget.N4 R : ℚ) + 2*E17.FarBudget.N3 R) * θ +
        (ζ + (5/6 : ℚ)*(u+v)) * (n : ℚ)^2 := by
  obtain ⟨N,hN⟩ := exists_improvedGateGap_eventually ζ hζ
  refine ⟨N, ?_⟩
  intro n hn G _ δ hδ R x d θ u v hd hθ huv k₀ hk₀ hk
  obtain ⟨P,hP⟩ := hN n hn G R x d θ u v hθ huv
  exact ⟨P, E17.FarBudget.improved_far_loss hδ R x P d θ u v ζ hd hk₀ hk huv hP⟩

#print axioms exists_improvedGateGap_eventually
#print axioms improved_far_loss_eventually
end E17Bridge
