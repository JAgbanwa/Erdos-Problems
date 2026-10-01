import PaperIV.RC01DensePhysicalGate

/-!
# RC01: the dense physical gate with constants uniform in `n`

`PaperIV.RC01DensePhysicalGate.exists_packing_mass_loss_le_denseActive` produces
the three physical constants `gam, Cst, D` *after* fixing the order `n`, because
the reduced colour type `Option (Finset (Fin n))` of the cleaned gate depends on
`n`.  The final RC01 assembly has to choose one threshold `N` from those
constants, so it needs them **before** `n`.

Nothing new is proved here.  The statement below is the literal statement of
`exists_packing_mass_loss_le_denseActive` with the existential block moved in
front of `n`, and the proof is the same chain, taken from the one place where it
is already uniform in `n` *and* free of the reduced colour type, namely
`PaperIV.RC01MarkedRounding.exists_packing_loss_le_of_slackMarkedQuota`.  The
three intermediate steps of `RC01CleanedGate` (served patterns, joint codegree,
retained value) are applied pointwise, exactly as in that module.
-/

namespace PaperIV.RC01UniformDenseGate

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

/-- The high-triangle physical gate on the literal dense active profiles, with
the three physical constants chosen once and for all, uniformly in `n`. -/
theorem exists_packing_mass_loss_le_denseActive_uniform
    (zeta : ℝ) (hzeta : 0 < zeta) (hzeta1 : zeta ≤ 1) :
    ∃ gam : ℝ, 0 < gam ∧ ∃ Cst : ℝ, 0 < Cst ∧ ∃ D : ℝ, 0 < D ∧
      ∀ (n : ℕ) [NeZero n] (Gn : SimpleGraph (Fin n)) [DecidableRel Gn.Adj]
        {δ d θ u v gamma : ℚ} (R : EqualRegularity Gn δ) (x : FracPacking Gn),
        ∀ (hδ : 0 ≤ δ) (hd : 0 ≤ d) (hu : 0 < u) (hv : 0 ≤ v)
        (hc3 : 0 < d ^ 3 - 3 * δ) (hc4 : 0 < d ^ 6 - 6 * δ)
        (hchoice3 : 33 * δ ≤ v * u ^ 2 * (d ^ 3 - 3 * δ) ^ 3)
        (hchoice4 : 138 * δ ≤ v * u ^ 2 * (d ^ 6 - 6 * δ) ^ 3),
        ((denseActiveProfiles R x d θ).card : ℚ) * (d ^ 6 - 6 * δ) +
            ((denseActiveProfiles R x d θ).card : ℚ) * (d ^ 3 - 3 * δ)
          ≤ gamma * (d ^ 3 - 3 * δ) * (d ^ 6 - 6 * δ) * (R.size : ℚ) →
        (gamma : ℝ) ≤ gam →
        12 + 10 * D ≤ zeta * (n : ℝ) ^ 2 →
        Cst ≤ PaperIV.JointTwoQuotaPhysical.triangleMass
          (cleanedPacking x (partOf R) (denseActiveProfiles R x d θ)
            (rootwiseReference (G := Gn) (partOf R))
            (profileVolume (G := Gn) (partOf R)) u hu.le
            (denseActiveProfiles_profileVolume_pos hδ hd hc3 hc4 R x)
            (fun H _ f => rootwiseReference_volume_budget (G := Gn) (partOf R) H f)) →
        ∃ Pk : Packing Gn,
          (((1 - u - v) *
              (∑ H ∈ denseActiveProfiles R x d θ,
                patternGain H * PaperIV.PatternTransfer.psiT x (partOf R) H) : ℚ) : ℝ)
            - (Pk.gain : ℝ) ≤ zeta * (n : ℝ) ^ 2 := by
  obtain ⟨gam, hgam, Cst, hCst, D, hD, hslack⟩ :=
    PaperIV.RC01MarkedRounding.exists_packing_loss_le_of_slackMarkedQuota zeta
      hzeta hzeta1
  refine ⟨gam, hgam, Cst, hCst, D, hD, ?_⟩
  intro n _ Gn _ δ d θ u v gamma R x hδ hd hu hv hc3 hc4 hchoice3 hchoice4
    hthreshold hgamma hsize hmass
  classical
  set Pats := denseActiveProfiles R x d θ with hPats
  set A := rootwiseReference (G := Gn) (partOf R) with hA
  set vol := profileVolume (G := Gn) (partOf R) with hvolDef
  have hvolpos : ∀ H ∈ Pats, 0 < vol H :=
    denseActiveProfiles_profileVolume_pos hδ hd hc3 hc4 R x
  have hvol : ∀ H ∈ Pats, ∀ f : Sym2 (Fin n),
      A H (partsOf (partOf R) f) * densT Gn (partOf R) f ≤ vol H :=
    fun H _ f => rootwiseReference_volume_budget (G := Gn) (partOf R) H f
  -- the geometric data of the dense family, exactly as in `RC01DensePhysicalGate`
  have hcard : ∀ H ∈ Pats, H.card = 3 ∨ H.card = 4 := fun H hH =>
    denseActiveProfiles_card R x d θ hH
  have hpart : ∀ H ∈ Pats, ∀ p ∈ H,
      (univ.filter (fun w => partOf R w = p)).card ≤ R.size :=
    denseActiveProfiles_class_card_le R x d θ
  have hlower := denseActiveProfiles_profileVolume_lower (θ := θ) hδ hd R x
  have hb3 : ∀ H ∈ Pats, H.card = 3 →
      (d ^ 3 - 3 * δ) * (R.size : ℚ) ^ 2 * (R.size : ℚ) ≤ (1 + u) * vol H := by
    intro H hH hH3
    rcases hlower H hH with h3 | h4
    · have hbase : (d ^ 3 - 3 * δ) * (R.size : ℚ) ^ 2 * (R.size : ℚ) ≤ vol H := by
        nlinarith [h3.2]
      have hnonneg : 0 ≤ vol H := le_of_lt (hvolpos H hH)
      nlinarith
    · omega
  have hb4 : ∀ H ∈ Pats, H.card = 4 →
      (d ^ 6 - 6 * δ) * (R.size : ℚ) ^ 2 * (R.size : ℚ) ^ 2 ≤ (1 + u) * vol H := by
    intro H hH hH4
    rcases hlower H hH with h3 | h4
    · omega
    · have hbase : (d ^ 6 - 6 * δ) * (R.size : ℚ) ^ 2 * (R.size : ℚ) ^ 2 ≤ vol H := by
        nlinarith [h4.2]
      have hnonneg : 0 ≤ vol H := le_of_lt (hvolpos H hH)
      nlinarith
  have hclean : ∀ H ∈ Pats,
      (1 - v) * vol H ≤ ((cleanFiber Gn (partOf R) A u H).card : ℚ) :=
    denseActiveProfiles_clean_retention hδ hd hu hv hc3 hc4 hchoice3 hchoice4 R x
  have hk3 : (((Pats.filter (fun H => H.card = 3)).card : ℕ) : ℚ) ≤ (Pats.card : ℚ) := by
    exact_mod_cast Finset.card_filter_le (s := Pats) (p := fun H => H.card = 3)
  have hk4 : (((Pats.filter (fun H => ¬ H.card = 3)).card : ℕ) : ℚ) ≤ (Pats.card : ℚ) := by
    exact_mod_cast Finset.card_filter_le (s := Pats) (p := fun H => ¬ H.card = 3)
  have href : ∀ H ∈ Pats, vol H ≤ ((profileFiber Gn (partOf R) H).card : ℚ) :=
    fun H _ => le_of_eq rfl
  -- every retained pattern serves at least one real pair
  have hserved : ∀ H ∈ Pats, ∃ e : Sym2 (Fin n), H ∈ servingT (partOf R) e := by
    intro H hH
    have hposQ : (0 : ℚ) < ((profileFiber Gn (partOf R) H).card : ℚ) :=
      lt_of_lt_of_le (hvolpos H hH) (href H hH)
    have hpos : 0 < (profileFiber Gn (partOf R) H).card := by exact_mod_cast hposQ
    obtain ⟨K, hK⟩ := Finset.card_pos.1 hpos
    have hitem : IsItem Gn K := mem_items.1 (mem_profileFiber.1 hK).1
    have hpairs : (pairs K).Nonempty := by
      rw [← Finset.card_pos, card_pairs]
      rcases hitem.2 with h3 | h4
      · simp [h3]
      · rw [h4]
        decide
    obtain ⟨e, he⟩ := hpairs
    exact ⟨e, serving_of_mem_profileFiber hK he⟩
  have ht : 1 ≤ R.size := R.size_pos
  have hthreshold' :
      (Pats.card : ℚ) * (d ^ 6 - 6 * δ) + (Pats.card : ℚ) * (d ^ 3 - 3 * δ)
        ≤ gamma * (d ^ 3 - 3 * δ) * (d ^ 6 - 6 * δ) * (R.size : ℚ) := hthreshold
  -- (C.1) the joint codegree of the cleaned packing
  have hcodeg := cleanedPacking_joint_codegree_le_of_served_patterns x (partOf R)
    Pats A vol u hu.le hvolpos hvol R.size (Pats.card : ℚ) (Pats.card : ℚ)
    (d ^ 3 - 3 * δ) (d ^ 6 - 6 * δ) gamma ht hc3 hc4 hserved hcard hpart hk3 hk4
    hb3 hb4 (by linarith [hthreshold'])
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.2 (NeZero.ne n)
  obtain ⟨Pk, hPk⟩ := hslack n hn1 Gn
    (cleanedPacking x (partOf R) Pats A vol u hu.le hvolpos hvol) hsize
    (fun e f hef => le_trans (hcodeg e f hef) hgamma) hmass
  refine ⟨Pk, ?_⟩
  -- (C.2) the cleaned packing retains the transferred objective
  have hvalue := cleanedPacking_value_ge x (partOf R) Pats A vol u hu.le hvolpos
    hvol v hv hcard hclean
  have hcast :
      (((1 - u - v) * (∑ H ∈ Pats, patternGain H * psiT x (partOf R) H) : ℚ) : ℝ)
        ≤ (((cleanedPacking x (partOf R) Pats A vol u hu.le hvolpos hvol).value : ℚ) : ℝ) := by
    exact_mod_cast hvalue
  linarith

end PaperIV.RC01UniformDenseGate

