import PaperIV.RC01DenseRootwiseRetention
import PaperIV.RC01CleanedGate

/-!
# RC01: the cleaned physical gate on the literal dense active family

This module removes the remaining local geometric hypotheses from
`RC01CleanedGate`: positive reference volume, the volume budget, the K3/K4
volume scales, and simultaneous rootwise retention are all derived for the
canonical dense family.  Only global cardinal/codegree and large-`n` budgets
remain explicit.
-/

namespace PaperIV.RC01DensePhysicalGate

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

/-- High-triangle physical gate specialized to the actual dense active
profiles and to the exact rootwise reference. -/
theorem exists_packing_mass_loss_le_denseActive
    {n : ℕ} [NeZero n] (Gn : SimpleGraph (Fin n)) [DecidableRel Gn.Adj]
    (zeta : ℝ) (hzeta : 0 < zeta) (hzeta1 : zeta ≤ 1) :
    ∃ gam : ℝ, 0 < gam ∧ ∃ Cst : ℝ, 0 < Cst ∧ ∃ D : ℝ, 0 < D ∧
      ∀ {δ d θ u v gamma : ℚ} (R : EqualRegularity Gn δ) (x : FracPacking Gn),
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
  obtain ⟨gam, hgam, Cst, hCst, D, hD, hgate⟩ :=
    exists_packing_mass_loss_le_of_cleanedSpread_physicalScale_of_clean
      (P := Option (Finset (Fin n))) zeta hzeta hzeta1
  refine ⟨gam, hgam, Cst, hCst, D, hD, ?_⟩
  intro δ d θ u v gamma R x hδ hd hu hv hc3 hc4 hchoice3 hchoice4
    hthreshold hgamma hsize hmass
  let Pats := denseActiveProfiles R x d θ
  let A := rootwiseReference (G := Gn) (partOf R)
  let vol := profileVolume (G := Gn) (partOf R)
  have hvolpos : ∀ H ∈ Pats, 0 < vol H := by
    simpa [Pats, vol] using denseActiveProfiles_profileVolume_pos hδ hd hc3 hc4 R x
  have hvol : ∀ H ∈ Pats, ∀ f : Sym2 (Fin n),
      A H (partsOf (partOf R) f) * densT Gn (partOf R) f
        ≤ vol H := by
    intro H _ f
    simpa [A, vol] using rootwiseReference_volume_budget (G := Gn) (partOf R) H f
  have hlower := denseActiveProfiles_profileVolume_lower (θ := θ) hδ hd R x
  have hb3 : ∀ H ∈ Pats, H.card = 3 →
      (d ^ 3 - 3 * δ) * (R.size : ℚ) ^ 2 * (R.size : ℚ) ≤ (1 + u) * vol H := by
    intro H hH hH3
    rcases hlower H (by simpa [Pats] using hH) with h3 | h4
    · have hbase : (d ^ 3 - 3 * δ) * (R.size : ℚ) ^ 2 * (R.size : ℚ) ≤ vol H := by
        nlinarith [h3.2]
      have hnonneg : 0 ≤ vol H := le_of_lt (hvolpos H hH)
      nlinarith
    · omega
  have hb4 : ∀ H ∈ Pats, H.card = 4 →
      (d ^ 6 - 6 * δ) * (R.size : ℚ) ^ 2 * (R.size : ℚ) ^ 2 ≤ (1 + u) * vol H := by
    intro H hH hH4
    rcases hlower H (by simpa [Pats] using hH) with h3 | h4
    · omega
    · have hbase : (d ^ 6 - 6 * δ) * (R.size : ℚ) ^ 2 * (R.size : ℚ) ^ 2 ≤ vol H := by
        nlinarith [h4.2]
      have hnonneg : 0 ≤ vol H := le_of_lt (hvolpos H hH)
      nlinarith
  have hclean : ∀ H ∈ Pats,
      (1 - v) * vol H ≤ ((cleanFiber Gn (partOf R) A u H).card : ℚ) := by
    simpa [Pats, A, vol] using
      denseActiveProfiles_clean_retention hδ hd hu hv
        hc3 hc4 hchoice3 hchoice4 R x
  have hk3 : (((Pats.filter (fun H => H.card = 3)).card : ℕ) : ℚ) ≤ (Pats.card : ℚ) := by
    exact_mod_cast Finset.card_filter_le (s := Pats) (p := fun H => H.card = 3)
  have hk4 : (((Pats.filter (fun H => ¬ H.card = 3)).card : ℕ) : ℚ) ≤ (Pats.card : ℚ) := by
    exact_mod_cast Finset.card_filter_le (s := Pats) (p := fun H => ¬ H.card = 3)
  exact hgate n Gn x (partOf R) Pats A vol u hu.le hvolpos hvol R.size
    ((Pats.card : ℚ)) ((Pats.card : ℚ)) (d ^ 3 - 3 * δ) (d ^ 6 - 6 * δ)
    gamma v R.size_pos hc3 hc4 hv
    (by intro H hH; exact denseActiveProfiles_card R x d θ (by simpa [Pats] using hH))
    (by simpa [Pats] using denseActiveProfiles_class_card_le R x d θ)
    hk3 hk4 hb3 hb4
    (by simpa [Pats] using hthreshold)
    (by intro H hH; rfl) hclean hgamma hsize (by simpa [Pats, A, vol] using hmass)

end PaperIV.RC01DensePhysicalGate
