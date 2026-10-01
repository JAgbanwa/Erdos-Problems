import E17.ExplicitFarRounding
import E19.Main

/-! Explicit B7 budgets and their transfer to the all-graphs far branch.
E18/E19 supply numerical constants only; the physical rounder is R3/F1. -/

namespace E17Bridge
open Finset PaperIV.RegularityFormat PaperIV.FarRounding
  PaperIV.RC01ResidualCoverage PaperIV.DiscardCounts

theorem exists_improvedGateGap_explicit (ζ : ℚ) (hζ : 0 < ζ) :
    ∀ n ≥ E18.NE ζ, ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      ∀ {δ : ℚ} (R : EqualRegularity G δ) (x : FracPacking G ℚ)
        (d θ u v : ℚ), 0 ≤ θ → 0 ≤ u + v →
      ∃ P : Packing G, E17.FarBudget.ImprovedGateGap R x P d θ u v ζ := by
  intro n hn G _ δ R x d θ u v hθ huv
  let y := cleanedR3 R x d θ
  obtain ⟨P,hP⟩ := ExplicitSchedule.uniformRoundingTarget_explicit ζ hζ n hn G
    (PaperIV.MixedRoundingAdapter.ofFarFrac y)
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
theorem improved_far_loss_explicit (ζ : ℚ) (hζ : 0 < ζ) :
    ∀ n ≥ E18.NE ζ, ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      ∀ {δ : ℚ} (hδ : 0 ≤ δ) (R : EqualRegularity G δ) (x : FracPacking G ℚ)
        (d θ u v : ℚ), 0 ≤ d → 0 ≤ θ → 0 ≤ u+v →
      ∀ k₀ : ℕ, 0 < k₀ → k₀ ≤ R.parts.card →
      ∃ P : Packing G, x.value - (P.gain : ℚ) ≤
        3 * ((3*δ + 1/(k₀ : ℚ) + d) * (n : ℚ)^2) +
        ((E17.FarBudget.N4 R : ℚ) + 2*E17.FarBudget.N3 R) * θ +
        (ζ + (5/6 : ℚ)*(u+v)) * (n : ℚ)^2 := by
  intro n hn G _ δ hδ R x d θ u v hd hθ huv k₀ hk₀ hk
  obtain ⟨P,hP⟩ := exists_improvedGateGap_explicit ζ hζ n hn G R x d θ u v hθ huv
  exact ⟨P, E17.FarBudget.improved_far_loss hδ R x P d θ u v ζ hd hk₀ hk huv hP⟩


namespace ExplicitAssembly
open E18
open PaperIV.MixedRoundingAdapter

theorem uniformTransferAt_explicit (ζ : ℚ) (hζ : 0 < ζ) :
    ∀ n : ℕ, NE ζ ≤ n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (w : ℚ),
      CertifiedFractionalOptimum G w → ∃ P : Packing G, w - (P.gain : ℚ) ≤ ζ * (n : ℚ) ^ 2 := by
  intro n hn G _ w hw
  obtain ⟨x, -, hx, -⟩ := id hw
  obtain ⟨P, hP⟩ := ExplicitSchedule.uniformRoundingTarget_explicit ζ hζ n hn G (ofFarFrac x)
  refine ⟨toFarPacking P, ?_⟩
  rw [gain_toFarPacking, ← hx, ← value_ofFarFrac x]
  exact hP

/-- `UniformTransferAt ζ` with the explicit witness `NE ζ`. -/
theorem uniformTransferAt_of_explicit (ζ : ℚ) (hζ : 0 < ζ) : UniformTransferAt ζ :=
  ⟨NE ζ, uniformTransferAt_explicit ζ hζ⟩


/-- **A3: Corollary 3.5 with an explicit threshold.**  Every graph of order
`n ≥ NfarE η` with `F4'(G) < n²/6 − η n²` has a clique partition into cliques of order
at most `4` of size at most `targetSize n = ⌊n(n+1)/6⌋`.  Adapted from
`PaperIV.FarRegimeAllGraphs.farRegime_cliquePartition_allGraphs` and
`PaperIV.RC01FarAssembly.farRegime_cliquePartition_allGraphs`. -/
theorem farRegime_allGraphs_explicit (η : ℚ) (hη : 0 < η) :
    ∀ n : ℕ, NfarE η ≤ n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      PaperIV.VertexCopyGate.F4' G < (n : ℝ) ^ 2 / 6 - (η : ℝ) * (n : ℝ) ^ 2 →
        ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size ≤ targetSize n := by
  intro n hn G _ hfar
  obtain ⟨w, hw⟩ :=
    PaperIV.CertifiedOptimumExistence.exists_certifiedFractionalOptimum G
  rw [PaperIV.CertifiedF4Bridge.F4'_eq_edge_sub_certified hw] at hfar
  have hfarQ :
      (G.edgeFinset.card : ℚ) - w < (n : ℚ) ^ 2 / 6 - η * (n : ℚ) ^ 2 := by
    have hfarR :
        (((G.edgeFinset.card : ℚ) - w : ℚ) : ℝ) <
          (((n : ℚ) ^ 2 / 6 - η * (n : ℚ) ^ 2 : ℚ) : ℝ) := by
      push_cast
      simpa only [Rat.cast_sub] using hfar
    exact_mod_cast hfarR
  obtain ⟨P, hP⟩ := uniformTransferAt_explicit (η / 2) (by positivity) n hn G w hw
  obtain ⟨Q, hQ4, hQsize⟩ := exists_cliquePartition_of_packing P
  refine ⟨Q, hQ4, ?_⟩
  have hsize : (Q.size : ℚ) + (P.gain : ℚ) = (G.edgeFinset.card : ℚ) := by
    exact_mod_cast hQsize
  have hlt : (Q.size : ℚ) < (n : ℚ) ^ 2 / 6 - η * (n : ℚ) ^ 2 / 2 := by
    linarith
  have hn0 : (0 : ℚ) ≤ (n : ℚ) := Nat.cast_nonneg n
  have hn2 : (n : ℚ) ^ 2 ≤ (n : ℚ) * ((n : ℚ) + 1) := by nlinarith
  have hηn : 0 ≤ η * (n : ℚ) ^ 2 / 2 := by positivity
  have h6 : 6 * Q.size ≤ n * (n + 1) := by
    have hcast : ((6 * Q.size : ℕ) : ℚ) ≤ ((n * (n + 1) : ℕ) : ℚ) := by
      push_cast
      linarith
    exact_mod_cast hcast
  rw [targetSize, Nat.le_div_iff_mul_le (by norm_num)]
  omega



/-- The E19 numerical bound now applies to the R3/F1 far construction. -/
theorem farRegime_eta0_tower :
    ∀ n : ℕ, E19.tower2 (E18.Numeric.hIter + 7) ≤ n →
      ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      PaperIV.VertexCopyGate.F4' G < (n : ℝ)^2 / 6 -
        ((E18.Numeric.eta0 : ℚ) : ℝ) * (n : ℝ)^2 →
      ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size ≤ targetSize n := by
  intro n hn G _ hfar
  exact farRegime_allGraphs_explicit E18.Numeric.eta0
    (by norm_num [E18.Numeric.eta0]) n
    (E19.NfarE_eta0_le_tower.trans hn) G hfar

end ExplicitAssembly
end E17Bridge

