import E18.Rounding
import PaperIV.FarRegimeAllGraphs

/-!
# E18 — the far branch (Corollary 3.5) with an explicit threshold (A3)

`PaperIV.FarRegimeAllGraphs.farRegime_cliquePartition_allGraphs η` only states `∃ N`.
Its proof goes through `uniformTransferAt (η/2)`, i.e. through RC01 at `ε = η/2`, and does
not change the threshold.  With the explicit RC01 threshold `E18.NE` this gives the explicit
far threshold `NfarE η = NE (η/2)`.
-/

namespace E18

open PaperIV.FarRounding
open PaperIV.MixedRoundingAdapter

/-- RC01 transported to the `FarRounding` model, with explicit threshold `NE ζ`
(adapted from `PaperIV.RC01FarAssembly.uniformRoundingAt` and
`PaperIV.NB08Interface.uniformTransferAt_of_uniformRoundingAt`). -/
theorem uniformTransferAt_explicit (ζ : ℚ) (hζ : 0 < ζ) :
    ∀ n : ℕ, NE ζ ≤ n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (w : ℚ),
      CertifiedFractionalOptimum G w → ∃ P : Packing G, w - (P.gain : ℚ) ≤ ζ * (n : ℚ) ^ 2 := by
  intro n hn G _ w hw
  obtain ⟨x, -, hx, -⟩ := id hw
  obtain ⟨P, hP⟩ := rc01_uniformRoundingTarget_explicit ζ hζ n hn G (ofFarFrac x)
  refine ⟨toFarPacking P, ?_⟩
  rw [gain_toFarPacking, ← hx, ← value_ofFarFrac x]
  exact hP

/-- `UniformTransferAt ζ` with the explicit witness `NE ζ`. -/
theorem uniformTransferAt_of_explicit (ζ : ℚ) (hζ : 0 < ζ) : UniformTransferAt ζ :=
  ⟨NE ζ, uniformTransferAt_explicit ζ hζ⟩

/-- **The explicit far threshold** `NfarE η = NE (η/2)`. -/
noncomputable def NfarE (η : ℚ) : ℕ := NE (η / 2)

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

end E18
