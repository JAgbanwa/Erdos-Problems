import PaperIV.RC01FarAssembly
import PaperIV.CertifiedOptimumExistence
import PaperIV.CertifiedF4Bridge

/-!
# The far-regime corollary for all graphs

This is Corollary 3.5 in the manuscript, with no chordality or supplied
optimum certificate in the statement. The rational certificate is constructed
inside the proof from finite LP duality.
-/

namespace PaperIV.FarRegimeAllGraphs

open PaperIV.FarRounding

/-- Every sufficiently large graph with a fixed quadratic margin below the
mixed fractional threshold admits a physical clique partition at the sharp
target. This conclusion does not require chordality. -/
theorem farRegime_cliquePartition_allGraphs (η : ℚ) (hη : 0 < η) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      PaperIV.VertexCopyGate.F4' G < (n : ℝ) ^ 2 / 6 - (η : ℝ) * (n : ℝ) ^ 2 →
        ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size ≤ targetSize n := by
  obtain ⟨N, hN⟩ :=
    PaperIV.RC01FarAssembly.farRegime_cliquePartition_allGraphs η hη
  refine ⟨N, ?_⟩
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
  exact hN n hn G w hw hfarQ

end PaperIV.FarRegimeAllGraphs
