import E32.Basic
import PaperIV.FarRegimeAllGraphs
import PaperIV.FarSlackQuantitative

/-!
# E32 — the far branch keeps its margin, for all graphs (step 1)

`PaperIV.FarRegimeAllGraphs.farRegime_cliquePartition_allGraphs` concludes `Q.size ≤ M(n)`,
which does not contradict `c₄(G) ≥ Q_s(n) − δ`. As `PaperIV.FarSlackQuantitative` does for chordal
graphs, we reassemble the far branch *without* the final rounding, now for **all** graphs: the
partition satisfies `Q.size < n²/6 − η n²/2`. Consequently a graph with rooted defect `s`, order
`n ≥ N`, and `c₄(G) ≥ Q_s(n) − δ` with `δ ≤ (η/4) n²` is never in the far branch.
-/

namespace E32

open PaperIV.FarRounding PaperIV.RootedSimplicialDefect PaperIV.DefectTargetArithmetic

/-- The far branch with margin, for every graph. -/
theorem farRegime_slack_allGraphs (η : ℚ) (hη : 0 < η) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      PaperIV.VertexCopyGate.F4' G < (n : ℝ) ^ 2 / 6 - (η : ℝ) * (n : ℝ) ^ 2 →
        ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧
          (Q.size : ℚ) < (n : ℚ) ^ 2 / 6 - η * (n : ℚ) ^ 2 / 2 := by
  obtain ⟨N, hN⟩ := PaperIV.RC01FarAssembly.uniformTransferAt (η / 2) (by positivity)
  refine ⟨N, ?_⟩
  intro n hn G _ hfar
  obtain ⟨w, hw⟩ := PaperIV.CertifiedOptimumExistence.exists_certifiedFractionalOptimum G
  rw [PaperIV.CertifiedF4Bridge.F4'_eq_edge_sub_certified hw] at hfar
  have hfarQ :
      (G.edgeFinset.card : ℚ) - w < (n : ℚ) ^ 2 / 6 - η * (n : ℚ) ^ 2 := by
    have hfarR :
        (((G.edgeFinset.card : ℚ) - w : ℚ) : ℝ) <
          (((n : ℚ) ^ 2 / 6 - η * (n : ℚ) ^ 2 : ℚ) : ℝ) := by
      push_cast
      simpa only [Rat.cast_sub] using hfar
    exact_mod_cast hfarR
  obtain ⟨P, hP⟩ := hN n hn G w hw
  obtain ⟨Q, hQ4, hQsize⟩ := exists_cliquePartition_of_packing P
  refine ⟨Q, hQ4, ?_⟩
  have hsize : (Q.size : ℚ) + (P.gain : ℚ) = (G.edgeFinset.card : ℚ) := by
    exact_mod_cast hQsize
  linarith

/-- **Far exclusion.** With `γ ≤ η/4`, a deficit `δ ≤ γ n²` forces the near branch
`F4'(G) ≥ n²/6 − η n²`. -/
theorem near_of_small_deficit (s : ℕ) (η : ℚ) (hη : 0 < η) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      ∀ δ : ℚ, δ ≤ η / 4 * (n : ℚ) ^ 2 →
      (∀ Q : CliquePartition G, Q.OrderAtMost 4 → (defectTarget s n : ℚ) - δ ≤ Q.size) →
        (n : ℝ) ^ 2 / 6 - (η : ℝ) * (n : ℝ) ^ 2 ≤ PaperIV.VertexCopyGate.F4' G := by
  obtain ⟨Nf, hNf⟩ := farRegime_slack_allGraphs η hη
  refine ⟨Nf + s + 5, ?_⟩
  intro n hn G _ δ hδ hlow
  by_contra hfar
  push_neg at hfar
  obtain ⟨Q, hQ4, hQ⟩ := hNf n (by omega) G hfar
  have h1 := hlow Q hQ4
  have h2 := PaperIV.FarSlackQuantitative.sq_div_six_le_targetSize (n := n) (by omega)
  have h3 : (PaperIV.targetSize n : ℚ) ≤ (defectTarget s n : ℚ) := by
    have := targetSize_le_defectTarget s n (by omega)
    exact_mod_cast this
  have hn5 : (5 : ℚ) ≤ (n : ℚ) := by exact_mod_cast (show 5 ≤ n by omega)
  have hsq : (0 : ℚ) < (n : ℚ) ^ 2 := by positivity
  nlinarith

end E32
