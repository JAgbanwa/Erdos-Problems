import PaperIV.NearH1GlobalAssembly
import PaperIV.TargetEnvelope
import PaperIV.CertifiedOptimumExistence

/-!
# Unconditional export of the chordal Erdős #81 theorem

The near H1 route and the RC01 far route are both discharged in the imported
assembly.  This file only exposes the final statement in its named and
expanded forms.
-/

namespace PaperIV.Erdos81Unconditional

open PaperIV.FarRounding PaperIV.RC01FarAssembly

/-- Every sufficiently large chordal graph has a clique partition of order at
most four and size at most `⌊n(n+1)/6⌋`. -/
theorem erdos81_chordalTarget : ChordalTargetAt :=
  PaperIV.NearH1GlobalAssembly.chordalTargetAt

/-- Expanded certificate-parametric form of the assembled route. -/
theorem erdos81_cliquePartition_of_certificate :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      PaperIV.FarRounding.IsChordal G → ∀ w : ℚ, CertifiedFractionalOptimum G w →
        ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size ≤ targetSize n :=
  erdos81_chordalTarget

/-- **Unconditional Erdős #81 export.**  The finite rational optimum certificate
is constructed internally, so the statement has no analytic or LP input. -/
theorem erdos81_cliquePartition :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      PaperIV.FarRounding.IsChordal G →
        ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size ≤ targetSize n := by
  obtain ⟨N, hN⟩ := erdos81_cliquePartition_of_certificate
  refine ⟨N, ?_⟩
  intro n hn G _ hG
  obtain ⟨w, hw⟩ :=
    PaperIV.CertifiedOptimumExistence.exists_certifiedFractionalOptimum G
  exact hN n hn G hG w hw

/-- The traditional `n²/6 + O(n)` formulation. -/
theorem erdos81_linear_form :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      PaperIV.FarRounding.IsChordal G →
        ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧
          (Q.size : ℚ) ≤ (n : ℚ) ^ 2 / 6 + (n : ℚ) / 6 := by
  obtain ⟨N, hN⟩ := erdos81_cliquePartition
  refine ⟨N, ?_⟩
  intro n hn G _ hG
  obtain ⟨Q, hQ4, hQsize⟩ := hN n hn G hG
  refine ⟨Q, hQ4, ?_⟩
  have h1 : (Q.size : ℚ) ≤ ((targetSize n : ℕ) : ℚ) := by
    exact_mod_cast hQsize
  have h2 : ((targetSize n : ℕ) : ℚ) ≤
      (n : ℚ) * ((n : ℚ) + 1) / 6 :=
    PaperIV.targetSize_cast_le_continuous n
  have h3 : (n : ℚ) * ((n : ℚ) + 1) / 6 = (n : ℚ) ^ 2 / 6 + (n : ℚ) / 6 := by
    ring
  linarith [h1.trans h2, h3]

end PaperIV.Erdos81Unconditional
