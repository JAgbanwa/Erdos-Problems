import SmallOrderFractional
import PaperIV.RC01FarAssembly
import PaperIV.CertifiedOptimumExistence

/-! The uniform RC01 threshold is chosen from epsilon alone, before n and s.
Neither the refined fractional bound nor a physical realizer is an assumption.
-/
namespace PaperIV.SublinearResearch
open PaperIV.FarRounding PaperIV.RootedSimplicialDefect

theorem uniform_shifted_partition_bound (ε : ℚ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n s : ℕ, N ≤ n → s ≤ n →
    ∀ G : SimpleGraph (Fin n), ∀ [DecidableRel G.Adj], RootedDefectAt G s →
      ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧
        (Q.size : ℚ) ≤ (targetSize (n-s) : ℚ)+(n : ℚ)*s+ε*(n : ℚ)^2 := by
  classical
  obtain ⟨N,hround⟩ := RC01FarAssembly.uniformTransferAt ε hε
  refine ⟨N,?_⟩
  intro n s hn hs G _ hG
  obtain ⟨w,hw⟩ := CertifiedOptimumExistence.exists_certifiedFractionalOptimum G
  have hb := certified_shifted_fractional_bound_all_orders hs G hG hw
  obtain ⟨P,hP⟩ := hround n hn G w hw
  obtain ⟨Q,hQ,hcount⟩ := exists_cliquePartition_of_packing P
  have hc : (Q.size : ℚ)+(P.gain : ℚ) = (G.edgeFinset.card : ℚ) := by exact_mod_cast hcount
  exact ⟨Q,hQ,by linarith⟩

theorem uniform_refined_partition_bound (ε : ℚ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n s : ℕ, N ≤ n → 4*s ≤ n →
    ∀ G : SimpleGraph (Fin n), ∀ [DecidableRel G.Adj], RootedDefectAt G s →
      ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧
        (Q.size : ℚ) ≤ (targetSize (n-s) : ℚ)+(n : ℚ)*s-
          ((s+1).choose 2 : ℚ)+ε*(n : ℚ)^2 := by
  classical
  obtain ⟨N,hround⟩ := RC01FarAssembly.uniformTransferAt ε hε
  refine ⟨N,?_⟩
  intro n s hn hs G _ hG
  obtain ⟨w,hw⟩ := CertifiedOptimumExistence.exists_certifiedFractionalOptimum G
  have hb := certified_refined_fractional_bound_all_orders hs G hG hw
  obtain ⟨P,hP⟩ := hround n hn G w hw
  obtain ⟨Q,hQ,hcount⟩ := exists_cliquePartition_of_packing P
  have hc : (Q.size : ℚ)+(P.gain : ℚ) = (G.edgeFinset.card : ℚ) := by exact_mod_cast hcount
  exact ⟨Q,hQ,by linarith⟩

end PaperIV.SublinearResearch
#print axioms PaperIV.SublinearResearch.uniform_shifted_partition_bound
#print axioms PaperIV.SublinearResearch.uniform_refined_partition_bound
