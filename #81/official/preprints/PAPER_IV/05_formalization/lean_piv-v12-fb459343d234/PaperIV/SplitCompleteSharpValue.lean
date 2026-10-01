import PaperIV.SplitCompleteExactValueAllParities
import PaperIV.SplitCompleteSharpLower

/-! # Sharp complete-split value against unrestricted clique partitions -/

namespace PaperIV.SplitCompleteSharpValue

open PaperIV.FarRounding PaperIV.SplitUniformIncidence
open PaperIV.SplitCompleteExactValueAllParities
open PaperIV.SplitCompleteSharpLower

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem exists_sharp_cliquePartition_allParities
    {Core Hosts : Finset V} (hd : Disjoint Core Hosts)
    (hcore : 2 ≤ Core.card) (hhosts : Core.card ≤ Hosts.card) :
    ∃ Q : CliquePartition (splitGraph Core Hosts),
      Q.OrderAtMost 4 ∧
      Q.size = Core.card * Hosts.card - Core.card.choose 2 ∧
      ∀ R : CliquePartition (splitGraph Core Hosts), Q.size ≤ R.size := by
  obtain ⟨Q, hQ4, hQsize, _hQopt4⟩ :=
    exists_optimal_cliquePartition_allParities hd hcore hhosts
  refine ⟨Q, hQ4, hQsize, ?_⟩
  intro R
  rw [hQsize]
  exact cliquePartition_size_ge_baseline_unrestricted hd R

end PaperIV.SplitCompleteSharpValue
