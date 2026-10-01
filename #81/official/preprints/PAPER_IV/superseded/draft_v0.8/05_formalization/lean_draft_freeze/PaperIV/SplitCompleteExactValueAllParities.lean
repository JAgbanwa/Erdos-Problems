import PaperIV.SplitCompleteExactValue
import PaperIV.SplitTriangleFactorOddHighHost

/-! # Exact complete-split value in both core parities -/

namespace PaperIV.SplitCompleteExactValueAllParities

open PaperIV.Model PaperIV.SplitUniformIncidence
open PaperIV.SplitCompleteExactValue

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- For every nontrivial complete-split core with at least as many hosts as core
vertices, the split baseline is attained and is optimal among all order-four
clique partitions. -/
theorem exists_optimal_cliquePartition_allParities
    {Core Hosts : Finset V} (hd : Disjoint Core Hosts)
    (hcore : 2 ≤ Core.card) (hhosts : Core.card ≤ Hosts.card) :
    ∃ Q : PaperIV.FarRounding.CliquePartition (splitGraph Core Hosts),
      Q.OrderAtMost 4 ∧
      Q.size = Core.card * Hosts.card - Core.card.choose 2 ∧
      ∀ R : PaperIV.FarRounding.CliquePartition (splitGraph Core Hosts),
        R.OrderAtMost 4 → Q.size ≤ R.size := by
  rcases Nat.even_or_odd Core.card with heven | hodd
  · obtain ⟨r, hr⟩ := heven
    have hrpos : 0 < r := by omega
    have hk : Core.card = 2 * (r - 1) + 2 := by omega
    exact exists_optimal_cliquePartition hd hk (by omega)
  · obtain ⟨r, hr⟩ := hodd
    obtain ⟨P, _hpack, hpart, hcard⟩ :=
      PaperIV.SplitTriangleFactorOddHighHost.exists_odd_high_host_baseline
        hd (n := r) (by omega) (by omega)
    let Q := PaperIV.PhysicalToCliquePartition.ofExactPartition hpart
    refine ⟨Q, PaperIV.PhysicalToCliquePartition.ofExactPartition_orderAtMost_four hpart,
      ?_, ?_⟩
    · simpa [Q] using hcard
    · intro R hR
      rw [show Q.size = Core.card * Hosts.card - Core.card.choose 2 by simpa [Q] using hcard]
      exact cliquePartition_size_ge_baseline hd R hR

end PaperIV.SplitCompleteExactValueAllParities
