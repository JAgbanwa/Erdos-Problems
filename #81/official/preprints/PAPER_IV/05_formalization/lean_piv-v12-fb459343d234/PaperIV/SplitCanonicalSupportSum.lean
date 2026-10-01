import PaperIV.SplitCanonicalWeight
import PaperIV.SplitItems

/-!
# Reducing canonical item sums to the selected split support

Although the canonical item program contains additional cliques, the selected
weight function vanishes outside the three literal split families.  This module
makes that finite-sum reduction explicit.
-/

namespace PaperIV.SplitCanonicalSupportSum

open PaperIV.FarRounding
open PaperIV.SplitUniformIncidence
open PaperIV.SplitItems
open PaperIV.SplitCanonicalWeight

variable {V : Type*} [Fintype V] [DecidableEq V]

local instance (Core Hosts : Finset V) : DecidableRel (splitGraph Core Hosts).Adj := by
  intro x y
  unfold splitGraph
  infer_instance

theorem selected_support_subset_items {Core Hosts : Finset V} (hd : Disjoint Core Hosts) :
    famK3 Core Hosts ∪ famK4 Core Hosts ∪ famK4core Core ⊆
      items (splitGraph Core Hosts) := by
  exact Finset.union_subset
    (Finset.union_subset (famK3_subset_items hd) (famK4_subset_items hd))
    (famK4core_subset_items Core Hosts)

theorem sum_selectedWeight_over_items
    {Core Hosts : Finset V} (hd : Disjoint Core Hosts)
    (h3 : (famK3 Core Hosts).Nonempty)
    (h4 : (famK4 Core Hosts).Nonempty)
    (h4c : (famK4core Core).Nonempty)
    (u v w : ℚ) :
    ∑ K ∈ items (splitGraph Core Hosts), selectedWeight Core Hosts u v w K = u + v + w := by
  let S := famK3 Core Hosts ∪ famK4 Core Hosts ∪ famK4core Core
  have hsub : S ⊆ items (splitGraph Core Hosts) := selected_support_subset_items hd
  have hsum :
      (∑ K ∈ S, selectedWeight Core Hosts u v w K) =
        ∑ K ∈ items (splitGraph Core Hosts), selectedWeight Core Hosts u v w K := by
    apply Finset.sum_subset hsub
    intro K hK hnot
    have hnot3 : K ∉ famK3 Core Hosts := fun h => hnot (by simp [S, h])
    have hnot4 : K ∉ famK4 Core Hosts := fun h => hnot (by simp [S, h])
    have hnot4c : K ∉ famK4core Core := fun h => hnot (by simp [S, h])
    exact selectedWeight_eq_zero_of_outside hnot3 hnot4 hnot4c
  rw [← hsum]
  exact sum_selectedWeight_on_support hd h3 h4 h4c u v w

end PaperIV.SplitCanonicalSupportSum
