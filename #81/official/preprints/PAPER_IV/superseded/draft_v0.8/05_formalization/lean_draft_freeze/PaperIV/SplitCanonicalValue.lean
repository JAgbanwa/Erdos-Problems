import PaperIV.SplitCanonicalSupportSum
import PaperIV.SplitFamilyNonempty

/-!
# Exact canonical mixed value of the selected split weight
-/

namespace PaperIV.SplitCanonicalValue

open PaperIV.FarRounding
open PaperIV.SplitUniformIncidence
open PaperIV.SplitFamilyDisjoint
open PaperIV.SplitCanonicalWeight
open PaperIV.SplitCanonicalSupportSum
open PaperIV.SplitFamilyNonempty

variable {V : Type*} [Fintype V] [DecidableEq V]

local instance (Core Hosts : Finset V) : DecidableRel (splitGraph Core Hosts).Adj := by
  intro x y
  unfold splitGraph
  infer_instance

theorem gainF_famK3 {Core Hosts : Finset V} (hd : Disjoint Core Hosts)
    {K : Finset V} (hK : K ∈ famK3 Core Hosts) : gainF ℚ K = 2 := by
  unfold gainF
  rw [(famK3_isClique hd hK).2]
  norm_num

theorem gainF_famK4 {Core Hosts : Finset V} (hd : Disjoint Core Hosts)
    {K : Finset V} (hK : K ∈ famK4 Core Hosts) : gainF ℚ K = 5 := by
  have e42 : Nat.choose 4 2 = 6 := by decide
  unfold gainF
  rw [(famK4_isClique hd hK).2, e42]
  norm_num

theorem gainF_famK4core {Core Hosts : Finset V}
    {K : Finset V} (hK : K ∈ famK4core Core) : gainF ℚ K = 5 := by
  have e42 : Nat.choose 4 2 = 6 := by decide
  unfold gainF
  rw [(famK4core_isClique (Hosts := Hosts) hK).2, e42]
  norm_num

theorem selected_gain_value_over_items
    {Core Hosts : Finset V} (hd : Disjoint Core Hosts)
    (h3 : (famK3 Core Hosts).Nonempty)
    (h4 : (famK4 Core Hosts).Nonempty)
    (h4c : (famK4core Core).Nonempty)
    (u v w : ℚ) :
    ∑ K ∈ items (splitGraph Core Hosts),
      gainF ℚ K * selectedWeight Core Hosts u v w K = 2 * u + 5 * v + 5 * w := by
  let S := famK3 Core Hosts ∪ famK4 Core Hosts ∪ famK4core Core
  have hsub : S ⊆ items (splitGraph Core Hosts) := selected_support_subset_items hd
  have hsum :
      (∑ K ∈ S, gainF ℚ K * selectedWeight Core Hosts u v w K) =
        ∑ K ∈ items (splitGraph Core Hosts), gainF ℚ K * selectedWeight Core Hosts u v w K := by
    apply Finset.sum_subset hsub
    intro K hK hnot
    have hnot3 : K ∉ famK3 Core Hosts := fun h => hnot (by simp [S, h])
    have hnot4 : K ∉ famK4 Core Hosts := fun h => hnot (by simp [S, h])
    have hnot4c : K ∉ famK4core Core := fun h => hnot (by simp [S, h])
    simp [selectedWeight_eq_zero_of_outside hnot3 hnot4 hnot4c]
  rw [← hsum, show S = (famK3 Core Hosts ∪ famK4 Core Hosts) ∪ famK4core Core by rfl]
  rw [Finset.sum_union (Finset.disjoint_union_left.mpr ⟨disjoint_famK3_famK4core hd,
    disjoint_famK4_famK4core hd⟩), Finset.sum_union (disjoint_famK3_famK4 hd)]
  have hs3 : ∑ K ∈ famK3 Core Hosts, gainF ℚ K * selectedWeight Core Hosts u v w K = 2 * u := by
    calc
      _ = ∑ K ∈ famK3 Core Hosts, 2 * uniformWeight (famK3 Core Hosts) u := by
        apply Finset.sum_congr rfl
        intro K hK
        rw [gainF_famK3 hd hK, selectedWeight_of_mem_famK3 hK]
      _ = 2 * u := by rw [← Finset.mul_sum, sum_uniformWeight h3]
  have hs4 : ∑ K ∈ famK4 Core Hosts, gainF ℚ K * selectedWeight Core Hosts u v w K = 5 * v := by
    calc
      _ = ∑ K ∈ famK4 Core Hosts, 5 * uniformWeight (famK4 Core Hosts) v := by
        apply Finset.sum_congr rfl
        intro K hK
        rw [gainF_famK4 hd hK, selectedWeight_of_mem_famK4 hd hK]
      _ = 5 * v := by rw [← Finset.mul_sum, sum_uniformWeight h4]
  have hs4c : ∑ K ∈ famK4core Core, gainF ℚ K * selectedWeight Core Hosts u v w K = 5 * w := by
    calc
      _ = ∑ K ∈ famK4core Core, 5 * uniformWeight (famK4core Core) w := by
        apply Finset.sum_congr rfl
        intro K hK
        rw [gainF_famK4core (Hosts := Hosts) hK, selectedWeight_of_mem_famK4core hd hK]
      _ = 5 * w := by rw [← Finset.mul_sum, sum_uniformWeight h4c]
  rw [hs3, hs4, hs4c]

/-- The exact canonical value in the ordinary nondegenerate split regime,
with family nonemptiness discharged from `k ≥ 4` and `h > 0`. -/
theorem selected_gain_value_over_items_nondegenerate
    {Core Hosts : Finset V} (hd : Disjoint Core Hosts)
    (hk4 : 4 ≤ Core.card) (hh : 0 < Hosts.card)
    (u v w : ℚ) :
    ∑ K ∈ items (splitGraph Core Hosts),
      gainF ℚ K * selectedWeight Core Hosts u v w K = 2 * u + 5 * v + 5 * w := by
  apply selected_gain_value_over_items hd
  · exact famK3_nonempty (by omega) hh
  · exact famK4_nonempty (by omega) hh
  · exact famK4core_nonempty hk4

end PaperIV.SplitCanonicalValue
