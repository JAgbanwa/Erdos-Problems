import PaperIV.SplitFamilyDisjoint
import PaperIV.UniformWeightValue

/-!
# One canonical weight function for the selected split families

The three uniform masses are assembled into one total function on finite vertex
sets.  Its zero branch is essential: canonical mixed-packing items not selected
by the split LP receive no weight.
-/

namespace PaperIV.SplitCanonicalWeight

open PaperIV.SplitUniformIncidence
open PaperIV.SplitFamilyDisjoint
open PaperIV.UniformWeightValue

variable {V : Type*} [DecidableEq V]

def selectedWeight (Core Hosts : Finset V) (u v w : ℚ) (K : Finset V) : ℚ :=
  if K ∈ famK3 Core Hosts then uniformWeight (famK3 Core Hosts) u
  else if K ∈ famK4 Core Hosts then uniformWeight (famK4 Core Hosts) v
  else if K ∈ famK4core Core then uniformWeight (famK4core Core) w
  else 0

theorem selectedWeight_nonneg
    {Core Hosts : Finset V} (hd : Disjoint Core Hosts)
    (h3 : (famK3 Core Hosts).Nonempty)
    (h4 : (famK4 Core Hosts).Nonempty)
    (h4c : (famK4core Core).Nonempty)
    {u v w : ℚ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w) (K : Finset V) :
    0 ≤ selectedWeight Core Hosts u v w K := by
  unfold selectedWeight
  split_ifs
  · exact uniformWeight_nonneg h3 hu
  · exact uniformWeight_nonneg h4 hv
  · exact uniformWeight_nonneg h4c hw
  · exact le_rfl

theorem selectedWeight_of_mem_famK3
    {Core Hosts : Finset V} {u v w : ℚ} {K : Finset V}
    (hK : K ∈ famK3 Core Hosts) :
    selectedWeight Core Hosts u v w K = uniformWeight (famK3 Core Hosts) u := by
  simp [selectedWeight, hK]

theorem selectedWeight_of_mem_famK4
    {Core Hosts : Finset V} (hd : Disjoint Core Hosts) {u v w : ℚ} {K : Finset V}
    (hK : K ∈ famK4 Core Hosts) :
    selectedWeight Core Hosts u v w K = uniformWeight (famK4 Core Hosts) v := by
  have hnot3 : K ∉ famK3 Core Hosts := fun h =>
    Finset.disjoint_left.mp (disjoint_famK3_famK4 hd) h hK
  simp [selectedWeight, hnot3, hK]

theorem selectedWeight_of_mem_famK4core
    {Core Hosts : Finset V} (hd : Disjoint Core Hosts) {u v w : ℚ} {K : Finset V}
    (hK : K ∈ famK4core Core) :
    selectedWeight Core Hosts u v w K = uniformWeight (famK4core Core) w := by
  have hnot3 : K ∉ famK3 Core Hosts := fun h =>
    Finset.disjoint_left.mp (disjoint_famK3_famK4core hd) h hK
  have hnot4 : K ∉ famK4 Core Hosts := fun h =>
    Finset.disjoint_left.mp (disjoint_famK4_famK4core hd) h hK
  simp [selectedWeight, hnot3, hnot4, hK]

theorem selectedWeight_eq_zero_of_outside
    {Core Hosts : Finset V} {u v w : ℚ} {K : Finset V}
    (h3 : K ∉ famK3 Core Hosts) (h4 : K ∉ famK4 Core Hosts)
    (h4c : K ∉ famK4core Core) :
    selectedWeight Core Hosts u v w K = 0 := by
  simp [selectedWeight, h3, h4, h4c]

theorem sum_selectedWeight_on_support
    {Core Hosts : Finset V} (hd : Disjoint Core Hosts)
    (h3 : (famK3 Core Hosts).Nonempty)
    (h4 : (famK4 Core Hosts).Nonempty)
    (h4c : (famK4core Core).Nonempty)
    (u v w : ℚ) :
    ∑ K ∈ (famK3 Core Hosts ∪ famK4 Core Hosts ∪ famK4core Core),
      selectedWeight Core Hosts u v w K = u + v + w := by
  have h34 := disjoint_famK3_famK4 hd
  have h3c := disjoint_famK3_famK4core hd
  have h4c' := disjoint_famK4_famK4core hd
  have hUnion : Disjoint (famK3 Core Hosts ∪ famK4 Core Hosts) (famK4core Core) :=
    Finset.disjoint_union_left.mpr ⟨h3c, h4c'⟩
  have hs3 : ∑ K ∈ famK3 Core Hosts, selectedWeight Core Hosts u v w K = u := by
    calc
      ∑ K ∈ famK3 Core Hosts, selectedWeight Core Hosts u v w K =
          ∑ K ∈ famK3 Core Hosts, uniformWeight (famK3 Core Hosts) u := by
        apply Finset.sum_congr rfl
        intro K hK
        exact selectedWeight_of_mem_famK3 hK
      _ = u := sum_uniformWeight h3 u
  have hs4 : ∑ K ∈ famK4 Core Hosts, selectedWeight Core Hosts u v w K = v := by
    calc
      ∑ K ∈ famK4 Core Hosts, selectedWeight Core Hosts u v w K =
          ∑ K ∈ famK4 Core Hosts, uniformWeight (famK4 Core Hosts) v := by
        apply Finset.sum_congr rfl
        intro K hK
        exact selectedWeight_of_mem_famK4 hd hK
      _ = v := sum_uniformWeight h4 v
  have hs4c : ∑ K ∈ famK4core Core, selectedWeight Core Hosts u v w K = w := by
    calc
      ∑ K ∈ famK4core Core, selectedWeight Core Hosts u v w K =
          ∑ K ∈ famK4core Core, uniformWeight (famK4core Core) w := by
        apply Finset.sum_congr rfl
        intro K hK
        exact selectedWeight_of_mem_famK4core hd hK
      _ = w := sum_uniformWeight h4c w
  rw [Finset.sum_union hUnion, Finset.sum_union h34, hs3, hs4, hs4c]

/-- Any item carrying nonzero selected weight lies in one of the three
literal split families.  This is the support reduction used when sums are
initially indexed by all canonical items. -/
theorem mem_support_of_selectedWeight_ne_zero
    {Core Hosts : Finset V} {u v w : ℚ} {K : Finset V}
    (hK : selectedWeight Core Hosts u v w K ≠ 0) :
    K ∈ famK3 Core Hosts ∪ famK4 Core Hosts ∪ famK4core Core := by
  by_contra hnot
  have hout : K ∉ famK3 Core Hosts ∧ K ∉ famK4 Core Hosts ∧ K ∉ famK4core Core := by
    simpa only [Finset.mem_union, not_or, and_assoc] using hnot
  exact hK (selectedWeight_eq_zero_of_outside hout.1 hout.2.1 hout.2.2)

end PaperIV.SplitCanonicalWeight
