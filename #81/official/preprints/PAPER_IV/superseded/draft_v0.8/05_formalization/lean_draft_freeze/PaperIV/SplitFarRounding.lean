import PaperIV.FarRounding
import PaperIV.SplitLPToPhysicalLoads
import PaperIV.SplitCanonicalSupportSum
import PaperIV.SplitCanonicalWeight
import PaperIV.SplitFamilyNonempty
import PaperIV.SplitItems
import PaperIV.SplitCanonicalValue

/-!
# Complete-split fractional-packing adapter

This is the compatibility integration of Aristotle task `53de59d4`: it keeps
the richer, existing `FarRounding` fractional LP and proves that the literal
uniform split weights define one of its `FracPacking` objects.  The key bridge
is that the capacity of every literal split edge is exactly `totalLoad`.
-/

namespace PaperIV.SplitFarRounding

open Finset
open PaperIV.FarRounding
open PaperIV.SplitUniformIncidence
open PaperIV.SplitTerminalLP
open PaperIV.SplitLPToPhysicalLoads
open PaperIV.SplitCanonicalWeight
open PaperIV.SplitCanonicalSupportSum
open PaperIV.SplitFamilyNonempty
open PaperIV.SplitItems

variable {V : Type*} [Fintype V] [DecidableEq V]

local instance (Core Hosts : Finset V) : DecidableRel (splitGraph Core Hosts).Adj := by
  intro x y
  unfold splitGraph
  infer_instance

/-- Aristotle's explicit uniform split weight, identified with the canonical
weight function already used by the value calculation. -/
abbrev splitWeight (Core Hosts : Finset V) (u v w : ℚ) : Finset V → ℚ :=
  selectedWeight Core Hosts u v w

theorem splitWeight_eq_zero_of_notMem_items
    {Core Hosts : Finset V} (hd : Disjoint Core Hosts) (u v w : ℚ)
    {K : Finset V} (hK : K ∉ items (splitGraph Core Hosts)) :
    splitWeight Core Hosts u v w K = 0 := by
  apply selectedWeight_eq_zero_of_outside
  · intro h
    exact hK ((famK3_subset_items hd) h)
  · intro h
    exact hK ((famK4_subset_items hd) h)
  · intro h
    exact hK ((famK4core_subset_items Core Hosts) h)

theorem splitWeight_nonneg
    {Core Hosts : Finset V} (hd : Disjoint Core Hosts)
    (hk4 : 4 ≤ Core.card) (hh : 0 < Hosts.card)
    {u v w : ℚ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w) (K : Finset V) :
    0 ≤ splitWeight Core Hosts u v w K := by
  apply selectedWeight_nonneg hd
  · exact famK3_nonempty (by omega) hh
  · exact famK4_nonempty (by omega) hh
  · exact famK4core_nonempty hk4
  · exact hu
  · exact hv
  · exact hw

/-- The canonical capacity sum through a non-diagonal pair is exactly the
three-family uniform load.  This is the substantive adapter supplied by the
Aristotle return, ported to the richer `FarRounding` representation. -/
theorem capacity_sum_eq_totalLoad
    {Core Hosts : Finset V} (hd : Disjoint Core Hosts) (u v w : ℚ)
    (x z : V) (hxz : x ≠ z) :
    (∑ K ∈ items (splitGraph Core Hosts),
      if s(x, z) ∈ pairs K then splitWeight Core Hosts u v w K else 0)
      = totalLoad Core Hosts u v w x z := by
  classical
  have hsub : famK3 Core Hosts ∪ famK4 Core Hosts ∪ famK4core Core
      ⊆ items (splitGraph Core Hosts) := selected_support_subset_items hd
  have hfilter_sub :
      (famK3 Core Hosts ∪ famK4 Core Hosts ∪ famK4core Core).filter
          (fun K => x ∈ K ∧ z ∈ K)
        ⊆ (items (splitGraph Core Hosts)).filter (fun K => x ∈ K ∧ z ∈ K) := by
    intro K hK
    rw [Finset.mem_filter] at hK ⊢
    exact ⟨hsub hK.1, hK.2⟩
  have hzero : ∀ K ∈ (items (splitGraph Core Hosts)).filter (fun K => x ∈ K ∧ z ∈ K),
      K ∉ (famK3 Core Hosts ∪ famK4 Core Hosts ∪ famK4core Core).filter
          (fun K => x ∈ K ∧ z ∈ K) →
      splitWeight Core Hosts u v w K = 0 := by
    intro K hK hnot
    rw [Finset.mem_filter] at hK
    apply selectedWeight_eq_zero_of_outside
    · intro h
      exact hnot (Finset.mem_filter.2
        ⟨Finset.mem_union.2 (Or.inl (Finset.mem_union.2 (Or.inl h))), hK.2⟩)
    · intro h
      exact hnot (Finset.mem_filter.2
        ⟨Finset.mem_union.2 (Or.inl (Finset.mem_union.2 (Or.inr h))), hK.2⟩)
    · intro h
      exact hnot (Finset.mem_filter.2 ⟨Finset.mem_union.2 (Or.inr h), hK.2⟩)
  have hpair :
      (∑ K ∈ items (splitGraph Core Hosts),
        if s(x, z) ∈ pairs K then splitWeight Core Hosts u v w K else 0)
        = ∑ K ∈ (items (splitGraph Core Hosts)).filter (fun K => x ∈ K ∧ z ∈ K),
          splitWeight Core Hosts u v w K := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl ?_
    intro K _
    refine if_congr ?_ rfl rfl
    rw [mk_mem_pairs]
    simp [hxz]
  have h34 : Disjoint (famK3 Core Hosts) (famK4 Core Hosts) :=
    PaperIV.SplitFamilyDisjoint.disjoint_famK3_famK4 hd
  have h3c : Disjoint (famK3 Core Hosts) (famK4core Core) :=
    PaperIV.SplitFamilyDisjoint.disjoint_famK3_famK4core hd
  have h4c : Disjoint (famK4 Core Hosts) (famK4core Core) :=
    PaperIV.SplitFamilyDisjoint.disjoint_famK4_famK4core hd
  have hlast : Disjoint
      ((famK3 Core Hosts).filter (fun K => x ∈ K ∧ z ∈ K)
        ∪ (famK4 Core Hosts).filter (fun K => x ∈ K ∧ z ∈ K))
      ((famK4core Core).filter (fun K => x ∈ K ∧ z ∈ K)) :=
    Finset.disjoint_union_left.mpr ⟨Finset.disjoint_filter_filter h3c,
      Finset.disjoint_filter_filter h4c⟩
  refine hpair.trans (((Finset.sum_subset hfilter_sub hzero).symm).trans ?_)
  rw [Finset.filter_union, Finset.filter_union, Finset.sum_union hlast,
    Finset.sum_union (Finset.disjoint_filter_filter h34), totalLoad]
  congr 1
  · congr 1
    · refine Finset.sum_congr rfl ?_
      intro K hK
      exact selectedWeight_of_mem_famK3 (Finset.mem_filter.1 hK).1
    · refine Finset.sum_congr rfl ?_
      intro K hK
      exact selectedWeight_of_mem_famK4 hd (Finset.mem_filter.1 hK).1
  · refine Finset.sum_congr rfl ?_
    intro K hK
    exact selectedWeight_of_mem_famK4core hd (Finset.mem_filter.1 hK).1

/-- A feasible complete-split LP point is a genuine fractional packing in the
canonical `FarRounding` model. -/
noncomputable def isFracPacking_splitWeight
    {Core Hosts : Finset V} (hd : Disjoint Core Hosts)
    (hk4 : 4 ≤ Core.card) (hh : 0 < Hosts.card)
    {u v w : ℚ} (hfeas : Feasible (splitA Core) (splitB Core Hosts) u v w) :
    FarRounding.FracPacking (splitGraph Core Hosts) ℚ := by
  refine
    { weight := splitWeight Core Hosts u v w
      weight_nonneg := ?_
      capacity := ?_ }
  · exact splitWeight_nonneg hd hk4 hh hfeas.nonneg_u hfeas.nonneg_v hfeas.nonneg_w
  · intro e he
    induction e using Sym2.ind with
    | _ x z =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
      have hxz : x ≠ z := (splitGraph Core Hosts).ne_of_adj he
      rw [capacity_sum_eq_totalLoad hd u v w x z hxz]
      exact feasible_hasUnitCapacity hd hk4 hh hfeas he

/-- The canonical fractional packing associated with a feasible split-LP
point.  Naming the object makes its objective available to later rounding
statements without re-running the capacity argument. -/
noncomputable def splitFracPacking
    {Core Hosts : Finset V} (hd : Disjoint Core Hosts)
    (hk4 : 4 ≤ Core.card) (hh : 0 < Hosts.card)
    {u v w : ℚ} (hfeas : Feasible (splitA Core) (splitB Core Hosts) u v w) :
    FarRounding.FracPacking (splitGraph Core Hosts) ℚ :=
  isFracPacking_splitWeight hd hk4 hh hfeas

/-- Exact objective of the canonical split fractional packing. -/
theorem splitFracPacking_value
    {Core Hosts : Finset V} (hd : Disjoint Core Hosts)
    (hk4 : 4 ≤ Core.card) (hh : 0 < Hosts.card)
    {u v w : ℚ} (hfeas : Feasible (splitA Core) (splitB Core Hosts) u v w) :
    (splitFracPacking hd hk4 hh hfeas).value = 2 * u + 5 * v + 5 * w := by
  change ∑ K ∈ items (splitGraph Core Hosts),
      gainF ℚ K * selectedWeight Core Hosts u v w K = _
  exact PaperIV.SplitCanonicalValue.selected_gain_value_over_items_nondegenerate hd hk4 hh u v w

/-! ## The host-free endpoint

The generic adapter above assumes that all three selected families are
nonempty.  When there are no hosts, the first two families vanish and the
uniform core-`K₄` family alone gives the required fractional packing. -/

theorem splitWeight_coreOnly_nonneg
    {Core : Finset V} (hk4 : 4 ≤ Core.card) (K : Finset V) :
    0 ≤ splitWeight Core (∅ : Finset V) 0 0 (splitA Core / 6) K := by
  have h4c := famK4core_nonempty (Core := Core) hk4
  rw [show splitWeight Core (∅ : Finset V) 0 0 (splitA Core / 6) K =
      selectedWeight Core ∅ 0 0 (splitA Core / 6) K from rfl]
  unfold selectedWeight
  rw [famK3_eq_empty_of_hosts_empty, famK4_eq_empty_of_hosts_empty]
  have hempty : K ∉ (∅ : Finset (Finset V)) := by simp
  rw [if_neg hempty, if_neg hempty]
  split_ifs
  · apply PaperIV.UniformWeightValue.uniformWeight_nonneg h4c
    apply div_nonneg
    · unfold PaperIV.SplitUniformIncidence.splitA
      positivity
    · norm_num
  · exact le_rfl

/-- With no hosts, the uniform mass `a/6` on all core `K₄`'s is a literal
fractional packing of the complete core. -/
noncomputable def coreOnlyFracPacking
    {Core : Finset V} (hk4 : 4 ≤ Core.card) :
    FarRounding.FracPacking (splitGraph Core ∅) ℚ := by
  refine
    { weight := splitWeight Core ∅ 0 0 (splitA Core / 6)
      weight_nonneg := splitWeight_coreOnly_nonneg hk4
      capacity := ?_ }
  intro e he
  induction e using Sym2.ind with
  | _ x z =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
      have hxz : x ≠ z := (splitGraph Core ∅).ne_of_adj he
      have hx : x ∈ Core := by
        rw [splitGraph_adj_iff] at he
        have hcore : x ∈ Core ∧ z ∈ Core := by simpa using he.2
        exact hcore.1
      have hz : z ∈ Core := by
        have hcore : x ∈ Core ∧ z ∈ Core := by simpa using he.2
        exact hcore.2
      rw [capacity_sum_eq_totalLoad (Finset.disjoint_empty_right Core)
        0 0 (splitA Core / 6) x z hxz]
      rw [totalLoad_inner_hosts_empty hx hz hxz hk4]
      have ha : 0 < PaperIV.SplitUniformIncidence.splitA Core := by
        unfold PaperIV.SplitUniformIncidence.splitA
        exact_mod_cast Nat.choose_pos (by omega : 2 ≤ Core.card)
      field_simp
      exact le_rfl

/-- Exact objective of the host-free core packing. -/
theorem coreOnlyFracPacking_value
    {Core : Finset V} (hk4 : 4 ≤ Core.card) :
    (coreOnlyFracPacking hk4).value = 5 * (splitA Core / 6) := by
  classical
  change ∑ K ∈ items (splitGraph Core ∅),
      gainF ℚ K * selectedWeight Core ∅ 0 0 (splitA Core / 6) K = _
  have hsub : famK4core Core ⊆ items (splitGraph Core ∅) :=
    famK4core_subset_items Core ∅
  rw [← Finset.sum_subset hsub]
  · calc
      (∑ K ∈ famK4core Core,
          gainF ℚ K * selectedWeight Core ∅ 0 0 (splitA Core / 6) K) =
          ∑ K ∈ famK4core Core,
            5 * uniformWeight (famK4core Core) (splitA Core / 6) := by
              apply Finset.sum_congr rfl
              intro K hK
              rw [PaperIV.SplitCanonicalValue.gainF_famK4core (Hosts := ∅) hK,
                selectedWeight_of_mem_famK4core (Finset.disjoint_empty_right Core) hK]
      _ = 5 * (splitA Core / 6) := by
        rw [← Finset.mul_sum, sum_uniformWeight (famK4core_nonempty hk4)]
  · intro K hK hnot
    have hnot3 : K ∉ famK3 Core ∅ := by
      rw [famK3_eq_empty_of_hosts_empty]
      simp
    have hnot4 : K ∉ famK4 Core ∅ := by
      rw [famK4_eq_empty_of_hosts_empty]
      simp
    simp [selectedWeight_eq_zero_of_outside hnot3 hnot4 hnot]

end PaperIV.SplitFarRounding
