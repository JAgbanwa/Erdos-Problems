import PaperIV.SplitTerminalLP
import PaperIV.SplitUniformIncidence
import PaperIV.UniformSplitLoads

/-!
# Feasible split LP solutions give literal per-edge capacities

This is the first non-opaque coupling of the two split modules: the scalar
feasibility inequalities are read directly as capacities of the actual,
uniformly weighted clique families of a complete split.
-/

namespace PaperIV.SplitLPToPhysicalLoads

open PaperIV.SplitTerminalLP
open PaperIV.SplitUniformIncidence
open PaperIV.UniformSplitLoads

variable {V : Type*} [DecidableEq V]

theorem load_comm (F : Finset (Finset V)) (m : ℚ) (x y : V) :
    load F m x y = load F m y x := by
  rw [load_eq_incidence_mul, load_eq_incidence_mul, incidence_comm]

theorem totalLoad_comm (Core Hosts : Finset V) (u v w : ℚ) (x y : V) :
    totalLoad Core Hosts u v w x y = totalLoad Core Hosts u v w y x := by
  simp only [totalLoad, load_comm]

/-- A uniform weighting has unit capacity when every literal edge of the split
graph receives total load at most one. -/
def HasUnitCapacity (Core Hosts : Finset V) (u v w : ℚ) : Prop :=
  ∀ ⦃x y : V⦄, (splitGraph Core Hosts).Adj x y → totalLoad Core Hosts u v w x y ≤ 1

theorem inner_load_le_one
    {Core Hosts : Finset V} (hd : Disjoint Core Hosts) {x y : V}
    (hx : x ∈ Core) (hy : y ∈ Core) (hxy : x ≠ y)
    (hk4 : 4 ≤ Core.card) (hh : 0 < Hosts.card)
    {u v w : ℚ}
    (hfeas : Feasible (SplitUniformIncidence.splitA Core) (SplitUniformIncidence.splitB Core Hosts) u v w) :
    totalLoad Core Hosts u v w x y ≤ 1 := by
  rw [totalLoad_inner hd hx hy hxy hk4 hh]
  apply uniform_load_le_one
  · unfold SplitUniformIncidence.splitA
    exact_mod_cast (Nat.choose_pos (by omega))
  · exact hfeas.inner

theorem cross_load_le_one
    {Core Hosts : Finset V} (hd : Disjoint Core Hosts) {x z : V}
    (hx : x ∈ Core) (hz : z ∈ Hosts) (hk4 : 4 ≤ Core.card)
    {u v w : ℚ}
    (hfeas : Feasible (SplitUniformIncidence.splitA Core) (SplitUniformIncidence.splitB Core Hosts) u v w) :
    totalLoad Core Hosts u v w x z ≤ 1 := by
  rw [totalLoad_cross hd hx hz hk4]
  apply uniform_load_le_one
  · have hc : 0 < Core.card := Finset.card_pos.mpr ⟨x, hx⟩
    have hh : 0 < Hosts.card := Finset.card_pos.mpr ⟨z, hz⟩
    unfold SplitUniformIncidence.splitB
    push_cast
    positivity
  · exact hfeas.cross

/-- The pointwise inner/cross bounds are exhaustive for the complete split
graph.  Thus a feasible split-LP point gives a genuine global unit-capacity
load assignment in the literal split model. -/
theorem feasible_hasUnitCapacity
    {Core Hosts : Finset V} (hd : Disjoint Core Hosts)
    (hk4 : 4 ≤ Core.card) (hh : 0 < Hosts.card)
    {u v w : ℚ}
    (hfeas : Feasible (SplitUniformIncidence.splitA Core) (SplitUniformIncidence.splitB Core Hosts) u v w) :
    HasUnitCapacity Core Hosts u v w := by
  intro x y hadj
  rw [splitGraph_adj_iff] at hadj
  rcases hadj with ⟨hxy, ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩⟩
  · exact inner_load_le_one hd hx hy hxy hk4 hh hfeas
  · exact cross_load_le_one hd hx hy hk4 hfeas
  · rw [totalLoad_comm]
    exact cross_load_le_one hd hy hx hk4 hfeas

end PaperIV.SplitLPToPhysicalLoads
