import PaperIV.F4EditRobustness
import PaperIV.SplitFarRounding
import PaperIV.SplitEdgeCount
import PaperIV.NearTerminalSynthesis
import PaperIV.GatedSplitTargetBridge

/-! # Residual localization of a literal split comparator

This module turns the scalar three-branch split LP into an upper bound for the
actual mixed fractional defect of the literal split graph.  It deliberately
keeps the graph-theoretic realization and the branch arithmetic separate.
-/

namespace PaperIV.SplitComparatorResidual

open Finset
open PaperIV.FarRounding
open PaperIV.VertexCopyMonotone PaperIV.VertexCopyGate
open PaperIV.VertexCopyWBridge
open PaperIV.SplitUniformIncidence
open PaperIV.SplitTerminalLP

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Exact critical-branch identity. -/
theorem wide_cost_eq_baseline {n k a b : ℚ}
    (ha : a = k * (k - 1) / 2) (hb : b = k * (n - k)) :
    b - a = PaperIV.splitBaseline n k := by
  rw [ha, hb]
  unfold PaperIV.splitBaseline
  ring

/-- Universal envelope for the middle branch. -/
theorem middle_cost_le_envelope {n k a b : ℚ}
    (ha : a = k * (k - 1) / 2) (hb : b = k * (n - k))
    (hab : a ≤ b) (hba : b ≤ 2 * a) :
    (2 * b - a) / 3 ≤ (4 * n + 1) ^ 2 / 120 := by
  rw [ha, hb] at hab hba ⊢
  nlinarith [sq_nonneg (10 * k - 4 * n - 1)]

/-- Universal envelope for the low branch.  The hypothesis `1 ≤ n-k` is the
literal positive-host integrality input found by the Certo precheck. -/
theorem low_cost_le_envelope {n k a b : ℚ}
    (ha : a = k * (k - 1) / 2) (hb : b = k * (n - k))
    (hhost : 1 ≤ n - k) :
    (a + b) / 6 ≤ n * (n - 1) / 12 := by
  rw [ha, hb]
  have h₁ : 0 ≤ n - k := by linarith
  have h₂ : 0 ≤ n - k - 1 := by linarith
  nlinarith [mul_nonneg h₁ h₂]

/-- Every feasible canonical split point bounds the actual real mixed defect
by its scalar cost. -/
theorem F4'_splitGraph_le_cost
    {Core Hosts : Finset V} (hd : Disjoint Core Hosts)
    (hk4 : 4 ≤ Core.card) (hh : 0 < Hosts.card)
    {u v w : ℚ}
    (hfeas : Feasible (PaperIV.SplitUniformIncidence.splitA Core)
      (PaperIV.SplitUniformIncidence.splitB Core Hosts) u v w) :
    F4' (splitGraph Core Hosts) ≤
      ((cost (PaperIV.SplitUniformIncidence.splitA Core)
        (PaperIV.SplitUniformIncidence.splitB Core Hosts) u v w : ℚ) : ℝ) := by
  classical
  let x := PaperIV.SplitFarRounding.splitFracPacking hd hk4 hh hfeas
  have hopt := PaperIV.VertexCopyMonotone.le_optVal x.toReal
  rw [← PaperIV.VertexCopyWBridge.optVal'_eq] at hopt
  have hxval : x.toReal.value =
      (((2 * u + 5 * v + 5 * w : ℚ)) : ℝ) := by
    rw [FracPacking.toReal_value]
    exact_mod_cast PaperIV.SplitFarRounding.splitFracPacking_value hd hk4 hh hfeas
  rw [hxval] at hopt
  push_cast at hopt
  rw [PaperIV.VertexCopyWBridge.F4'_eq_edge_sub_optVal']
  have hedge := PaperIV.SplitEdgeCount.card_graphEdges_splitGraph hd
  change (splitGraph Core Hosts).edgeFinset.card = _ at hedge
  have hE : (splitGraph Core Hosts).edgeFinset.card =
      Nat.card (splitGraph Core Hosts).edgeSet := by
    rw [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card]
  rw [← hE, hedge]
  unfold cost PaperIV.SplitUniformIncidence.splitA PaperIV.SplitUniformIncidence.splitB
  push_cast
  linarith

/-- At the host-free endpoint, the uniform core-`K₄` packing leaves at most
one sixth of the core edges in the fractional defect. -/
theorem F4'_splitGraph_coreOnly_le
    {Core : Finset V} (hk4 : 4 ≤ Core.card) :
    F4' (splitGraph Core ∅) ≤
      (Core.card : ℝ) * ((Core.card : ℝ) - 1) / 12 := by
  classical
  let x := PaperIV.SplitFarRounding.coreOnlyFracPacking hk4
  have hopt := PaperIV.VertexCopyMonotone.le_optVal x.toReal
  rw [← PaperIV.VertexCopyWBridge.optVal'_eq] at hopt
  have hxval : x.toReal.value =
      ((5 * (PaperIV.SplitUniformIncidence.splitA Core / 6) : ℚ) : ℝ) := by
    rw [FracPacking.toReal_value]
    exact_mod_cast PaperIV.SplitFarRounding.coreOnlyFracPacking_value hk4
  rw [hxval] at hopt
  rw [PaperIV.VertexCopyWBridge.F4'_eq_edge_sub_optVal']
  have hedge := PaperIV.SplitEdgeCount.card_graphEdges_splitGraph
    (Finset.disjoint_empty_right Core)
  change (splitGraph Core ∅).edgeFinset.card = _ at hedge
  have hE : (splitGraph Core ∅).edgeFinset.card =
      Nat.card (splitGraph Core ∅).edgeSet := by
    rw [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card]
  rw [← hE, hedge]
  simp only [Finset.card_empty, Nat.mul_zero, Nat.add_zero]
  dsimp [PaperIV.SplitUniformIncidence.splitA] at hopt
  push_cast at hopt ⊢
  rw [Nat.cast_choose_two] at hopt ⊢
  linarith

/-- For a split graph with fewer than four core vertices, the explicit
physical budget is linear in the total order. -/
theorem splitBudget_le_three_order {k h n : ℕ}
    (hk : k < 4) (hcover : k + h = n) :
    PaperIV.GatedSplitTargetBridge.splitBudget k h ≤ 3 * n := by
  interval_cases k <;> simp [PaperIV.GatedSplitTargetBridge.splitBudget] at hcover ⊢ <;> omega

/-- Below four core vertices, the literal split defect is at most `3n`. -/
theorem F4'_splitGraph_smallCore_le
    {Core Hosts : Finset V} (hd : Disjoint Core Hosts)
    (hcover : Core.card + Hosts.card = Fintype.card V)
    (hk : Core.card < 4) :
    F4' (splitGraph Core Hosts) ≤ (3 * Fintype.card V : ℕ) := by
  refine le_trans
    (PaperIV.GatedSplitTargetBridge.F4'_splitGraph_le_splitBudget hd) ?_
  exact_mod_cast splitBudget_le_three_order hk hcover

/-- A near-extremal literal split comparator lies on the critical branch and
therefore satisfies the exact quadratic residual. -/
theorem residual_sq_le_of_near_split
    {Core Hosts : Finset V} (hd : Disjoint Core Hosts)
    (hcover : Core.card + Hosts.card = Fintype.card V)
    (hk4 : 4 ≤ Core.card) (hh : 0 < Hosts.card)
    {delta : ℚ} (hn : 9 ≤ Fintype.card V)
    (hdelta : delta ≤ (Fintype.card V : ℚ) ^ 2 / 40)
    (hnear : ((PaperIV.sharpEnvelope (Fintype.card V : ℚ) - delta : ℚ) : ℝ) ≤
      F4' (splitGraph Core Hosts)) :
    (6 * (Core.card : ℚ) - 2 * (Fintype.card V : ℚ) - 1) ^ 2 ≤
      24 * delta := by
  classical
  let a : ℚ := PaperIV.SplitUniformIncidence.splitA Core
  let b : ℚ := PaperIV.SplitUniformIncidence.splitB Core Hosts
  have ha : a = (Core.card : ℚ) * ((Core.card : ℚ) - 1) / 2 := by
    dsimp [a, PaperIV.SplitUniformIncidence.splitA]
    exact Nat.cast_choose_two ℚ Core.card
  have hb : b = (Core.card : ℚ) *
      ((Fintype.card V : ℚ) - (Core.card : ℚ)) := by
    dsimp [b, PaperIV.SplitUniformIncidence.splitB]
    have hc : (Fintype.card V : ℚ) = (Core.card : ℚ) + (Hosts.card : ℚ) := by
      exact_mod_cast hcover.symm
    rw [hc]
    ring
  have hhost : (1 : ℚ) ≤ (Fintype.card V : ℚ) - (Core.card : ℚ) := by
    have hh' : (1 : ℚ) ≤ Hosts.card := by exact_mod_cast hh
    have hc : (Fintype.card V : ℚ) = (Core.card : ℚ) + (Hosts.card : ℚ) := by
      exact_mod_cast hcover.symm
    rw [hc]
    linarith
  rcases branch_trichotomy a b with hwide | hmid | hlow
  · have hf : Feasible a b a 0 0 := feasible_sub (by
        dsimp [a, PaperIV.SplitUniformIncidence.splitA]
        positivity) hwide
    have hF := F4'_splitGraph_le_cost hd hk4 hh hf
    rw [cost_sub] at hF
    have hbase : b - a = PaperIV.splitBaseline (Fintype.card V : ℚ) Core.card :=
      wide_cost_eq_baseline ha hb
    rw [hbase] at hF
    have hnearQ : PaperIV.sharpEnvelope (Fintype.card V : ℚ) - delta ≤
        PaperIV.splitBaseline (Fintype.card V : ℚ) Core.card := by
      exact_mod_cast hnear.trans hF
    exact PaperIV.critical_residual_sq_le hnearQ
  · rcases hmid with ⟨hab, hba⟩
    have hf : Feasible a b (b - a) ((2 * a - b) / 3) 0 :=
      feasible_mid hab hba
    have hF := F4'_splitGraph_le_cost hd hk4 hh hf
    rw [cost_mid] at hF
    have henv : (2 * b - a) / 3 ≤
        (4 * (Fintype.card V : ℚ) + 1) ^ 2 / 120 :=
      middle_cost_le_envelope ha hb hab hba
    have hsep := PaperIV.middleBranch_lt_sharpEnvelope_sub_of_nine
      (Fintype.card V) hn
    have hcostlt : (2 * b - a) / 3 <
        PaperIV.sharpEnvelope (Fintype.card V : ℚ) - delta := by
      have hδ : PaperIV.sharpEnvelope (Fintype.card V : ℚ) -
          (Fintype.card V : ℚ) ^ 2 / 40 ≤
          PaperIV.sharpEnvelope (Fintype.card V : ℚ) - delta := by linarith
      exact lt_of_le_of_lt henv (lt_of_lt_of_le hsep hδ)
    have hFQ : F4' (splitGraph Core Hosts) ≤ (((2 * b - a) / 3 : ℚ) : ℝ) := by
      simpa using hF
    have hcostltR : (((2 * b - a) / 3 : ℚ) : ℝ) <
        ((PaperIV.sharpEnvelope (Fintype.card V : ℚ) - delta : ℚ) : ℝ) := by
      exact_mod_cast hcostlt
    linarith
  · have hf : Feasible a b 0 (b / 3) ((a - b) / 6) :=
      feasible_low (by
        dsimp [b, PaperIV.SplitUniformIncidence.splitB]
        positivity) hlow
    have hF := F4'_splitGraph_le_cost hd hk4 hh hf
    rw [cost_low] at hF
    have henv : (a + b) / 6 ≤
        (Fintype.card V : ℚ) * ((Fintype.card V : ℚ) - 1) / 12 :=
      low_cost_le_envelope ha hb hhost
    have hsep := PaperIV.thirdBranch_lt_sharpEnvelope_sub_of_one
      (Fintype.card V) (by omega : 1 ≤ Fintype.card V)
    have hcostlt : (a + b) / 6 <
        PaperIV.sharpEnvelope (Fintype.card V : ℚ) - delta := by
      have hδ : PaperIV.sharpEnvelope (Fintype.card V : ℚ) -
          (Fintype.card V : ℚ) ^ 2 / 40 ≤
          PaperIV.sharpEnvelope (Fintype.card V : ℚ) - delta := by linarith
      exact lt_of_le_of_lt henv (lt_of_lt_of_le hsep hδ)
    have hFQ : F4' (splitGraph Core Hosts) ≤ (((a + b) / 6 : ℚ) : ℝ) := by
      simpa using hF
    have hcostltR : (((a + b) / 6 : ℚ) : ℝ) <
        ((PaperIV.sharpEnvelope (Fintype.card V : ℚ) - delta : ℚ) : ℝ) := by
      exact_mod_cast hcostlt
    linarith

/-- At order at least `100`, neither a core of size below four nor a
host-free complete graph can meet the near-extremal split threshold.  Hence
every near comparator is in the ordinary regime used by
`residual_sq_le_of_near_split`. -/
theorem residual_sq_le_of_near_split_universal
    {Core Hosts : Finset V} (hd : Disjoint Core Hosts)
    (hcover : Core.card + Hosts.card = Fintype.card V)
    {delta : ℚ} (hn : 100 ≤ Fintype.card V)
    (hdelta : delta ≤ (Fintype.card V : ℚ) ^ 2 / 40)
    (hnear : ((PaperIV.sharpEnvelope (Fintype.card V : ℚ) - delta : ℚ) : ℝ) ≤
      F4' (splitGraph Core Hosts)) :
    (6 * (Core.card : ℚ) - 2 * (Fintype.card V : ℚ) - 1) ^ 2 ≤
      24 * delta := by
  classical
  have hthreshold : (3 * (Fintype.card V : ℚ)) <
      PaperIV.sharpEnvelope (Fintype.card V : ℚ) -
        (Fintype.card V : ℚ) ^ 2 / 40 := by
    unfold PaperIV.sharpEnvelope
    have hnQ : (100 : ℚ) ≤ Fintype.card V := by exact_mod_cast hn
    nlinarith
  have hk4 : 4 ≤ Core.card := by
    by_contra hk
    have hk' : Core.card < 4 := by omega
    have hF := F4'_splitGraph_smallCore_le hd hcover hk'
    have hδ : PaperIV.sharpEnvelope (Fintype.card V : ℚ) -
        (Fintype.card V : ℚ) ^ 2 / 40 ≤
        PaperIV.sharpEnvelope (Fintype.card V : ℚ) - delta := by linarith
    have hlin : ((3 * (Fintype.card V : ℚ) : ℚ) : ℝ) <
        ((PaperIV.sharpEnvelope (Fintype.card V : ℚ) - delta : ℚ) : ℝ) := by
      exact_mod_cast lt_of_lt_of_le hthreshold hδ
    have hF' : F4' (splitGraph Core Hosts) ≤
        ((3 * (Fintype.card V : ℚ) : ℚ) : ℝ) := by
      exact_mod_cast hF
    linarith
  have hh : 0 < Hosts.card := by
    by_contra hh0
    have hhcard : Hosts.card = 0 := by omega
    have hHosts : Hosts = ∅ := Finset.card_eq_zero.mp hhcard
    subst Hosts
    have hcore : Core.card = Fintype.card V := by simpa using hcover
    have hF := F4'_splitGraph_coreOnly_le hk4
    have henv : (Core.card : ℚ) * ((Core.card : ℚ) - 1) / 12 <
        PaperIV.sharpEnvelope (Fintype.card V : ℚ) - delta := by
      rw [hcore]
      have hsep := PaperIV.thirdBranch_lt_sharpEnvelope_sub_of_one
        (Fintype.card V) (by omega : 1 ≤ Fintype.card V)
      have hδ : PaperIV.sharpEnvelope (Fintype.card V : ℚ) -
          (Fintype.card V : ℚ) ^ 2 / 40 ≤
          PaperIV.sharpEnvelope (Fintype.card V : ℚ) - delta := by linarith
      exact lt_of_lt_of_le hsep hδ
    have henvR :
        ((Core.card : ℚ) * ((Core.card : ℚ) - 1) / 12 : ℝ) <
          ((PaperIV.sharpEnvelope (Fintype.card V : ℚ) - delta : ℚ) : ℝ) := by
      exact_mod_cast henv
    exact (not_lt_of_ge (hnear.trans hF)) henvR
  exact residual_sq_le_of_near_split hd hcover hk4 hh (by omega) hdelta hnear

end PaperIV.SplitComparatorResidual
