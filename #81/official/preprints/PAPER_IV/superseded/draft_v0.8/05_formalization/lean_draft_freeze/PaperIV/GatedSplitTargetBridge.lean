import PaperIV.GatedTerminalSplit
import PaperIV.VertexCopyWBridge
import PaperIV.SplitTriangleFactorHighHost

/-!
# Gate (1): a quantitative target bridge for the gated fine-copy stabilization

`GatedTerminalSplit.exists_split_terminal_symmetrizationPath` produces, for every finite
chordal graph `G`, a gated fine-copy path to a literal
`SplitUniformIncidence.splitGraph` terminal with `F4' G ≤ F4' H`, and
`VertexCopyWBridge.F4'_le_completion_card_of_physical` bounds `F4'` of any graph
by the completed count of any of its literal `K3`/`K4` packings.

This module composes the two into one *numerical* statement: the mixed
fractional defect of the original chordal graph is bounded by an explicit
arithmetic function of the terminal core and host sizes, hence by every target
`Q` dominating that function.

The explicit budget `splitBudget k h` is:

* for an **even** core, the exact even-core split-terminal completion count
  `C(k,2) + k * (h - (k-1))` of `SplitTriangleFactorHighHost`, available for
  *every* host count;
* for an **odd** core, the even-core count of the core with one vertex deleted,
  plus the literal linear residue `(k-1) + h` of the deleted vertex's edges.

Nothing is assumed: the gate, the terminal identification and the packings are
all the existing literal constructions.  The direction of the resulting bound is
the one that the `W*` ledger actually supports: `F4'` is a *lower* bound for
completed packing counts, so this bridge constrains the defect of `G`, it does
not yet produce a partition of `G` (see `PaperIV.CopyTransportLoss`).
-/

namespace PaperIV.GatedSplitTargetBridge

open Finset PaperIV.Model PaperIV.PhysicalCompletion
open PaperIV.SplitUniformIncidence PaperIV.SplitEdgeCount
open PaperIV.SplitTriangleFactorHighHost
open PaperIV.VertexCopyGate PaperIV.VertexCopyWBridge
open PaperIV.TerminalSplitAdapter

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Two generic facts about literal packings -/

omit [Fintype V] in
/-- The empty family is a literal `K3`/`K4` packing. -/
theorem isK34Packing_empty (G : SimpleGraph V) [DecidableRel G.Adj] :
    IsK34Packing G (∅ : Finset (Finset V)) :=
  { toIsPacking := isPacking_empty, big := by simp }

/-- `F4'` never exceeds the number of edges: the empty packing completes to the
all-`K2` partition. -/
theorem F4'_le_card_graphEdges (G : SimpleGraph V) [DecidableRel G.Adj] :
    F4' G ≤ ((graphEdges G).card : ℝ) := by
  have h := F4'_le_completion_card_of_physical (isK34Packing_empty G)
  have hc : (completion G (∅ : Finset (Finset V))).card = (graphEdges G).card := by
    rw [card_completion (isK34Packing_empty G)]
    simp [uncoveredEdges, coveredEdges]
  rwa [hc] at h

/-- A literal `K3`/`K4` packing of a subgraph is one of the ambient graph, and
its completed count grows by at most the number of new edges. -/
theorem isK34Packing_and_card_completion_le_of_le {G G' : SimpleGraph V}
    [DecidableRel G.Adj] [DecidableRel G'.Adj] (hle : G ≤ G')
    {P : Finset (Finset V)} (hP : IsK34Packing G P) :
    IsK34Packing G' P ∧
      (completion G' P).card ≤
        (completion G P).card + ((graphEdges G').card - (graphEdges G).card) := by
  classical
  have hsub : graphEdges G ⊆ graphEdges G' := by
    intro e he
    rw [mem_graphEdges] at he ⊢
    exact SimpleGraph.edgeSet_mono hle he
  have hP' : IsK34Packing G' P :=
    { pieces := fun s hs => ⟨(hP.pieces s hs).clique.mono hle, (hP.pieces s hs).kind⟩
      edgeDisjoint := hP.edgeDisjoint
      big := hP.big }
  refine ⟨hP', ?_⟩
  have hunion : uncoveredEdges G' P ⊆ uncoveredEdges G P ∪ (graphEdges G' \ graphEdges G) := by
    intro e he
    rw [mem_uncoveredEdges] at he
    by_cases hE : e ∈ graphEdges G
    · exact Finset.mem_union_left _ (mem_uncoveredEdges.mpr ⟨hE, he.2⟩)
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨he.1, hE⟩)
  have hsdiff : (graphEdges G' \ graphEdges G).card + (graphEdges G).card
      = (graphEdges G').card := Finset.card_sdiff_add_card_eq_card hsub
  have hcard : (uncoveredEdges G' P).card ≤
      (uncoveredEdges G P).card + ((graphEdges G').card - (graphEdges G).card) := by
    have hstep : (uncoveredEdges G' P).card
        ≤ (uncoveredEdges G P).card + (graphEdges G' \ graphEdges G).card :=
      le_trans (Finset.card_le_card hunion) (Finset.card_union_le _ _)
    omega
  rw [card_completion hP, card_completion hP']
  omega

/-! ## The split graph is monotone in its core -/

omit [Fintype V] in
/-- Enlarging the core enlarges the split graph. -/
theorem splitGraph_mono_core {Core Core' Hosts : Finset V} (h : Core' ⊆ Core) :
    splitGraph Core' Hosts ≤ splitGraph Core Hosts := by
  rintro x y ⟨hne, hcase⟩
  refine ⟨hne, ?_⟩
  rcases hcase with ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩
  · exact Or.inl ⟨h hx, h hy⟩
  · exact Or.inr (Or.inl ⟨h hx, hy⟩)
  · exact Or.inr (Or.inr ⟨hx, h hy⟩)

/-! ## The explicit split-terminal budget -/

/-- The explicit completion budget of a split terminal with core size `k` and
host size `h`: the exact even-core split-terminal count, plus (for an odd core)
the literal linear residue of one deleted core vertex. -/
def splitBudget (k h : ℕ) : ℕ :=
  if k % 2 = 0 then k.choose 2 + k * (h - (k - 1))
  else (k - 1).choose 2 + (k - 1) * (h - (k - 2)) + ((k - 1) + h)

/-- **Odd core.**  Deleting one core vertex reduces to the even-core
construction and costs exactly the deleted vertex's `(k-1) + h` edges. -/
theorem exists_split_packing_odd {Core Hosts : Finset V} (hd : Disjoint Core Hosts)
    {n : ℕ} (hk : Core.card = 2 * n + 3) :
    ∃ P : Finset (Finset V), IsK34Packing (splitGraph Core Hosts) P ∧
      (completion (splitGraph Core Hosts) P).card ≤
        ((2 * n + 2).choose 2 + (2 * n + 2) * (Hosts.card - (2 * n + 1))
          + ((2 * n + 2) + Hosts.card)) := by
  classical
  have hpos : 0 < Core.card := by omega
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
  set Core' := Core.erase x with hCore'
  have hsub : Core' ⊆ Core := Finset.erase_subset _ _
  have hk' : Core'.card = 2 * n + 2 := by
    rw [hCore', Finset.card_erase_of_mem hx, hk]
    omega
  have hd' : Disjoint Core' Hosts := Finset.disjoint_of_subset_left hsub hd
  obtain ⟨P, hP, -, -, hcount⟩ := exists_split_completion_card hd' hk'
  obtain ⟨hP', hle⟩ :=
    isK34Packing_and_card_completion_le_of_le (splitGraph_mono_core hsub) hP
  have hE : (graphEdges (splitGraph Core Hosts)).card
      = Core.card.choose 2 + Core.card * Hosts.card := card_graphEdges_splitGraph hd
  have hE' : (graphEdges (splitGraph Core' Hosts)).card
      = Core'.card.choose 2 + Core'.card * Hosts.card := card_graphEdges_splitGraph hd'
  have hchoose : Core.card.choose 2 = Core'.card.choose 2 + (2 * n + 2) := by
    have hpascal : (2 * n + 3).choose 2 = (2 * n + 2) + (2 * n + 2).choose 2 := by
      have h := Nat.choose_succ_succ (2 * n + 2) 1
      simpa using h
    rw [hk, hk']
    omega
  have hdiff : (graphEdges (splitGraph Core Hosts)).card
      - (graphEdges (splitGraph Core' Hosts)).card = (2 * n + 2) + Hosts.card := by
    rw [hE, hE', hchoose, hk, hk']
    have : (2 * n + 3) * Hosts.card = (2 * n + 2) * Hosts.card + Hosts.card := by ring
    omega
  have hbound : (completion (splitGraph Core Hosts) P).card
      ≤ ((2 * n + 2).choose 2 + (2 * n + 2) * (Hosts.card - (2 * n + 1))
          + ((2 * n + 2) + Hosts.card)) := by
    rw [hdiff] at hle
    rw [hcount, hk'] at hle
    exact hle
  exact ⟨P, hP', hbound⟩

/-- **The explicit terminal packing, for every core and host size.**  Every
split graph carries a literal `K3`/`K4` packing whose completion count is at
most `splitBudget`. -/
theorem exists_split_packing_le_splitBudget {Core Hosts : Finset V}
    (hd : Disjoint Core Hosts) :
    ∃ P : Finset (Finset V), IsK34Packing (splitGraph Core Hosts) P ∧
      (completion (splitGraph Core Hosts) P).card ≤ splitBudget Core.card Hosts.card := by
  classical
  rcases Nat.lt_or_ge Core.card 2 with hsmall | hbig
  · -- degenerate cores: the all-`K2` partition already realizes the budget
    have hE : (graphEdges (splitGraph Core Hosts)).card
        = Core.card.choose 2 + Core.card * Hosts.card := card_graphEdges_splitGraph hd
    have hbud : splitBudget Core.card Hosts.card
        = Core.card.choose 2 + Core.card * Hosts.card := by
      interval_cases h : Core.card <;> simp [splitBudget]
    refine ⟨∅, isK34Packing_empty _, ?_⟩
    rw [card_completion (isK34Packing_empty (splitGraph Core Hosts))]
    simp only [Finset.card_empty, Nat.zero_add, uncoveredEdges, coveredEdges,
      Finset.biUnion_empty, Finset.sdiff_empty]
    rw [hbud, hE]
  · rcases Nat.even_or_odd Core.card with hpar | hpar
    · obtain ⟨n, hn⟩ : ∃ n, Core.card = 2 * n + 2 := by
        obtain ⟨m, hm⟩ := hpar
        exact ⟨m - 1, by omega⟩
      obtain ⟨P, hP, -, -, hcount⟩ := exists_split_completion_card hd hn
      refine ⟨P, hP, ?_⟩
      have hk1 : Core.card - 1 = 2 * n + 1 := by omega
      rw [hcount, splitBudget, if_pos (by omega), hk1]
    · obtain ⟨n, hn⟩ : ∃ n, Core.card = 2 * n + 3 := by
        obtain ⟨m, hm⟩ := hpar
        exact ⟨m - 1, by omega⟩
      obtain ⟨P, hP, hcount⟩ := exists_split_packing_odd hd hn
      refine ⟨P, hP, ?_⟩
      refine le_trans hcount (le_of_eq ?_)
      have hk1 : Core.card - 1 = 2 * n + 2 := by omega
      have hk2 : Core.card - 2 = 2 * n + 1 := by omega
      rw [splitBudget, if_neg (by omega), hk1, hk2]

/-- **The explicit terminal budget, for every core and host size.** -/
theorem F4'_splitGraph_le_splitBudget {Core Hosts : Finset V} (hd : Disjoint Core Hosts) :
    F4' (splitGraph Core Hosts) ≤ ((splitBudget Core.card Hosts.card : ℕ) : ℝ) := by
  classical
  obtain ⟨P, hP, hcount⟩ := exists_split_packing_le_splitBudget hd
  refine le_trans (F4'_le_completion_card_of_physical hP) ?_
  exact_mod_cast Nat.cast_le.mpr hcount

/-! ## The gate composed with the budget -/

/-- **Gate (1).**  Every finite chordal graph reaches, by gated fine copies, a
literal split terminal whose explicit completion budget dominates the mixed
fractional defect of the original graph. -/
theorem exists_split_terminal_F4'_le_splitBudget (G : SimpleGraph V)
    (hG : PaperIV.IsChordal G) :
    ∃ (H : SimpleGraph V) (C : Set V),
      SymmetrizationPath G H ∧ PaperIV.IsChordal H ∧
      H = splitGraph (coreFinset C) (hostFinset C) ∧
      F4' G ≤ F4' H ∧
      F4' G ≤ ((splitBudget (coreFinset C).card (hostFinset C).card : ℕ) : ℝ) := by
  obtain ⟨H, C, hreach, hchord, hsplit, hF4⟩ :=
    PaperIV.GatedTerminalSplit.exists_split_terminal_symmetrizationPath G hG
  refine ⟨H, C, hreach, hchord, hsplit, hF4, ?_⟩
  have hbudget := F4'_splitGraph_le_splitBudget (core_host_disjoint C)
  rw [← hsplit] at hbudget
  exact le_trans hF4 hbudget

/-- **Gate (1), target form.**  Any numerical target dominated by the explicit
split-terminal budget dominates the mixed fractional defect of the original
chordal graph. -/
theorem exists_split_terminal_F4'_le_target (G : SimpleGraph V)
    (hG : PaperIV.IsChordal G) :
    ∃ (H : SimpleGraph V) (C : Set V),
      SymmetrizationPath G H ∧ PaperIV.IsChordal H ∧
      H = splitGraph (coreFinset C) (hostFinset C) ∧
      ∀ Q : ℝ, ((splitBudget (coreFinset C).card (hostFinset C).card : ℕ) : ℝ) ≤ Q →
        F4' G ≤ Q := by
  obtain ⟨H, C, hreach, hchord, hsplit, -, hbudget⟩ :=
    exists_split_terminal_F4'_le_splitBudget G hG
  exact ⟨H, C, hreach, hchord, hsplit, fun Q hQ => le_trans hbudget hQ⟩

end PaperIV.GatedSplitTargetBridge


