import PaperIV.RD09RootFactorPhase
import PaperIV.TerminalLedger

/-!
# RD09 terminal assembly: from the literal two-phase root-factor packing to the paid terminal

This module closes the bookkeeping gap between

* the *literal* physical construction of `PaperIV.RD09RootFactorPhase`, i.e. the union
  `multiLiftedPacking z E ∪ phaseTwoPacking hub base` of the phase-I multi-host triangle
  lift and the phase-II root-factor hub pieces, and
* the *canonical accounting interface* `PaperIV.TerminalLedger.PhysicalTerminal`, which
  pays the RD09 terminal budget.

Nothing about the packing, the `K3`/`K4` status of the pieces, or the cross-phase
compatibility is postulated here:

* the packing property is derived from
  `PaperIV.RD09RootFactorPhase.isPacking_union_rootFactorPhases`;
* the `K3`/`K4` status is derived from the literal phase constructions (a phase-I piece is
  a triangle, a phase-II piece is a hub set plus a base edge, so it has `3` or `4`
  vertices).

The only data that the module *does* accept as input is the purely numerical ledger of
the RD09 budget (`base`, `missing`, `rootLoss`, `removed`, `recovered` together with the
ledger equality and the two RD09 inequalities), packaged as `RD09NumericLedger`, and –
where an exact global partition is wanted – one explicitly visible global coverage
hypothesis `hcov`.  Consequently the remaining obligations of the near-regime route are
isolated to: host selection (the phase data itself), global coverage, and the numerical
counts.
-/

namespace PaperIV.RD09TerminalAssembly

open Finset PaperIV.Model PaperIV.ExteriorTriangleLift PaperIV.MultiHostTriangleLift
open PaperIV.PhysicalCompletion PaperIV.RD09PhaseII PaperIV.RD09RootFactorPhase

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
variable {z : I → V} {E : I → Finset (Sym2 V)}
variable {root : Finset V} {hub : J → Finset V} {base : J → Sym2 V}

/-! ## `K3`/`K4` status of the two literal phases -/

omit [DecidableEq I] in
/-- Every phase-I piece is a literal triangle, hence has exactly three vertices. -/
theorem card_eq_three_of_mem_multiLiftedPacking (h1 : IsMultiExteriorHub G z E)
    {s : Finset V} (hs : s ∈ multiLiftedPacking z E) : s.card = 3 := by
  rw [mem_multiLiftedPacking] at hs
  obtain ⟨i, e, he, rfl⟩ := hs
  exact card_triangle (not_isDiag_of_mem_graphEdges G ((h1.hub i).edges e he))
    (notMem_of_hub (h1.hub i) he)

omit [DecidableEq J] in
/-- Every phase-II piece has three vertices (one-vertex hub) or four vertices
(two-vertex hub). -/
theorem card_eq_three_or_four_of_mem_phaseTwoPacking
    (h : IsRootFactorFamily G root hub base) {s : Finset V}
    (hs : s ∈ phaseTwoPacking hub base) : s.card = 3 ∨ s.card = 4 := by
  rw [mem_phaseTwoPacking] at hs
  obtain ⟨j, rfl⟩ := hs
  rcases h.hubCard j with hj | hj
  · exact Or.inl (h.isPhaseTwoFamily.card_piece_eq_three hj)
  · exact Or.inr (h.isPhaseTwoFamily.card_piece_eq_four hj)

omit [DecidableEq I] [DecidableEq J] in
/-- Every piece of the assembled two-phase family is a `K3` or a `K4`. -/
theorem card_eq_three_or_four_of_mem_union (h1 : IsMultiExteriorHub G z E)
    (h : IsRootFactorFamily G root hub base) {s : Finset V}
    (hs : s ∈ multiLiftedPacking z E ∪ phaseTwoPacking hub base) :
    s.card = 3 ∨ s.card = 4 := by
  rcases Finset.mem_union.mp hs with hs | hs
  · exact Or.inl (card_eq_three_of_mem_multiLiftedPacking h1 hs)
  · exact card_eq_three_or_four_of_mem_phaseTwoPacking h hs

omit [DecidableEq J] in
/-- **The structural adapter.**  The literal union of the phase-I multi-host triangle lift
and the phase-II root-factor pieces is a `K3`/`K4` packing of `G`: the packing property
comes from `isPacking_union_rootFactorPhases`, the `K3`/`K4` status from the literal
phase constructions. -/
theorem isK34Packing_union_rootFactorPhases (h1 : IsMultiExteriorHub G z E)
    (h : IsRootFactorFamily G root hub base) (hs : IsRootHostSeparated z E root hub) :
    IsK34Packing G (multiLiftedPacking z E ∪ phaseTwoPacking hub base) :=
  { isPacking_union_rootFactorPhases h1 h hs with
    big := fun _ hmem => card_eq_three_or_four_of_mem_union h1 h hmem }

/-! ## The remaining numerical ledger -/

/-- The purely numerical RD09 ledger attached to a literal packing `P`: the budget
displacement data together with the ledger equality and the two RD09 inequalities.
This is the *only* thing the assembly below assumes; it postulates neither a packing nor
any coverage or compatibility statement. -/
structure RD09NumericLedger (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finset (Finset V)) where
  /-- the canonical base count -/
  base : ℚ
  /-- the missing-edge displacement -/
  missing : ℚ
  /-- the root-factor loss -/
  rootLoss : ℚ
  /-- the number of removed pieces -/
  removed : ℚ
  /-- the number of recovered pieces -/
  recovered : ℚ
  /-- the two-phase ledger equality for the completed packing -/
  ledger : ((completion G P).card : ℚ) =
    base + missing - rootLoss - 2 * removed + 2 * recovered
  /-- the RD09 lower bound on removed pieces -/
  removed_lower : (40 : ℚ) / 73 * missing - (3 : ℚ) / 40 * rootLoss ≤ removed
  /-- the RD09 upper bound on recovered pieces -/
  recovered_upper : recovered ≤ (7 : ℚ) / 40 * rootLoss + removed / 25

/-- **The assembly.**  A literal RD09 two-phase root-factor configuration together with
its numerical ledger *is* a `PaperIV.TerminalLedger.PhysicalTerminal`. -/
def toPhysicalTerminal (h1 : IsMultiExteriorHub G z E)
    (h : IsRootFactorFamily G root hub base) (hs : IsRootHostSeparated z E root hub)
    (L : RD09NumericLedger G (multiLiftedPacking z E ∪ phaseTwoPacking hub base)) :
    PaperIV.TerminalLedger.PhysicalTerminal (G := G) where
  packing := multiLiftedPacking z E ∪ phaseTwoPacking hub base
  isK34 := isK34Packing_union_rootFactorPhases h1 h hs
  base := L.base
  missing := L.missing
  rootLoss := L.rootLoss
  removed := L.removed
  recovered := L.recovered
  ledger := L.ledger
  removed_lower := L.removed_lower
  recovered_upper := L.recovered_upper

omit [DecidableEq J] in
@[simp] theorem toPhysicalTerminal_packing (h1 : IsMultiExteriorHub G z E)
    (h : IsRootFactorFamily G root hub base) (hs : IsRootHostSeparated z E root hub)
    (L : RD09NumericLedger G (multiLiftedPacking z E ∪ phaseTwoPacking hub base)) :
    (toPhysicalTerminal h1 h hs L).packing
      = multiLiftedPacking z E ∪ phaseTwoPacking hub base := rfl

/-! ## The terminal consequences, stated directly for the two-phase configuration -/

section Consequences

variable (h1 : IsMultiExteriorHub G z E) (h : IsRootFactorFamily G root hub base)
  (hs : IsRootHostSeparated z E root hub)
  (L : RD09NumericLedger G (multiLiftedPacking z E ∪ phaseTwoPacking hub base))
include h1 h hs

omit [DecidableEq J] in
/-- The completion of the literal two-phase packing is an exact physical partition. -/
theorem isExactPartition_completion_union :
    IsExactPartition G (completion G (multiLiftedPacking z E ∪ phaseTwoPacking hub base)) :=
  isExactPartition_completion (isPacking_union_rootFactorPhases h1 h hs)

include L in
omit [DecidableEq J] in
/-- The strong exact-piece RD09 estimate for the two-phase configuration. -/
theorem count_le_exact_piece_bound :
    ((completion G (multiLiftedPacking z E ∪ phaseTwoPacking hub base)).card : ℚ) ≤
      L.base - (19 : ℚ) / 365 * L.missing - (253 : ℚ) / 500 * L.rootLoss :=
  (toPhysicalTerminal h1 h hs L).count_le_exact_piece_bound

include L in
omit [DecidableEq J] in
/-- The two-phase configuration pays the RD09 terminal budget. -/
theorem count_le_paid (hmissing : 0 ≤ L.missing) (hrootLoss : 0 ≤ L.rootLoss) :
    ((completion G (multiLiftedPacking z E ∪ phaseTwoPacking hub base)).card : ℚ) ≤
      L.base - L.missing / 20 - L.rootLoss / 2 :=
  (toPhysicalTerminal h1 h hs L).count_le_paid hmissing hrootLoss

include L in
omit [DecidableEq J] in
/-- The two-phase configuration is a direct input to the global factor-20 defect budget. -/
theorem defects_le_twenty_total {M U : ℚ} (hbase : 0 ≤ M - L.base)
    (hmissing : 0 ≤ L.missing) (hrootLoss : 0 ≤ L.rootLoss) :
    L.missing + L.rootLoss ≤ 20 *
      (PaperIV.CanonicalBudget.historicalDeficit M U +
        PaperIV.CanonicalBudget.geometricDeficit U
          ((completion G (multiLiftedPacking z E ∪ phaseTwoPacking hub base)).card : ℚ)) :=
  (toPhysicalTerminal h1 h hs L).defects_le_twenty_total hbase hmissing hrootLoss

end Consequences

/-! ## Exact global coverage: the visible hypothesis and its consequence -/

/-- A packing that already covers every edge equals its own completion. -/
theorem completion_eq_self_of_covers {P : Finset (Finset V)}
    (hcov : coveredEdges P = graphEdges G) : completion G P = P := by
  have huncov : uncoveredEdges G P = ∅ := by
    rw [uncoveredEdges, hcov, Finset.sdiff_self]
  rw [completion, huncov, Finset.image_empty, Finset.union_empty]

omit [DecidableEq I] [DecidableEq J] in
/-- Under the single visible global coverage hypothesis, the literal two-phase packing is
itself an exact partition: no `K2` completion pieces are created. -/
theorem completion_eq_union_of_covers
    (hcov : coveredEdges (multiLiftedPacking z E) ∪ coveredEdges (phaseTwoPacking hub base)
      = graphEdges G) :
    completion G (multiLiftedPacking z E ∪ phaseTwoPacking hub base)
      = multiLiftedPacking z E ∪ phaseTwoPacking hub base := by
  refine completion_eq_self_of_covers ?_
  rw [coveredEdges_union_phases]
  exact hcov

omit [DecidableEq I] [DecidableEq J] in
/-- Under exact global coverage the terminal piece count is the literal two-phase count:
one piece per phase-I base edge plus one piece per root-factor index. -/
theorem card_completion_of_covers (h1 : IsMultiExteriorHub G z E)
    (h : IsRootFactorFamily G root hub base) (hs : IsRootHostSeparated z E root hub)
    (hcov : coveredEdges (multiLiftedPacking z E) ∪ coveredEdges (phaseTwoPacking hub base)
      = graphEdges G) :
    (completion G (multiLiftedPacking z E ∪ phaseTwoPacking hub base)).card
      = (∑ i, (E i).card) + Fintype.card J := by
  rw [completion_eq_union_of_covers hcov]
  exact card_union_rootFactorPhases h1 h hs

omit [DecidableEq J] in
/-- Under exact global coverage the edge count of `G` is determined by the literal
two-phase ledger: pieces plus gains. -/
theorem card_graphEdges_of_covers (h1 : IsMultiExteriorHub G z E)
    (h : IsRootFactorFamily G root hub base) (hs : IsRootHostSeparated z E root hub)
    (hcov : coveredEdges (multiLiftedPacking z E) ∪ coveredEdges (phaseTwoPacking hub base)
      = graphEdges G) :
    (graphEdges G).card = ((∑ i, (E i).card) + Fintype.card J) +
      (2 * (∑ i, (E i).card) + (2 * (k3Indices hub).card + 5 * (k4Indices hub).card)) := by
  have hexact : IsExactPartition G (multiLiftedPacking z E ∪ phaseTwoPacking hub base) :=
    isExactPartition_union_rootFactorPhases h1 h hs hcov
  have hcard := hexact.card_add_totalGain
  rw [card_union_rootFactorPhases h1 h hs, totalGain_union_rootFactorPhases h1 h hs] at hcard
  exact hcard.symm

end PaperIV.RD09TerminalAssembly


