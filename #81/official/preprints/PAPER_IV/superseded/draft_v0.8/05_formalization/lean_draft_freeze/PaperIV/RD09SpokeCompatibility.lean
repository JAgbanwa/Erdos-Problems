import PaperIV.RD09PhaseII
import PaperIV.PhysicalCompletion
import PaperIV.RD09PhysicalLedger

/-!
# RD09 cross-phase compatibility in the orientation used by H1

In H1, phase-I hosts are root vertices and phase-I bases are exterior edges.
Phase II reverses the roles: its singleton hubs are exterior candidates and its
bases are root edges.  Consequently the older sufficient condition
`RD09PhaseII.IsPhaseCompatible.hostSep` is intentionally too strong: a phase-I
host is allowed to be an endpoint of a phase-II base.

The only dangerous configuration is the simultaneous occurrence of a root
`z i` on the phase-II base and an endpoint of the phase-I base in the
phase-II hub.  That would reuse the spoke joining those two vertices.  The
structure below records exactly that obstruction, together with the literal
root/exterior separation.  It is the resource-level adapter needed by the
actual L1--L2 orientation.
-/

namespace PaperIV.RD09SpokeCompatibility

open Finset PaperIV.Model PaperIV.ExteriorTriangleLift
open PaperIV.MultiHostTriangleLift PaperIV.RD09PhaseII

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
variable {z : I → V} {E : I → Finset (Sym2 V)}
variable {hub : J → Finset V} {base : J → Sym2 V}

/-- Literal cross-phase data in the H1 orientation.

`spokeSafe` says precisely that, when the phase-I root lies on a phase-II
root base, the exterior endpoint set of the phase-I edge avoids the chosen
phase-II candidate hub. -/
structure IsSpokeCompatible (z : I → V) (E : I → Finset (Sym2 V))
    (hub : J → Finset V) (base : J → Sym2 V) : Prop where
  /-- roots are not exterior candidate hubs -/
  hostNotHub : ∀ i j, z i ∉ hub j
  /-- exterior phase-I bases avoid root phase-II bases -/
  baseSep : ∀ i j, ∀ e ∈ E i, Disjoint e.toFinset (base j).toFinset
  /-- phase II uses singleton hubs (the mixed K4 extension is not needed here) -/
  hubCard : ∀ j, (hub j).card ≤ 1
  /-- the only possible shared spoke is explicitly forbidden -/
  spokeSafe : ∀ i j, ∀ e ∈ E i, z i ∈ base j → Disjoint e.toFinset (hub j)

namespace IsSpokeCompatible

variable (hc : IsSpokeCompatible z E hub base)
include hc

omit [Fintype V] [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
/-- A phase-I triangle and a phase-II triangle meet in at most one vertex,
although they may share their root vertex. -/
theorem card_inter_le_one {i : I} {j : J} {e : Sym2 V} (he : e ∈ E i) :
    (triangle (z i) e ∩ piece hub base j).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro v hv w hw
  have classify : ∀ {x : V}, x ∈ triangle (z i) e ∩ piece hub base j →
      (x = z i ∧ z i ∈ base j) ∨ (x ∈ e ∧ x ∈ hub j) := by
    intro x hx
    rw [Finset.mem_inter, mem_triangle, RD09PhaseII.mem_piece] at hx
    rcases hx with ⟨hxz | hxe, hxh | hxb⟩
    · exact absurd (hxz ▸ hxh) (hc.hostNotHub i j)
    · exact Or.inl ⟨hxz, hxz ▸ hxb⟩
    · exact Or.inr ⟨hxe, hxh⟩
    · exact False.elim (Finset.disjoint_left.mp (hc.baseSep i j e he)
        (Sym2.mem_toFinset.mpr hxe) (Sym2.mem_toFinset.mpr hxb))
  rcases classify hv with ⟨hvz, hzbase⟩ | ⟨hve, hvhub⟩
  · rcases classify hw with ⟨hwz, -⟩ | ⟨hwe, hwhub⟩
    · exact hvz.trans hwz.symm
    · exact False.elim (Finset.disjoint_left.mp (hc.spokeSafe i j e he hzbase)
        (Sym2.mem_toFinset.mpr hwe) hwhub)
  · rcases classify hw with ⟨hwz, hzbase⟩ | ⟨-, hwhub⟩
    · exact False.elim (Finset.disjoint_left.mp (hc.spokeSafe i j e he hzbase)
        (Sym2.mem_toFinset.mpr hve) hvhub)
    · have hle := hc.hubCard j
      rw [Finset.card_le_one] at hle
      exact hle v hvhub w hwhub

omit [Fintype V] [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
/-- The corresponding literal physical resources are disjoint. -/
theorem pieceEdges_disjoint_cross {i : I} {j : J} {e : Sym2 V} (he : e ∈ E i) :
    Disjoint (pieceEdges (triangle (z i) e)) (pieceEdges (piece hub base j)) :=
  RD09PhaseII.pieceEdges_disjoint_of_card_inter_le_one (hc.card_inter_le_one he)

omit [Fintype V] [DecidableEq I] [DecidableEq J] in
theorem pieceEdges_disjoint_phases :
    ∀ s ∈ multiLiftedPacking z E, ∀ t ∈ phaseTwoPacking hub base,
      Disjoint (pieceEdges s) (pieceEdges t) := by
  intro s hs t ht
  rw [mem_multiLiftedPacking] at hs
  rw [mem_phaseTwoPacking] at ht
  obtain ⟨i, e, he, rfl⟩ := hs
  obtain ⟨j, rfl⟩ := ht
  exact hc.pieceEdges_disjoint_cross he

omit [DecidableEq J] in
/-- The two literal phases form a packing in the actual H1 orientation. -/
theorem isPacking_union_phases (h1 : IsMultiExteriorHub G z E)
    (h2 : IsPhaseTwoFamily G hub base) :
    IsPacking G (multiLiftedPacking z E ∪ phaseTwoPacking hub base) :=
  PaperIV.PackingUnion.isPacking_union (isPacking_multiLiftedPacking h1)
    h2.isPacking_phaseTwoPacking hc.pieceEdges_disjoint_phases

omit [DecidableEq J] in
/-- The same literal union is a `K3`/`K4` packing.  In the H1 use all
phase-II hubs are singletons, but retaining the two-vertex alternative makes
the adapter reusable. -/
theorem isK34Packing_union_phases (h1 : IsMultiExteriorHub G z E)
    (h2 : IsPhaseTwoFamily G hub base) :
    PaperIV.PhysicalCompletion.IsK34Packing G
      (multiLiftedPacking z E ∪ phaseTwoPacking hub base) := by
  refine { hc.isPacking_union_phases h1 h2 with big := ?_ }
  intro t ht
  rcases Finset.mem_union.mp ht with ht | ht
  · exact Or.inl
      (PaperIV.RD09TerminalAssembly.card_eq_three_of_mem_multiLiftedPacking h1 ht)
  · rw [mem_phaseTwoPacking] at ht
    obtain ⟨j, rfl⟩ := ht
    rcases h2.hubCard j with hj | hj
    · exact Or.inl (h2.card_piece_eq_three hj)
    · exact Or.inr (h2.card_piece_eq_four hj)

omit [DecidableEq I] [DecidableEq J] in
theorem disjoint_families (h1 : IsMultiExteriorHub G z E) :
    Disjoint (multiLiftedPacking z E) (phaseTwoPacking hub base) := by
  rw [Finset.disjoint_left]
  intro s hs hs2
  have hdisj := hc.pieceEdges_disjoint_phases s hs s hs2
  rw [mem_multiLiftedPacking] at hs
  obtain ⟨i, e, he, rfl⟩ := hs
  have hmem : e ∈ pieceEdges (triangle (z i) e) :=
    base_mem_pieceEdges_triangle (h1.hub i) he
  exact Finset.disjoint_left.mp hdisj hmem hmem

omit [DecidableEq I] [DecidableEq J] in
/-- Exact additive piece ledger for the two phases. -/
theorem card_union_phases (h1 : IsMultiExteriorHub G z E)
    (h2 : IsPhaseTwoFamily G hub base) :
    (multiLiftedPacking z E ∪ phaseTwoPacking hub base).card
      = (∑ i, (E i).card) + Fintype.card J := by
  rw [Finset.card_union_of_disjoint (hc.disjoint_families h1),
    card_multiLiftedPacking h1, h2.card_phaseTwoPacking]

/-- Build the canonical physical-account object from the literal two-phase
packing and literal finite account families.  This is the final type-level
adapter: unlike a numeric ledger, none of the four accounts is an anonymous
rational parameter. -/
def physicalAccounts {n p : ℚ} {B : ℕ}
    (hbase : (B : ℚ) = PaperIV.splitBaseline n p)
    (missingEdges rootLossEdges : Finset (Sym2 V))
    (removedPieces recoveredPieces : Finset (Finset V))
    (hcount :
      (PaperIV.PhysicalCompletion.completion G
        (multiLiftedPacking z E ∪ phaseTwoPacking hub base)).card
          + rootLossEdges.card + 2 * removedPieces.card
        = B + missingEdges.card + 2 * recoveredPieces.card)
    (L9 : 1600 * missingEdges.card
      ≤ 2920 * removedPieces.card + 219 * rootLossEdges.card)
    (L10 : 200 * recoveredPieces.card
      ≤ 35 * rootLossEdges.card + 8 * removedPieces.card) :
    PaperIV.RD09PhysicalLedger.PhysicalAccounts G
      (multiLiftedPacking z E ∪ phaseTwoPacking hub base) where
  order := n
  split := p
  baseCount := B
  base_eq := hbase
  missingEdges := missingEdges
  rootLossEdges := rootLossEdges
  removedPieces := removedPieces
  recoveredPieces := recoveredPieces
  L3 := hcount
  L9 := L9
  L10 := L10

/-- End-to-end paid conclusion from the correctly oriented literal phases and
their physical accounts. -/
theorem completion_card_le_paid (h1 : IsMultiExteriorHub G z E)
    (h2 : IsPhaseTwoFamily G hub base)
    {n p : ℚ} {B : ℕ}
    (hbase : (B : ℚ) = PaperIV.splitBaseline n p)
    (missingEdges rootLossEdges : Finset (Sym2 V))
    (removedPieces recoveredPieces : Finset (Finset V))
    (hcount :
      (PaperIV.PhysicalCompletion.completion G
        (multiLiftedPacking z E ∪ phaseTwoPacking hub base)).card
          + rootLossEdges.card + 2 * removedPieces.card
        = B + missingEdges.card + 2 * recoveredPieces.card)
    (L9 : 1600 * missingEdges.card
      ≤ 2920 * removedPieces.card + 219 * rootLossEdges.card)
    (L10 : 200 * recoveredPieces.card
      ≤ 35 * rootLossEdges.card + 8 * removedPieces.card) :
    PaperIV.PhysicalCompletion.IsK34Packing G
        (multiLiftedPacking z E ∪ phaseTwoPacking hub base) ∧
      ((PaperIV.PhysicalCompletion.completion G
        (multiLiftedPacking z E ∪ phaseTwoPacking hub base)).card : ℚ)
        ≤ PaperIV.splitBaseline n p
          - (missingEdges.card : ℚ) / 20 - (rootLossEdges.card : ℚ) / 2 := by
  refine ⟨hc.isK34Packing_union_phases h1 h2, ?_⟩
  exact PaperIV.RD09PhysicalLedger.PhysicalAccounts.count_le_paid
    (physicalAccounts hbase missingEdges rootLossEdges
      removedPieces recoveredPieces hcount L9 L10)

end IsSpokeCompatible

end PaperIV.RD09SpokeCompatibility
