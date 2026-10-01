import PaperIV.RD09PhaseII
import PaperIV.RD09RootFactorPhase
import PaperIV.PhysicalCompletion
import PaperIV.SplitEdgeCount
import PaperIV.RoundRobinPairs

/-!
# A literal triangle factorization of a complete split graph

Let `Core` and `Hosts` be disjoint finite vertex sets and let
`G = splitGraph Core Hosts` be the complete split graph (core clique, independent
hosts, all cross edges).  Write `k = #Core` and `h = #Hosts`.

This module constructs, **literally and constructively**, a physical `K3` packing of
`G` in the regime

* `k = 2n + 2` is even, and
* `h ≤ 2n + 1 = k - 1`.

The construction is the round-robin one-factorization of the core clique
(`PaperIV.RoundRobinPairs`): the `h` hosts receive pairwise distinct colours, and host
`y` of colour `i` is joined to the `n+1` core pairs of the perfect matching of colour
`i`, producing `n+1` triangles per host.  The packing is exhibited as a literal
*RD09 phase-II family* (`PaperIV.RD09PhaseII.IsPhaseTwoFamily`), so all the RD09
ledgers apply verbatim, and each single-host slice is literally an
`PaperIV.RD09RootFactorPhase.IsRootFactorFamily` — one factor of the root clique
together with its assigned exterior host.

The ledger is exact:

| quantity                    | value                    |
| --------------------------- | ------------------------ |
| pieces                      | `h * (n+1)`              |
| `totalGain`                 | `2 * h * (n+1)`          |
| covered edges               | `3 * h * (n+1)`          |
| covered cross edges         | all `k * h` of them      |
| uncovered edges             | `(n+1) * (2n+1-h)`, all inner |

In particular for `h = 2n + 1 = k - 1` the packing is an *exact* triangle partition of
the complete split graph, and for `h = k - 1 - c` exactly `c * k / 2` edges remain, a
bound linear in `k` for fixed deficiency `c`.

Nothing is postulated: the labelling data is produced from the cardinality hypotheses
in `exists_splitFactorLabelling`, and every coverage statement is proved.
-/

namespace PaperIV.SplitTriangleFactor

open Finset PaperIV.Model PaperIV.SplitUniformIncidence PaperIV.SplitEdgeCount
open PaperIV.PhysicalCompletion PaperIV.RD09PhaseII PaperIV.RoundRobinPairs

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {H : Type*} [Fintype H] [DecidableEq H]
variable {n : ℕ}

/-- The literal labelling data of the construction: the core is enumerated by
`Option (ZMod (2n+1))` (the round-robin vertex set of size `2n+2`), the hosts are
enumerated by `H`, and each host carries a colour, all colours being distinct. -/
structure SplitFactorLabelling (Core Hosts : Finset V) (n : ℕ)
    (cv : Option (R n) → V) (hv : H → V) (col : H → R n) : Prop where
  cvInj : Function.Injective cv
  cvImage : Finset.univ.image cv = Core
  hvInj : Function.Injective hv
  hvImage : Finset.univ.image hv = Hosts
  colInj : Function.Injective col
  disj : Disjoint Core Hosts

variable {Core Hosts : Finset V} {cv : Option (R n) → V} {hv : H → V} {col : H → R n}

namespace SplitFactorLabelling

variable (hL : SplitFactorLabelling Core Hosts n cv hv col)
include hL

theorem cv_mem (x : Option (R n)) : cv x ∈ Core := by
  rw [← hL.cvImage]; exact Finset.mem_image_of_mem _ (Finset.mem_univ x)

theorem hv_mem (y : H) : hv y ∈ Hosts := by
  rw [← hL.hvImage]; exact Finset.mem_image_of_mem _ (Finset.mem_univ y)

theorem cv_ne_hv (x : Option (R n)) (y : H) : cv x ≠ hv y := by
  intro hEq
  exact (Finset.disjoint_left.mp hL.disj (hL.cv_mem x)) (hEq ▸ hL.hv_mem y)

end SplitFactorLabelling

/-! ## The phase-II data of the construction -/

/-- The phase-II index set: one index per (host, matching-pair) couple. -/
abbrev Idx (H : Type*) (n : ℕ) : Type _ := H × Fin (n + 1)

/-- The hub of an index is the single host vertex: every piece is a triangle. -/
def hubOf (hv : H → V) : Idx H n → Finset V := fun p => {hv p.1}

/-- The base edge of an index is the corresponding core pair of the round-robin factor
of the colour of the host. -/
def baseOf (cv : Option (R n) → V) (col : H → R n) : Idx H n → Sym2 V :=
  fun p => s(cv (fstV (col p.1) p.2), cv (sndV (col p.1) p.2))

@[simp] theorem hubOf_apply (hv : H → V) (p : Idx H n) : hubOf hv p = {hv p.1} := rfl

theorem baseOf_toFinset (cv : Option (R n) → V) (col : H → R n) (p : Idx H n) :
    (baseOf cv col p).toFinset = (pair (col p.1) p.2).image cv := by
  ext x
  simp only [baseOf, Sym2.mem_toFinset, Sym2.mem_iff, Finset.mem_image, mem_pair]
  constructor
  · rintro (rfl | rfl)
    · exact ⟨fstV (col p.1) p.2, Or.inl rfl, rfl⟩
    · exact ⟨sndV (col p.1) p.2, Or.inr rfl, rfl⟩
  · rintro ⟨u, (rfl | rfl), rfl⟩
    · exact Or.inl rfl
    · exact Or.inr rfl

theorem piece_eq (cv : Option (R n) → V) (hv : H → V) (col : H → R n) (p : Idx H n) :
    piece (hubOf hv) (baseOf cv col) p = {hv p.1} ∪ (pair (col p.1) p.2).image cv := by
  rw [piece, hubOf_apply, baseOf_toFinset]

theorem mem_piece_iff {cv : Option (R n) → V} {hv : H → V} {col : H → R n} {p : Idx H n}
    {x : V} :
    x ∈ piece (hubOf hv) (baseOf cv col) p ↔
      x = hv p.1 ∨ ∃ u ∈ pair (col p.1) p.2, cv u = x := by
  rw [piece_eq]
  simp [Finset.mem_union]

/-- The packing: one triangle per (host, core pair). -/
def packing (cv : Option (R n) → V) (hv : H → V) (col : H → R n) : Finset (Finset V) :=
  phaseTwoPacking (hubOf hv) (baseOf cv col)

namespace SplitFactorLabelling

variable (hL : SplitFactorLabelling Core Hosts n cv hv col)
include hL

theorem baseOf_mem_graphEdges (p : Idx H n) :
    baseOf cv col p ∈ graphEdges (splitGraph Core Hosts) := by
  rw [baseOf, mem_graphEdges, SimpleGraph.mem_edgeSet]
  refine splitGraph_adj_inner (hL.cv_mem _) (hL.cv_mem _) ?_
  intro hEq
  exact fstV_ne_sndV (col p.1) p.2 (hL.cvInj hEq)

theorem image_pair_disjoint {i : R n} {t t' : Fin (n + 1)} (h : t ≠ t') :
    Disjoint ((pair i t).image cv) ((pair i t').image cv) :=
  (Finset.disjoint_image hL.cvInj).mpr (pair_disjoint i h)

theorem image_pair_inter_card_le_one {i i' : R n} (hii : i ≠ i') (t t' : Fin (n + 1)) :
    (((pair i t).image cv) ∩ ((pair i' t').image cv)).card ≤ 1 := by
  rw [← Finset.image_inter _ _ hL.cvInj, Finset.card_image_of_injective _ hL.cvInj]
  exact card_inter_le_one hii t t'

/-- The `meet` condition: two distinct pieces of the construction share at most one
vertex. -/
theorem meet_pieces (p q : Idx H n) (hpq : p ≠ q) :
    ((piece (hubOf hv) (baseOf cv col) p) ∩ (piece (hubOf hv) (baseOf cv col) q)).card ≤ 1 := by
  by_cases hy : p.1 = q.1
  · -- same host, different matching pairs: the pieces meet exactly in the host
    have ht : p.2 ≠ q.2 := by
      intro h
      exact hpq (Prod.ext hy h)
    refine le_trans (Finset.card_le_card ?_) (Finset.card_singleton (hv p.1)).le
    intro x hx
    rw [Finset.mem_inter, piece_eq, piece_eq, Finset.mem_union, Finset.mem_union] at hx
    rw [Finset.mem_singleton]
    rcases hx.1 with h1 | h1
    · exact Finset.mem_singleton.mp h1
    · rcases hx.2 with h2 | h2
      · rw [Finset.mem_singleton] at h2
        rw [h2, hy]
      · exact absurd h2
          (Finset.disjoint_left.mp (by rw [hy] at h1 ⊢; exact hL.image_pair_disjoint ht) h1)
  · -- different hosts: distinct colours, so the two core pairs meet in at most one vertex
    have hcol : col p.1 ≠ col q.1 := fun h => hy (hL.colInj h)
    refine le_trans (Finset.card_le_card ?_) (hL.image_pair_inter_card_le_one hcol p.2 q.2)
    intro x hx
    rw [Finset.mem_inter, piece_eq, piece_eq, Finset.mem_union, Finset.mem_union] at hx
    rw [Finset.mem_inter]
    have hxp : x ∈ (pair (col p.1) p.2).image cv := by
      rcases hx.1 with h1 | h1
      · exfalso
        rw [Finset.mem_singleton] at h1
        rcases hx.2 with h2 | h2
        · rw [Finset.mem_singleton] at h2
          exact hy (hL.hvInj (h1 ▸ h2 ▸ rfl))
        · obtain ⟨u, _, hu⟩ := Finset.mem_image.mp h2
          exact hL.cv_ne_hv u p.1 (by rw [hu, h1])
      · exact h1
    have hxq : x ∈ (pair (col q.1) q.2).image cv := by
      rcases hx.2 with h2 | h2
      · exfalso
        rw [Finset.mem_singleton] at h2
        obtain ⟨u, _, hu⟩ := Finset.mem_image.mp hxp
        exact hL.cv_ne_hv u q.1 (by rw [hu, h2])
      · exact h2
    exact ⟨hxp, hxq⟩

/-- **The construction is a literal RD09 phase-II family** of the complete split
graph. -/
theorem isPhaseTwoFamily :
    IsPhaseTwoFamily (splitGraph Core Hosts) (hubOf hv) (baseOf cv col) where
  baseEdge := hL.baseOf_mem_graphEdges
  hubCard := fun p => Or.inl (by simp [hubOf])
  hubClique := fun p => by
    simp only [hubOf_apply, Finset.coe_singleton]
    exact SimpleGraph.isClique_singleton _
  hubAdj := by
    rintro p a ha w hw
    rw [hubOf_apply, Finset.mem_singleton] at hw
    subst hw
    have haCore : a ∈ Core := by
      rw [baseOf, Sym2.mem_iff] at ha
      rcases ha with rfl | rfl <;> exact hL.cv_mem _
    exact (splitGraph_adj_cross hL.disj haCore (hL.hv_mem p.1)).symm
  sep := by
    rintro p q a ha hmem
    rw [hubOf_apply, Finset.mem_singleton] at hmem
    rw [baseOf, Sym2.mem_iff] at ha
    rcases ha with rfl | rfl <;> exact hL.cv_ne_hv _ q.1 hmem
  meet := hL.meet_pieces

theorem card_piece_three (p : Idx H n) :
    (piece (hubOf hv) (baseOf cv col) p).card = 3 :=
  (hL.isPhaseTwoFamily).card_piece_eq_three (by simp [hubOf])

theorem card_eq_three_of_mem_packing {s : Finset V} (hs : s ∈ packing cv hv col) :
    s.card = 3 := by
  rw [packing, mem_phaseTwoPacking] at hs
  obtain ⟨p, rfl⟩ := hs
  exact hL.card_piece_three p

theorem isPacking : IsPacking (splitGraph Core Hosts) (packing cv hv col) :=
  (hL.isPhaseTwoFamily).isPacking_phaseTwoPacking

/-- The packing is a literal `K3`/`K4` packing in the sense of
`PaperIV.PhysicalCompletion`. -/
theorem isK34Packing : IsK34Packing (splitGraph Core Hosts) (packing cv hv col) :=
  { hL.isPacking with big := fun s hs => Or.inl (hL.card_eq_three_of_mem_packing hs) }

/-! ### The ledgers -/

omit hL in
theorem k3Indices_eq_univ : k3Indices (hubOf hv) = (Finset.univ : Finset (Idx H n)) := by
  ext p
  simp [k3Indices, hubOf]

omit hL in
theorem k4Indices_eq_empty : k4Indices (hubOf hv) = (∅ : Finset (Idx H n)) := by
  ext p
  simp [k4Indices, hubOf]

theorem card_packing : (packing cv hv col).card = Fintype.card H * (n + 1) := by
  rw [packing, (hL.isPhaseTwoFamily).card_phaseTwoPacking]
  rw [Fintype.card_prod, Fintype.card_fin]

theorem totalGain_packing : totalGain (packing cv hv col) = 2 * (Fintype.card H * (n + 1)) := by
  rw [packing, (hL.isPhaseTwoFamily).totalGain_phaseTwoPacking, k3Indices_eq_univ,
    k4Indices_eq_empty]
  rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
  simp

theorem card_coveredEdges_packing :
    (coveredEdges (packing cv hv col)).card = 3 * (Fintype.card H * (n + 1)) := by
  rw [packing, (hL.isPhaseTwoFamily).card_coveredEdges_phaseTwoPacking, k3Indices_eq_univ,
    k4Indices_eq_empty]
  rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
  simp

/-! ### Coverage of all cross edges -/

/-- Every cross edge of the complete split graph is covered by the construction. -/
theorem crossEdges_subset_coveredEdges :
    crossEdges Core Hosts ⊆ coveredEdges (packing cv hv col) := by
  intro e he
  rw [mem_crossEdges] at he
  obtain ⟨x, hx, z, hz, rfl⟩ := he
  obtain ⟨u, -, rfl⟩ : ∃ u ∈ (Finset.univ : Finset (Option (R n))), cv u = x := by
    rw [← hL.cvImage] at hx; exact Finset.mem_image.mp hx
  obtain ⟨y, -, rfl⟩ : ∃ y ∈ (Finset.univ : Finset H), hv y = z := by
    rw [← hL.hvImage] at hz; exact Finset.mem_image.mp hz
  obtain ⟨t, ht⟩ := exists_mem_pair (col y) u
  refine mem_coveredEdges.mpr ⟨piece (hubOf hv) (baseOf cv col) (y, t), ?_, ?_⟩
  · rw [packing, mem_phaseTwoPacking]; exact ⟨(y, t), rfl⟩
  · rw [mem_pieceEdges_mk]
    refine ⟨mem_piece_iff.mpr (Or.inr ⟨u, ht, rfl⟩), mem_piece_iff.mpr (Or.inl rfl), ?_⟩
    exact hL.cv_ne_hv u y

/-- Every uncovered edge is an inner (core) edge. -/
theorem uncovered_subset_inner :
    graphEdges (splitGraph Core Hosts) \ coveredEdges (packing cv hv col) ⊆ pieceEdges Core := by
  intro e he
  rw [Finset.mem_sdiff, graphEdges_splitGraph hL.disj, Finset.mem_union] at he
  rcases he.1 with h | h
  · exact h
  · exact absurd (hL.crossEdges_subset_coveredEdges h) he.2

/-! ### The reusable block: one factor of the core clique plus its assigned exterior host -/

/-- **Block theorem.**  For a single host `y`, the `n+1` triangles over the round-robin
perfect matching of the colour of `y` form a literal
`PaperIV.RD09RootFactorPhase.IsRootFactorFamily` with root clique `Core`: one factor of
the root clique together with one assigned exterior host.  All hypotheses are derived
from the literal split graph, none is assumed. -/
theorem isRootFactorFamily_singleHost (y : H) :
    PaperIV.RD09RootFactorPhase.IsRootFactorFamily (splitGraph Core Hosts) Core
      (fun _ : Fin (n + 1) => ({hv y} : Finset V)) (fun t => baseOf cv col (y, t)) where
  rootClique := isClique_of_subset_core (le_refl Core)
  baseSubRoot := by
    intro t a ha
    rw [baseOf, Sym2.mem_iff] at ha
    rcases ha with rfl | rfl <;> exact hL.cv_mem _
  baseNotDiag := fun t =>
    not_isDiag_of_mem_graphEdges _ (hL.baseOf_mem_graphEdges (y, t))
  baseMatching := by
    intro t t' htt
    rw [baseOf_toFinset, baseOf_toFinset]
    exact hL.image_pair_disjoint htt
  hubCard := fun _ => Or.inl (Finset.card_singleton _)
  hubClique := fun _ => by
    simp only [Finset.coe_singleton]
    exact SimpleGraph.isClique_singleton _
  hubAdj := by
    intro t a ha w hw
    rw [Finset.mem_singleton] at hw
    subst hw
    have haCore : a ∈ Core := by
      rw [baseOf, Sym2.mem_iff] at ha
      rcases ha with rfl | rfl <;> exact hL.cv_mem _
    exact (splitGraph_adj_cross hL.disj haCore (hL.hv_mem y)).symm
  hubExterior := by
    intro t w hw
    rw [Finset.mem_singleton] at hw
    subst hw
    exact Finset.disjoint_right.mp hL.disj (hL.hv_mem y)
  hubMeet := fun _ _ _ => by simp

end SplitFactorLabelling

/-! ## Existence of the labelling from the bare cardinality hypotheses -/

theorem card_option_R (n : ℕ) : Fintype.card (Option (R n)) = 2 * n + 2 := by
  haveI : NeZero (2 * n + 1) := ⟨by omega⟩
  have hcard : Fintype.card (R n) = 2 * n + 1 := ZMod.card (2 * n + 1)
  rw [Fintype.card_option, hcard]

/-- From the literal cardinality hypotheses `#Core = 2n+2` and `#Hosts ≤ 2n+1` one can
construct the labelling data of the construction. -/
theorem exists_splitFactorLabelling {Core Hosts : Finset V} (hd : Disjoint Core Hosts)
    {n : ℕ} (hk : Core.card = 2 * n + 2) (hh : Hosts.card ≤ 2 * n + 1) :
    ∃ (cv : Option (R n) → V) (hv : Fin Hosts.card → V) (col : Fin Hosts.card → R n),
      SplitFactorLabelling Core Hosts n cv hv col := by
  haveI : NeZero (2 * n + 1) := ⟨by omega⟩
  -- the core labelling
  have hcard : Fintype.card (Option (R n)) = Core.card := by rw [card_option_R, hk]
  let eC : Option (R n) ≃ {x // x ∈ Core} :=
    (Fintype.equivFinOfCardEq hcard).trans (Core.equivFin).symm
  refine ⟨fun u => (eC u : V), fun j => ((Hosts.equivFin).symm j : V),
    fun j => ((j : ℕ) : R n), ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, hd⟩
  · intro a b hab
    exact eC.injective (Subtype.ext hab)
  · ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨u, rfl⟩; exact (eC u).2
    · intro hx; exact ⟨eC.symm ⟨x, hx⟩, by simp⟩
  · intro a b hab
    exact (Hosts.equivFin).symm.injective (Subtype.ext hab)
  · ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨j, rfl⟩; exact ((Hosts.equivFin).symm j).2
    · intro hx; exact ⟨Hosts.equivFin ⟨x, hx⟩, by simp⟩
  · intro a b hab
    have ha := a.isLt
    have hb := b.isLt
    have h1 := congrArg ZMod.val hab
    rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)] at h1
    exact Fin.ext h1

/-! ## The main theorem -/

theorem choose_two_even (n : ℕ) : (2 * n + 2).choose 2 = (n + 1) * (2 * n + 1) := by
  have h := PaperIV.SplitUniformIncidence.mul_pred_eq_two_mul_choose_two (2 * n + 2)
  have h2 : (2 * n + 2) * (2 * n + 2 - 1) = 2 * ((n + 1) * (2 * n + 1)) := by
    have hsub : 2 * n + 2 - 1 = 2 * n + 1 := by omega
    rw [hsub]; ring
  omega

/-- **The main construction.**  For a complete split graph with an even core of size
`k = 2n+2` and at most `k-1` hosts, there is an explicit physical `K3` packing with a
fully explicit ledger: it consists of `h(n+1)` triangles, covers *all* cross edges, and
leaves exactly `(n+1)(2n+1-h)` inner edges uncovered. -/
theorem exists_split_triangle_packing {Core Hosts : Finset V} (hd : Disjoint Core Hosts)
    {n : ℕ} (hk : Core.card = 2 * n + 2) (hh : Hosts.card ≤ 2 * n + 1) :
    ∃ P : Finset (Finset V),
      IsK34Packing (splitGraph Core Hosts) P ∧
      (∀ s ∈ P, s.card = 3) ∧
      P.card = Hosts.card * (n + 1) ∧
      totalGain P = 2 * (Hosts.card * (n + 1)) ∧
      (coveredEdges P).card = 3 * (Hosts.card * (n + 1)) ∧
      crossEdges Core Hosts ⊆ coveredEdges P ∧
      (graphEdges (splitGraph Core Hosts) \ coveredEdges P) ⊆ pieceEdges Core ∧
      (graphEdges (splitGraph Core Hosts) \ coveredEdges P).card
        = (n + 1) * (2 * n + 1 - Hosts.card) := by
  obtain ⟨cv, hv, col, hL⟩ := exists_splitFactorLabelling hd hk hh
  refine ⟨packing cv hv col, hL.isK34Packing, fun s hs => hL.card_eq_three_of_mem_packing hs,
    ?_, ?_, ?_, hL.crossEdges_subset_coveredEdges, hL.uncovered_subset_inner, ?_⟩
  · rw [hL.card_packing]; simp
  · rw [hL.totalGain_packing]; simp
  · rw [hL.card_coveredEdges_packing]; simp
  · have hsub : coveredEdges (packing cv hv col) ⊆ graphEdges (splitGraph Core Hosts) :=
      hL.isPacking.coveredEdges_subset
    rw [Finset.card_sdiff_of_subset hsub, card_graphEdges_splitGraph hd,
      hL.card_coveredEdges_packing,
      hk, choose_two_even]
    have hcardH : Fintype.card (Fin Hosts.card) = Hosts.card := Fintype.card_fin _
    rw [hcardH]
    have hrw : (2 * n + 2) * Hosts.card = 2 * (Hosts.card * (n + 1)) := by ring
    rw [hrw]
    have hX : Hosts.card * (n + 1) ≤ (n + 1) * (2 * n + 1) := by
      calc Hosts.card * (n + 1) ≤ (2 * n + 1) * (n + 1) := Nat.mul_le_mul_right _ hh
        _ = (n + 1) * (2 * n + 1) := by ring
    have key : (n + 1) * (2 * n + 1 - Hosts.card) + Hosts.card * (n + 1)
        = (n + 1) * (2 * n + 1) := by
      rw [Nat.mul_comm Hosts.card (n + 1), ← Nat.mul_add, Nat.sub_add_cancel hh]
    omega

/-- **Exact triangle partition.**  For `h = k - 1 = 2n+1` hosts the construction covers
*every* edge of the complete split graph: the split graph is partitioned into
`(2n+1)(n+1)` triangles. -/
theorem exists_split_triangle_partition {Core Hosts : Finset V} (hd : Disjoint Core Hosts)
    {n : ℕ} (hk : Core.card = 2 * n + 2) (hh : Hosts.card = 2 * n + 1) :
    ∃ P : Finset (Finset V),
      IsExactPartition (splitGraph Core Hosts) P ∧
      (∀ s ∈ P, s.card = 3) ∧
      P.card = (2 * n + 1) * (n + 1) := by
  obtain ⟨P, hK34, hthree, hcard, -, -, -, -, huncov⟩ :=
    exists_split_triangle_packing hd hk (le_of_eq hh)
  have hsub : coveredEdges P ⊆ graphEdges (splitGraph Core Hosts) :=
    hK34.toIsPacking.coveredEdges_subset
  have hzero : (graphEdges (splitGraph Core Hosts) \ coveredEdges P).card = 0 := by
    rw [huncov, hh]; simp
  refine ⟨P, ⟨hK34.toIsPacking, ?_⟩, hthree, by rw [hcard, hh]⟩
  have hempty : graphEdges (splitGraph Core Hosts) \ coveredEdges P = ∅ :=
    Finset.card_eq_zero.mp hzero
  exact hsub.antisymm (Finset.sdiff_eq_empty_iff_subset.mp hempty)

/-- **The physical terminal with its complete ledger.**  Completing the triangle packing
by its uncovered inner edges gives an exact physical partition of the complete split
graph into `h(n+1)` triangles and `(n+1)(2n+1-h)` single edges; the gain is carried
entirely by the triangles. -/
theorem exists_split_physical_terminal {Core Hosts : Finset V} (hd : Disjoint Core Hosts)
    {n : ℕ} (hk : Core.card = 2 * n + 2) (hh : Hosts.card ≤ 2 * n + 1) :
    ∃ P : Finset (Finset V),
      IsK34Packing (splitGraph Core Hosts) P ∧
      IsExactPartition (splitGraph Core Hosts) (completion (splitGraph Core Hosts) P) ∧
      (completion (splitGraph Core Hosts) P).card
        = Hosts.card * (n + 1) + (n + 1) * (2 * n + 1 - Hosts.card) ∧
      totalGain P = 2 * (Hosts.card * (n + 1)) := by
  obtain ⟨P, hK34, -, hcard, hgain, -, -, -, huncov⟩ :=
    exists_split_triangle_packing hd hk hh
  refine ⟨P, hK34, isExactPartition_completion hK34.toIsPacking, ?_, hgain⟩
  rw [card_completion hK34, hcard]
  exact congrArg (Hosts.card * (n + 1) + ·) huncov

/-! ## Non-vacuity

A literal instance of the hypotheses: a core of four vertices and three hosts inside
`Fin 7`.  The theorems above then produce an exact partition of the `6 + 12 = 18` edges
of this complete split graph into six triangles. -/

namespace Example

/-- A four-element core inside `Fin 7`. -/
def exCore : Finset (Fin 7) := {0, 1, 2, 3}

/-- Three hosts inside `Fin 7`. -/
def exHosts : Finset (Fin 7) := {4, 5, 6}

theorem exDisjoint : Disjoint exCore exHosts := by decide

theorem exCoreCard : exCore.card = 2 * 1 + 2 := by decide

theorem exHostsCard : exHosts.card = 2 * 1 + 1 := by decide

/-- The complete split graph on this core and these hosts is partitioned into six
triangles. -/
theorem exists_partition_example :
    ∃ P : Finset (Finset (Fin 7)),
      IsExactPartition (splitGraph exCore exHosts) P ∧
      (∀ s ∈ P, s.card = 3) ∧ P.card = 6 := by
  obtain ⟨P, hP, hthree, hcard⟩ :=
    exists_split_triangle_partition exDisjoint exCoreCard exHostsCard
  exact ⟨P, hP, hthree, by simpa using hcard⟩

end Example

end PaperIV.SplitTriangleFactor
