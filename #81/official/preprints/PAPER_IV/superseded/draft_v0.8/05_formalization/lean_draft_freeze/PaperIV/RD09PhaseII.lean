import PaperIV.MultiHostTriangleLift
import PaperIV.TransportedMatchings
import PaperIV.OneFactorization
import PaperIV.LineGraphColouring

/-!
# RD09 Phase II: a literal resource-level second physical phase

Phase I (`PaperIV.MultiHostTriangleLift`) lifts literal base matchings over exterior
hosts to a packing of `K3` pieces.  This module supplies a *reusable* second physical
phase which is compatible with `PaperIV.MultiHostTriangleLift.multiLiftedPacking`:

* the phase-II data is an arbitrary finite family, indexed by `J`, of a **hub set**
  `hub j` (one or two vertices) together with one **base edge** `base j` of `G`;
* a piece is the literal `Finset V` `hub j ∪ (base j).toFinset`, hence a `K3` when the
  hub is a single vertex and a `K4` when the hub is an (adjacent) pair;
* every compatibility requirement is explicit and literal: hub cliqueness, hub/base
  adjacency, core/hub separation, and "distinct pieces meet in at most one vertex".

We prove
1. every phase-II piece is a `PaperIV.Model.IsPiece`;
2. every phase-II physical edge resource is disjoint from every phase-I resource, under
   the explicit cross-phase compatibility hypotheses of `IsPhaseCompatible`;
3. exact ledgers: the covered resource set, its cardinality, the number of pieces and
   `PaperIV.Model.totalGain`, all expressed through the literal counts of `K3` and `K4`
   indices;
4. the assembly theorems: the union with phase I is a `PaperIV.Model.IsPacking`, and it
   is a `PaperIV.Model.IsExactPartition` exactly when the supplied coverage equality
   says the two phases together cover `PaperIV.Model.graphEdges G`.

Nothing here postulates a terminal partition, a terminal numerical ledger, or a global
rounding theorem: every statement is conditional on the explicitly supplied finite data.
-/

namespace PaperIV.RD09PhaseII

open Finset PaperIV.Model PaperIV.ExteriorTriangleLift PaperIV.MultiHostTriangleLift

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ## A resource criterion: pieces meeting in at most one vertex -/

omit [Fintype V] in
/-- Two literal vertex sets meeting in at most one vertex have disjoint physical edge
resources.  This is the resource-level workhorse of the whole module. -/
theorem pieceEdges_disjoint_of_card_inter_le_one {s t : Finset V}
    (h : (s ∩ t).card ≤ 1) : Disjoint (pieceEdges s) (pieceEdges t) := by
  rw [Finset.disjoint_left]
  intro g hs ht
  rw [mem_pieceEdges] at hs ht
  induction g with
  | _ a b =>
    have hab : a ≠ b := by simpa [Sym2.isDiag_iff_proj_eq] using hs.2
    have ha : a ∈ s ∩ t := Finset.mem_inter.mpr ⟨hs.1 a (by simp), ht.1 a (by simp)⟩
    have hb : b ∈ s ∩ t := Finset.mem_inter.mpr ⟨hs.1 b (by simp), ht.1 b (by simp)⟩
    have : 1 < (s ∩ t).card := Finset.one_lt_card.mpr ⟨a, ha, b, hb, hab⟩
    omega

omit [Fintype V] [DecidableRel G.Adj] in
/-- For any literal packing the covered resource count is `card + totalGain`. -/
theorem card_coveredEdges_of_isPacking {P : Finset (Finset V)} (h : IsPacking G P) :
    (coveredEdges P).card = P.card + totalGain P := by
  have hcard : (coveredEdges P).card = ∑ s ∈ P, (pieceEdges s).card :=
    Finset.card_biUnion fun s hs t ht hst => h.edgeDisjoint s hs t ht hst
  have hsum : ∑ s ∈ P, (pieceEdges s).card = ∑ s ∈ P, (gainOf s + 1) :=
    Finset.sum_congr rfl fun s hs => (h.pieces s hs).card_pieceEdges_eq
  rw [hcard, hsum, Finset.sum_add_distrib]
  simp [totalGain, Nat.add_comm]

/-! ## Phase-II data -/

variable {J : Type*} [Fintype J] [DecidableEq J]

/-- The literal phase-II piece: the hub set together with the endpoints of the base
edge.  A one-vertex hub gives a `K3`, a two-vertex hub gives a `K4`. -/
def piece (hub : J → Finset V) (base : J → Sym2 V) (j : J) : Finset V :=
  hub j ∪ (base j).toFinset

variable {hub : J → Finset V} {base : J → Sym2 V}

omit [Fintype V] [Fintype J] [DecidableEq J] in
@[simp] theorem mem_piece {j : J} {x : V} :
    x ∈ piece hub base j ↔ x ∈ hub j ∨ x ∈ base j := by
  simp [piece, Sym2.mem_toFinset]

/-- A literal phase-II family: finitely many hub/base pairs satisfying exactly the
compatibility requirements needed at the resource level.

* `baseEdge`  : each base is a genuine edge of `G`;
* `hubCard`   : each hub is one vertex (a `K3` piece) or two vertices (a `K4` piece);
* `hubClique` : the hub itself is a clique of `G`;
* `hubAdj`    : every hub vertex is adjacent to every endpoint of its own base edge;
* `sep`       : core/hub separation — no base endpoint is a hub vertex, for any index;
* `meet`      : distinct pieces of the family meet in at most one vertex. -/
structure IsPhaseTwoFamily (G : SimpleGraph V) [DecidableRel G.Adj]
    (hub : J → Finset V) (base : J → Sym2 V) : Prop where
  baseEdge : ∀ j, base j ∈ graphEdges G
  hubCard : ∀ j, (hub j).card = 1 ∨ (hub j).card = 2
  hubClique : ∀ j, G.IsClique (hub j : Set V)
  hubAdj : ∀ j, ∀ a ∈ base j, ∀ w ∈ hub j, G.Adj w a
  sep : ∀ j k, ∀ a ∈ base j, a ∉ hub k
  meet : ∀ j k, j ≠ k → ((piece hub base j) ∩ (piece hub base k)).card ≤ 1

namespace IsPhaseTwoFamily

variable (h : IsPhaseTwoFamily G hub base)
include h

omit [Fintype J] [DecidableEq J] in
theorem base_not_isDiag (j : J) : ¬ (base j).IsDiag :=
  not_isDiag_of_mem_graphEdges G (h.baseEdge j)

omit [Fintype J] [DecidableEq J] in
theorem disjoint_hub_base (j : J) : Disjoint (hub j) (base j).toFinset := by
  rw [Finset.disjoint_right]
  intro a ha
  exact h.sep j j a (Sym2.mem_toFinset.mp ha)

omit [Fintype J] [DecidableEq J] in
/-- Exact size of a phase-II piece: the hub size plus the two base endpoints. -/
theorem card_piece (j : J) : (piece hub base j).card = (hub j).card + 2 := by
  rw [piece, Finset.card_union_of_disjoint (h.disjoint_hub_base j),
    Sym2.card_toFinset_of_not_isDiag _ (h.base_not_isDiag j)]

omit [Fintype J] [DecidableEq J] in
theorem card_piece_eq_three {j : J} (hj : (hub j).card = 1) :
    (piece hub base j).card = 3 := by rw [h.card_piece j, hj]

omit [Fintype J] [DecidableEq J] in
theorem card_piece_eq_four {j : J} (hj : (hub j).card = 2) :
    (piece hub base j).card = 4 := by rw [h.card_piece j, hj]

omit [Fintype J] [DecidableEq J] in
theorem three_le_card_piece (j : J) : 3 ≤ (piece hub base j).card := by
  rw [h.card_piece j]
  rcases h.hubCard j with hj | hj <;> omega

omit [Fintype J] [DecidableEq J] in
/-- **(1)** Every phase-II piece is a literal physical piece of `G`. -/
theorem isPiece (j : J) : IsPiece G (piece hub base j) := by
  refine ⟨?_, ?_⟩
  · intro x hx y hy hxy
    simp only [Finset.mem_coe, mem_piece] at hx hy
    rcases hx with hx | hx
    · rcases hy with hy | hy
      · exact h.hubClique j (Finset.mem_coe.mpr hx) (Finset.mem_coe.mpr hy) hxy
      · exact h.hubAdj j y hy x hx
    · rcases hy with hy | hy
      · exact (h.hubAdj j x hx y hy).symm
      · exact adj_of_mem_edge (h.baseEdge j) hx hy hxy
  · rcases h.hubCard j with hj | hj
    · exact ⟨PieceKind.K3, h.card_piece_eq_three hj⟩
    · exact ⟨PieceKind.K4, h.card_piece_eq_four hj⟩

omit [Fintype J] [DecidableEq J] in
/-- The base edge is a physical resource of its own piece. -/
theorem base_mem_pieceEdges (j : J) : base j ∈ pieceEdges (piece hub base j) := by
  rw [mem_pieceEdges]
  exact ⟨fun a ha => mem_piece.mpr (Or.inr ha), h.base_not_isDiag j⟩

omit [Fintype J] [DecidableEq J] in
/-- Distinct indices give resource-disjoint phase-II pieces. -/
theorem pieceEdges_disjoint {j k : J} (hjk : j ≠ k) :
    Disjoint (pieceEdges (piece hub base j)) (pieceEdges (piece hub base k)) :=
  pieceEdges_disjoint_of_card_inter_le_one (h.meet j k hjk)

omit [Fintype J] [DecidableEq J] in
/-- The phase-II pieces are pairwise distinct as literal vertex sets. -/
theorem piece_injective : Function.Injective (piece hub base) := by
  intro j k hjk
  by_contra hne
  have := h.meet j k hne
  rw [hjk, Finset.inter_self] at this
  have := h.three_le_card_piece k
  omega

end IsPhaseTwoFamily

/-! ### A convenient sufficient criterion for the `meet` hypothesis -/

omit [Fintype V] [Fintype J] [DecidableEq J] in
/-- The `meet` hypothesis follows from primitive, literal separation data: the base edges
form a matching, no base endpoint is a hub vertex, and distinct hubs share at most one
vertex (in particular a common single hub vertex, as in the phase-I triangle lift, or
disjoint hub pairs, as for `K4` pieces). -/
theorem meet_of_matching_hubs
    (hsep : ∀ j k, ∀ a ∈ base j, a ∉ hub k)
    (hbase : ∀ j k, j ≠ k → Disjoint (base j).toFinset (base k).toFinset)
    (hhub : ∀ j k, j ≠ k → (hub j ∩ hub k).card ≤ 1) :
    ∀ j k, j ≠ k → ((piece hub base j) ∩ (piece hub base k)).card ≤ 1 := by
  intro j k hjk
  refine le_trans (Finset.card_le_card ?_) (hhub j k hjk)
  intro x hx
  rw [Finset.mem_inter, mem_piece, mem_piece] at hx
  obtain ⟨hxj, hxk⟩ := hx
  rcases hxj with hxj | hxj
  · rcases hxk with hxk | hxk
    · exact Finset.mem_inter.mpr ⟨hxj, hxk⟩
    · exact absurd hxj (hsep k j x hxk)
  · rcases hxk with hxk | hxk
    · exact absurd hxk (hsep j k x hxj)
    · exact absurd (Sym2.mem_toFinset.mpr hxk)
        (Finset.disjoint_left.mp (hbase j k hjk) (Sym2.mem_toFinset.mpr hxj))

omit [Fintype J] [DecidableEq J] in
/-- Build a phase-II family from explicit matching/separation data. -/
theorem isPhaseTwoFamily_of_matching_hubs
    (hbaseEdge : ∀ j, base j ∈ graphEdges G)
    (hhubCard : ∀ j, (hub j).card = 1 ∨ (hub j).card = 2)
    (hhubClique : ∀ j, G.IsClique (hub j : Set V))
    (hhubAdj : ∀ j, ∀ a ∈ base j, ∀ w ∈ hub j, G.Adj w a)
    (hsep : ∀ j k, ∀ a ∈ base j, a ∉ hub k)
    (hbase : ∀ j k, j ≠ k → Disjoint (base j).toFinset (base k).toFinset)
    (hhub : ∀ j k, j ≠ k → (hub j ∩ hub k).card ≤ 1) :
    IsPhaseTwoFamily G hub base :=
  ⟨hbaseEdge, hhubCard, hhubClique, hhubAdj, hsep, meet_of_matching_hubs hsep hbase hhub⟩

/-! ### Supplying the base edges from explicit finite factors / transported matchings

The base family of a phase-II construction is typically read off from one literal
matching: a colour class of a proper edge colouring (`PaperIV.ColourClasses`,
`PaperIV.LineGraphColouring`, `PaperIV.Vizing`), a 1-factor
(`SimpleGraph.IsOneFactorization`), or a transported labelled matching
(`PaperIV.TransportedMatchings`).  All of these deliver exactly the
`PairwiseDisjoint Sym2.toFinset` property, which is all the phase-II construction
needs. -/

omit [Fintype V] [Fintype J] [DecidableEq J] in
/-- An injective indexing of a literal matching gives the base-matching hypothesis. -/
theorem baseMatching_of_pairwiseDisjoint {S : Finset (Sym2 V)}
    (hS : (↑S : Set (Sym2 V)).PairwiseDisjoint Sym2.toFinset)
    (hmem : ∀ j, base j ∈ S) (hinj : Function.Injective base) :
    ∀ j k, j ≠ k → Disjoint (base j).toFinset (base k).toFinset :=
  fun j k hjk => hS (by simpa using hmem j) (by simpa using hmem k) fun he => hjk (hinj he)

omit [Fintype V] [Fintype J] [DecidableEq J] in
/-- The base-matching hypothesis for base edges taken from a transported colour class of
a proper labelled edge colouring. -/
theorem baseMatching_of_mapColourClass {A Color : Type*} [DecidableEq A] [DecidableEq Color]
    {f : A ↪ V} {E : Finset (Sym2 A)} {colour : Sym2 A → Color}
    (hproper : PaperIV.ColourClasses.ProperOn E colour) (c : Color)
    (hmem : ∀ j, base j ∈ PaperIV.TransportedMatchings.mapColourClass f E colour c)
    (hinj : Function.Injective base) :
    ∀ j k, j ≠ k → Disjoint (base j).toFinset (base k).toFinset :=
  baseMatching_of_pairwiseDisjoint
    (PaperIV.TransportedMatchings.mapColourClass_pairwiseDisjoint_toFinset hproper c)
    hmem hinj

/-! ## The phase-II packing and its ledgers -/

/-- The literal family of phase-II pieces. -/
def phaseTwoPacking (hub : J → Finset V) (base : J → Sym2 V) : Finset (Finset V) :=
  Finset.univ.image (piece hub base)

omit [Fintype V] [DecidableEq J] in
@[simp] theorem mem_phaseTwoPacking {s : Finset V} :
    s ∈ phaseTwoPacking hub base ↔ ∃ j, piece hub base j = s := by
  simp [phaseTwoPacking]

/-- The indices carrying a `K3` piece. -/
def k3Indices (hub : J → Finset V) : Finset J := Finset.univ.filter fun j => (hub j).card = 1

/-- The indices carrying a `K4` piece. -/
def k4Indices (hub : J → Finset V) : Finset J := Finset.univ.filter fun j => (hub j).card = 2

namespace IsPhaseTwoFamily

variable (h : IsPhaseTwoFamily G hub base)
include h

omit [DecidableEq J] in
/-- Every index is either a `K3` index or a `K4` index. -/
theorem card_k3_add_card_k4 :
    (k3Indices hub).card + (k4Indices hub).card = Fintype.card J := by
  have hk4 : k4Indices hub = Finset.univ.filter fun j => ¬ (hub j).card = 1 := by
    ext j
    simp only [k4Indices, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hj; omega
    · intro hj; rcases h.hubCard j with hj' | hj' <;> omega
  rw [k3Indices, hk4, Finset.card_filter_add_card_filter_not, Finset.card_univ]

omit [DecidableEq J] in
/-- **(3a)** The phase-II family has exactly one piece per index. -/
theorem card_phaseTwoPacking : (phaseTwoPacking hub base).card = Fintype.card J := by
  rw [phaseTwoPacking, Finset.card_image_of_injective _ h.piece_injective, Finset.card_univ]

omit [DecidableEq J] in
/-- **(1')** The phase-II family is a literal packing of `G`. -/
theorem isPacking_phaseTwoPacking : IsPacking G (phaseTwoPacking hub base) := by
  constructor
  · intro s hs
    rw [mem_phaseTwoPacking] at hs
    obtain ⟨j, rfl⟩ := hs
    exact h.isPiece j
  · intro s hs t ht hst
    rw [mem_phaseTwoPacking] at hs ht
    obtain ⟨j, rfl⟩ := hs
    obtain ⟨k, rfl⟩ := ht
    exact h.pieceEdges_disjoint fun hjk => hst (by rw [hjk])

omit [Fintype V] [DecidableRel G.Adj] [DecidableEq J] h in
/-- **(3b)** The covered physical resource set of phase II, literally. -/
theorem coveredEdges_phaseTwoPacking :
    coveredEdges (phaseTwoPacking hub base)
      = Finset.univ.biUnion fun j => pieceEdges (piece hub base j) := by
  ext g
  simp only [mem_coveredEdges, Finset.mem_biUnion, mem_phaseTwoPacking, Finset.mem_univ,
    true_and]
  constructor
  · rintro ⟨s, ⟨j, rfl⟩, hg⟩; exact ⟨j, hg⟩
  · rintro ⟨j, hg⟩; exact ⟨piece hub base j, ⟨j, rfl⟩, hg⟩

omit [DecidableEq J] in
/-- Every base edge is a covered phase-II resource. -/
theorem base_mem_coveredEdges (j : J) :
    base j ∈ coveredEdges (phaseTwoPacking hub base) := by
  rw [mem_coveredEdges]
  exact ⟨piece hub base j, mem_phaseTwoPacking.mpr ⟨j, rfl⟩, h.base_mem_pieceEdges j⟩

omit [Fintype J] [DecidableEq J] in
theorem gainOf_piece (j : J) :
    gainOf (piece hub base j) = if (hub j).card = 1 then 2 else 5 := by
  rcases h.hubCard j with hj | hj
  · rw [gainOf_of_card_three (h.card_piece_eq_three hj), if_pos hj]
  · rw [gainOf_of_card_four (h.card_piece_eq_four hj), if_neg (by omega)]

omit [DecidableEq J] in
/-- **(3c)** The exact gain ledger of phase II: `2` per `K3` piece and `5` per `K4`
piece. -/
theorem totalGain_phaseTwoPacking :
    totalGain (phaseTwoPacking hub base)
      = 2 * (k3Indices hub).card + 5 * (k4Indices hub).card := by
  have hsum : totalGain (phaseTwoPacking hub base)
      = ∑ j : J, gainOf (piece hub base j) := by
    rw [totalGain, phaseTwoPacking,
      Finset.sum_image fun j _ k _ hjk => h.piece_injective hjk]
  have hk4 : k4Indices hub = Finset.univ.filter fun j => ¬ (hub j).card = 1 := by
    ext j
    simp only [k4Indices, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hj; omega
    · intro hj; rcases h.hubCard j with hj' | hj' <;> omega
  rw [hsum, ← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun j => (hub j).card = 1) fun j => gainOf (piece hub base j)]
  have h1 : ∑ j ∈ Finset.univ.filter fun j => (hub j).card = 1,
      gainOf (piece hub base j) = 2 * (k3Indices hub).card := by
    rw [Finset.sum_congr rfl fun j hj => h.gainOf_piece j |>.trans
      (if_pos (Finset.mem_filter.mp hj).2)]
    rw [Finset.sum_const, k3Indices, smul_eq_mul, Nat.mul_comm]
  have h2 : ∑ j ∈ Finset.univ.filter fun j => ¬ (hub j).card = 1,
      gainOf (piece hub base j) = 5 * (k4Indices hub).card := by
    rw [Finset.sum_congr rfl fun j hj => h.gainOf_piece j |>.trans
      (if_neg (Finset.mem_filter.mp hj).2)]
    rw [Finset.sum_const, hk4, smul_eq_mul, Nat.mul_comm]
  rw [h1, h2]

omit [DecidableEq J] in
/-- **(3d)** The exact covered-resource count of phase II: three resources per `K3`
piece and six per `K4` piece. -/
theorem card_coveredEdges_phaseTwoPacking :
    (coveredEdges (phaseTwoPacking hub base)).card
      = 3 * (k3Indices hub).card + 6 * (k4Indices hub).card := by
  rw [card_coveredEdges_of_isPacking h.isPacking_phaseTwoPacking, h.card_phaseTwoPacking,
    h.totalGain_phaseTwoPacking, ← h.card_k3_add_card_k4]
  ring

omit [DecidableEq J] in
/-- If phase II alone happens to cover all of `G`, it is an exact literal partition. -/
theorem isExactPartition_of_covers
    (hcov : coveredEdges (phaseTwoPacking hub base) = graphEdges G) :
    IsExactPartition G (phaseTwoPacking hub base) :=
  ⟨h.isPacking_phaseTwoPacking, hcov⟩

end IsPhaseTwoFamily

/-! ## Cross-phase compatibility with the phase-I multi-host lift -/

variable {I : Type*} [Fintype I] [DecidableEq I] {z : I → V} {E : I → Finset (Sym2 V)}

/-- The explicit, literal compatibility between the phase-I multi-host triangle lift
`multiLiftedPacking z E` and a phase-II family `(hub, base)`:

* `hostSep`  : no phase-I host occurs in any phase-II piece (host/core separation);
* `baseMeet` : every phase-I base edge meets every phase-II piece in at most one vertex
  (matching/factor resource separation).

Note that phase-I and phase-II pieces are allowed to share a vertex; only physical edge
resources must not be shared, and that is exactly what these two conditions give. -/
structure IsPhaseCompatible (z : I → V) (E : I → Finset (Sym2 V))
    (hub : J → Finset V) (base : J → Sym2 V) : Prop where
  hostSep : ∀ i j, z i ∉ piece hub base j
  baseMeet : ∀ i j, ∀ e ∈ E i, (e.toFinset ∩ piece hub base j).card ≤ 1

namespace IsPhaseCompatible

variable (hc : IsPhaseCompatible z E hub base)
include hc

omit [Fintype V] [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
/-- A phase-I triangle and a phase-II piece meet in at most one vertex. -/
theorem card_inter_le_one {i : I} {j : J} {e : Sym2 V} (he : e ∈ E i) :
    (triangle (z i) e ∩ piece hub base j).card ≤ 1 := by
  have hrw : triangle (z i) e ∩ piece hub base j = e.toFinset ∩ piece hub base j := by
    ext x
    simp only [Finset.mem_inter, mem_triangle, Sym2.mem_toFinset]
    constructor
    · rintro ⟨hx | hx, hx2⟩
      · exact absurd (hx ▸ hx2) (hc.hostSep i j)
      · exact ⟨hx, hx2⟩
    · rintro ⟨hx, hx2⟩
      exact ⟨Or.inr hx, hx2⟩
  rw [hrw]
  exact hc.baseMeet i j e he

omit [Fintype V] [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
/-- **(2)** Every phase-II physical resource is disjoint from every phase-I resource. -/
theorem pieceEdges_disjoint_cross {i : I} {j : J} {e : Sym2 V} (he : e ∈ E i) :
    Disjoint (pieceEdges (triangle (z i) e)) (pieceEdges (piece hub base j)) :=
  pieceEdges_disjoint_of_card_inter_le_one (hc.card_inter_le_one he)

omit [Fintype V] [DecidableEq I] [DecidableEq J] in
/-- **(2')** Cross-phase resource disjointness at the level of the two packings. -/
theorem pieceEdges_disjoint_phases :
    ∀ s ∈ multiLiftedPacking z E, ∀ t ∈ phaseTwoPacking hub base,
      Disjoint (pieceEdges s) (pieceEdges t) := by
  intro s hs t ht
  rw [mem_multiLiftedPacking] at hs
  rw [mem_phaseTwoPacking] at ht
  obtain ⟨i, e, he, rfl⟩ := hs
  obtain ⟨j, rfl⟩ := ht
  exact hc.pieceEdges_disjoint_cross he

omit [DecidableEq I] [Fintype V] [DecidableEq J] in
/-- The two phases cover disjoint physical resource sets. -/
theorem disjoint_coveredEdges :
    Disjoint (coveredEdges (multiLiftedPacking z E))
      (coveredEdges (phaseTwoPacking hub base)) := by
  rw [Finset.disjoint_left]
  intro g hg1 hg2
  rw [mem_coveredEdges] at hg1 hg2
  obtain ⟨s, hs, hgs⟩ := hg1
  obtain ⟨t, ht, hgt⟩ := hg2
  exact Finset.disjoint_left.mp (hc.pieceEdges_disjoint_phases s hs t ht) hgs hgt

omit [DecidableEq I] [DecidableEq J] in
/-- The two phase families are literally disjoint families of pieces, so the ledgers
simply add. -/
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

end IsPhaseCompatible

/-! ## Assembling the two phases -/

variable {hub : J → Finset V} {base : J → Sym2 V}

omit [DecidableEq J] in
/-- **(4)** The union of the phase-I multi-host lift and a compatible phase-II family is
a literal physical packing of `G`. -/
theorem isPacking_union_phases (h1 : IsMultiExteriorHub G z E)
    (h2 : IsPhaseTwoFamily G hub base) (hc : IsPhaseCompatible z E hub base) :
    IsPacking G (multiLiftedPacking z E ∪ phaseTwoPacking hub base) :=
  PaperIV.PackingUnion.isPacking_union (isPacking_multiLiftedPacking h1)
    h2.isPacking_phaseTwoPacking hc.pieceEdges_disjoint_phases

omit [DecidableEq I] [Fintype V] [DecidableEq J] in
/-- The covered resource set of the assembled two-phase family. -/
theorem coveredEdges_union_phases :
    coveredEdges (multiLiftedPacking z E ∪ phaseTwoPacking hub base)
      = coveredEdges (multiLiftedPacking z E) ∪ coveredEdges (phaseTwoPacking hub base) :=
  PaperIV.PackingUnion.coveredEdges_union _ _

omit [DecidableEq J] in
/-- **(4')** Under the explicit coverage equality — and only under it — the assembled
two-phase family is an exact literal partition of the physical edge resources of `G`.
No terminal partition is postulated: the coverage hypothesis is supplied. -/
theorem isExactPartition_union_phases (h1 : IsMultiExteriorHub G z E)
    (h2 : IsPhaseTwoFamily G hub base) (hc : IsPhaseCompatible z E hub base)
    (hcov : coveredEdges (multiLiftedPacking z E) ∪ coveredEdges (phaseTwoPacking hub base)
      = graphEdges G) :
    IsExactPartition G (multiLiftedPacking z E ∪ phaseTwoPacking hub base) :=
  PaperIV.PackingUnion.isExactPartition_of_union (isPacking_multiLiftedPacking h1)
    h2.isPacking_phaseTwoPacking hc.pieceEdges_disjoint_phases hcov

omit [DecidableEq I] in
omit [DecidableEq J] in
/-- **(3e)** The exact cardinality ledger of the assembled two-phase family. -/
theorem card_union_phases (h1 : IsMultiExteriorHub G z E)
    (h2 : IsPhaseTwoFamily G hub base) (hc : IsPhaseCompatible z E hub base) :
    (multiLiftedPacking z E ∪ phaseTwoPacking hub base).card
      = (∑ i, (E i).card) + Fintype.card J := by
  rw [Finset.card_union_of_disjoint (hc.disjoint_families h1),
    card_multiLiftedPacking h1, h2.card_phaseTwoPacking]

omit [DecidableEq I] in
omit [DecidableEq J] in
/-- **(3f)** The exact gain ledger of the assembled two-phase family: `2` per phase-I
triangle, `2` per phase-II `K3` and `5` per phase-II `K4`. -/
theorem totalGain_union_phases (h1 : IsMultiExteriorHub G z E)
    (h2 : IsPhaseTwoFamily G hub base) (hc : IsPhaseCompatible z E hub base) :
    totalGain (multiLiftedPacking z E ∪ phaseTwoPacking hub base)
      = 2 * (∑ i, (E i).card) + (2 * (k3Indices hub).card + 5 * (k4Indices hub).card) := by
  rw [PaperIV.PackingUnion.totalGain_union (hc.disjoint_families h1),
    totalGain_multiLiftedPacking h1, h2.totalGain_phaseTwoPacking]

omit [DecidableEq J] in
/-- **(3g)** The exact covered-resource ledger of the assembled two-phase family. -/
theorem card_coveredEdges_union_phases (h1 : IsMultiExteriorHub G z E)
    (h2 : IsPhaseTwoFamily G hub base) (hc : IsPhaseCompatible z E hub base) :
    (coveredEdges (multiLiftedPacking z E ∪ phaseTwoPacking hub base)).card
      = 3 * (∑ i, (E i).card) + (3 * (k3Indices hub).card + 6 * (k4Indices hub).card) := by
  rw [coveredEdges_union_phases,
    Finset.card_union_of_disjoint hc.disjoint_coveredEdges,
    card_coveredEdges_multiLiftedPacking h1, h2.card_coveredEdges_phaseTwoPacking]

/-! ## Non-vacuity

An explicit two-phase instance: one phase-I triangle over the host `0`, one phase-II
`K3` over the hub `{1}` and one phase-II `K4` over the hub pair `{6, 7}`.  All
compatibility hypotheses hold, so the theorems above really do apply. -/

namespace Example

/-- The complete graph on ten vertices. -/
def graph : SimpleGraph (Fin 10) := ⊤

instance : DecidableRel graph.Adj := fun a b => by unfold graph; infer_instance

/-- The single phase-I host. -/
def hosts : Fin 1 → Fin 10 := ![0]

/-- Its base matching. -/
def bases : Fin 1 → Finset (Sym2 (Fin 10)) := ![{s(2, 3)}]

/-- One singleton hub (a `K3` piece) and one hub pair (a `K4` piece). -/
def hubs : Fin 2 → Finset (Fin 10) := ![{1}, {6, 7}]

/-- The two phase-II base edges. -/
def baseEdges : Fin 2 → Sym2 (Fin 10) := ![s(4, 5), s(8, 9)]

theorem isMultiExteriorHub_example : IsMultiExteriorHub graph hosts bases := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    exact ⟨by decide, by unfold IsLiteralMatching; decide, by decide⟩
  · intro a b hab
    fin_cases a
    fin_cases b
    rfl
  · decide
  · decide

theorem isPhaseTwoFamily_example : IsPhaseTwoFamily graph hubs baseEdges := by
  refine ⟨by decide, by decide, ?_, by decide, by decide, by decide⟩
  intro j x hx y hy hxy
  exact hxy

theorem isPhaseCompatible_example : IsPhaseCompatible hosts bases hubs baseEdges :=
  ⟨by decide, by decide⟩

theorem isPacking_example :
    IsPacking graph (multiLiftedPacking hosts bases ∪ phaseTwoPacking hubs baseEdges) :=
  isPacking_union_phases isMultiExteriorHub_example isPhaseTwoFamily_example
    isPhaseCompatible_example

theorem card_example :
    (multiLiftedPacking hosts bases ∪ phaseTwoPacking hubs baseEdges).card = 3 := by
  rw [card_union_phases isMultiExteriorHub_example isPhaseTwoFamily_example
    isPhaseCompatible_example]
  decide

theorem totalGain_example :
    totalGain (multiLiftedPacking hosts bases ∪ phaseTwoPacking hubs baseEdges) = 9 := by
  rw [totalGain_union_phases isMultiExteriorHub_example isPhaseTwoFamily_example
    isPhaseCompatible_example]
  decide

theorem card_coveredEdges_example :
    (coveredEdges (multiLiftedPacking hosts bases ∪ phaseTwoPacking hubs baseEdges)).card
      = 12 := by
  rw [card_coveredEdges_union_phases isMultiExteriorHub_example isPhaseTwoFamily_example
    isPhaseCompatible_example]
  decide

end Example

end PaperIV.RD09PhaseII


