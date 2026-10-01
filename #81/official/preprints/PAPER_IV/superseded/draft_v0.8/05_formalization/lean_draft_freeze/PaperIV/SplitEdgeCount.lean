import PaperIV.Model
import PaperIV.SplitUniformIncidence

/-!
# The literal edge set of a complete split graph

For two disjoint finite vertex sets `Core` (a clique) and `Hosts` (independent), the
complete split graph `PaperIV.SplitUniformIncidence.splitGraph Core Hosts` has exactly
two kinds of edges:

* the **inner** edges, i.e. the non-diagonal pairs inside `Core`
  (`PaperIV.Model.pieceEdges Core`), of which there are `C(k,2)` with `k = #Core`;
* the **cross** edges `crossEdges Core Hosts`, one for each core/host pair, of which
  there are `k * h` with `h = #Hosts`.

Everything here is literal and finite; nothing is assumed about the sizes.
-/

namespace PaperIV.SplitEdgeCount

open Finset PaperIV.Model PaperIV.SplitUniformIncidence

variable {V : Type*} [Fintype V] [DecidableEq V]

instance splitGraphDecidableRel (Core Hosts : Finset V) :
    DecidableRel (splitGraph Core Hosts).Adj := by
  intro x y
  unfold splitGraph
  infer_instance

/-- The cross edges of the split graph: one edge per core/host pair. -/
def crossEdges (Core Hosts : Finset V) : Finset (Sym2 V) :=
  (Core ×ˢ Hosts).image fun p => s(p.1, p.2)

omit [Fintype V] in
theorem mem_crossEdges {Core Hosts : Finset V} {e : Sym2 V} :
    e ∈ crossEdges Core Hosts ↔ ∃ x ∈ Core, ∃ z ∈ Hosts, e = s(x, z) := by
  simp only [crossEdges, Finset.mem_image, Finset.mem_product, Prod.exists]
  constructor
  · rintro ⟨x, z, ⟨hx, hz⟩, rfl⟩; exact ⟨x, hx, z, hz, rfl⟩
  · rintro ⟨x, hx, z, hz, rfl⟩; exact ⟨x, z, ⟨hx, hz⟩, rfl⟩

omit [Fintype V] in
theorem card_crossEdges {Core Hosts : Finset V} (hd : Disjoint Core Hosts) :
    (crossEdges Core Hosts).card = Core.card * Hosts.card := by
  rw [crossEdges, Finset.card_image_of_injOn, Finset.card_product]
  rintro ⟨x, z⟩ hp ⟨x', z'⟩ hp' hpp
  simp only [Finset.mem_coe, Finset.mem_product] at hp hp'
  simp only [Sym2.eq_iff] at hpp
  rcases hpp with ⟨rfl, rfl⟩ | ⟨h1, h2⟩
  · rfl
  · have hxH : x ∈ Hosts := by rw [h1]; exact hp'.2
    exact absurd hxH (Finset.disjoint_left.mp hd hp.1)

omit [Fintype V] in
theorem disjoint_inner_cross {Core Hosts : Finset V} (hd : Disjoint Core Hosts) :
    Disjoint (pieceEdges Core) (crossEdges Core Hosts) := by
  rw [Finset.disjoint_left]
  intro e he hc
  rw [mem_crossEdges] at hc
  obtain ⟨x, hx, z, hz, rfl⟩ := hc
  rw [mem_pieceEdges_mk] at he
  exact (Finset.disjoint_left.mp hd he.2.1) hz

theorem graphEdges_splitGraph {Core Hosts : Finset V} (hd : Disjoint Core Hosts) :
    graphEdges (splitGraph Core Hosts) = pieceEdges Core ∪ crossEdges Core Hosts := by
  ext e
  induction e with
  | _ a b =>
    rw [mem_graphEdges, SimpleGraph.mem_edgeSet, splitGraph_adj_iff, Finset.mem_union,
      mem_pieceEdges_mk, mem_crossEdges]
    constructor
    · rintro ⟨hne, hcase | hcase | hcase⟩
      · exact Or.inl ⟨hcase.1, hcase.2, hne⟩
      · exact Or.inr ⟨a, hcase.1, b, hcase.2, rfl⟩
      · exact Or.inr ⟨b, hcase.2, a, hcase.1, Sym2.eq_swap⟩
    · rintro (⟨ha, hb, hab⟩ | ⟨x, hx, z, hz, hxz⟩)
      · exact ⟨hab, Or.inl ⟨ha, hb⟩⟩
      · rw [Sym2.eq_iff] at hxz
        have hne : x ≠ z := fun h => (Finset.disjoint_left.mp hd hx) (h ▸ hz)
        rcases hxz with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨hne, Or.inr (Or.inl ⟨hx, hz⟩)⟩
        · exact ⟨hne.symm, Or.inr (Or.inr ⟨hz, hx⟩)⟩

/-- The exact edge count of the complete split graph: `C(k,2)` inner edges and `k*h`
cross edges. -/
theorem card_graphEdges_splitGraph {Core Hosts : Finset V} (hd : Disjoint Core Hosts) :
    (graphEdges (splitGraph Core Hosts)).card
      = Core.card.choose 2 + Core.card * Hosts.card := by
  rw [graphEdges_splitGraph hd, Finset.card_union_of_disjoint (disjoint_inner_cross hd),
    card_pieceEdges, card_crossEdges hd]

theorem crossEdges_subset_graphEdges {Core Hosts : Finset V} (hd : Disjoint Core Hosts) :
    crossEdges Core Hosts ⊆ graphEdges (splitGraph Core Hosts) := by
  rw [graphEdges_splitGraph hd]; exact Finset.subset_union_right

theorem innerEdges_subset_graphEdges {Core Hosts : Finset V} (hd : Disjoint Core Hosts) :
    pieceEdges Core ⊆ graphEdges (splitGraph Core Hosts) := by
  rw [graphEdges_splitGraph hd]; exact Finset.subset_union_left

end PaperIV.SplitEdgeCount
