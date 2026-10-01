import PaperIV.SplitEdgeCount
import PaperIV.PhysicalCompletion

/-!
# The defective complete-split comparator: the graph and its edge set

Fix three pairwise disjoint finite vertex sets

* `Core`   — a clique of `r` vertices,
* `Def`    — `s` *defective* vertices, joined to no core vertex and to no other
  defective vertex,
* `Hosts`  — `h` independent hosts, joined to **every** vertex of `Core ∪ Def`.

The resulting graph `defSplitGraph Core Def Hosts` is the complete split graph
`splitGraph Core Hosts` together with the complete bipartite graph between `Def`
and `Hosts`.  Its edge set therefore splits as

`pieceEdges Core ∪ crossEdges (Core ∪ Def) Hosts`,

of sizes `C(r,2)` and `(r+s)*h`.

This module fixes the definitions and proves the literal edge decomposition and
the two local structural facts that the extremal analysis uses: hosts are
pairwise non-adjacent, and every neighbour of a defective vertex is a host.
-/

namespace PaperIV.DefectComparatorGraph

open Finset
open PaperIV.Model PaperIV.SplitUniformIncidence PaperIV.SplitEdgeCount

variable {V : Type*} [DecidableEq V]

/-- The chromatic index of the complete graph `K_r`: `0` for `r ≤ 1`, `r - 1` for
even `r`, and `r` for odd `r ≥ 3`. -/
def chiPrime (r : ℕ) : ℕ := if r ≤ 1 then 0 else if r % 2 = 0 then r - 1 else r

@[simp] theorem chiPrime_zero : chiPrime 0 = 0 := rfl
@[simp] theorem chiPrime_one : chiPrime 1 = 0 := rfl

theorem chiPrime_even {r : ℕ} (h2 : 2 ≤ r) (hpar : r % 2 = 0) : chiPrime r = r - 1 := by
  unfold chiPrime
  rw [if_neg (by omega), if_pos hpar]

theorem chiPrime_odd {r : ℕ} (h2 : 2 ≤ r) (hpar : r % 2 = 1) : chiPrime r = r := by
  unfold chiPrime
  rw [if_neg (by omega), if_neg (by omega)]

/-- The defective complete-split comparator. -/
def defSplitGraph (Core Def Hosts : Finset V) : SimpleGraph V where
  Adj x y := x ≠ y ∧ ((x ∈ Core ∧ y ∈ Core) ∨
    (x ∈ Core ∪ Def ∧ y ∈ Hosts) ∨ (x ∈ Hosts ∧ y ∈ Core ∪ Def))
  symm := by
    rintro x y ⟨hne, h⟩
    exact ⟨hne.symm, by tauto⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance defSplitGraphDecidableRel (Core Def Hosts : Finset V) :
    DecidableRel (defSplitGraph Core Def Hosts).Adj := by
  intro x y
  unfold defSplitGraph
  infer_instance

theorem defSplitGraph_adj_iff {Core Def Hosts : Finset V} {x y : V} :
    (defSplitGraph Core Def Hosts).Adj x y ↔
      x ≠ y ∧ ((x ∈ Core ∧ y ∈ Core) ∨
        (x ∈ Core ∪ Def ∧ y ∈ Hosts) ∨ (x ∈ Hosts ∧ y ∈ Core ∪ Def)) :=
  Iff.rfl

theorem defSplitGraph_adj_inner {Core Def Hosts : Finset V} {x y : V}
    (hx : x ∈ Core) (hy : y ∈ Core) (hxy : x ≠ y) :
    (defSplitGraph Core Def Hosts).Adj x y :=
  ⟨hxy, Or.inl ⟨hx, hy⟩⟩

theorem defSplitGraph_adj_cross {Core Def Hosts : Finset V}
    (hd : Disjoint (Core ∪ Def) Hosts) {x z : V}
    (hx : x ∈ Core ∪ Def) (hz : z ∈ Hosts) : (defSplitGraph Core Def Hosts).Adj x z := by
  refine ⟨?_, Or.inr (Or.inl ⟨hx, hz⟩)⟩
  intro hEq
  exact (Finset.disjoint_left.mp hd hx) (hEq ▸ hz)

/-- The comparator contains the complete split graph on `Core` and `Hosts`. -/
theorem splitGraph_le_defSplitGraph (Core Def Hosts : Finset V) :
    splitGraph Core Hosts ≤ defSplitGraph Core Def Hosts := by
  rintro x y ⟨hne, hcase⟩
  refine ⟨hne, ?_⟩
  rcases hcase with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨Finset.mem_union_left _ h.1, h.2⟩)
  · exact Or.inr (Or.inr ⟨h.1, Finset.mem_union_left _ h.2⟩)

/-- Two hosts are never adjacent. -/
theorem not_adj_of_mem_hosts {Core Def Hosts : Finset V}
    (hd : Disjoint (Core ∪ Def) Hosts) {z w : V} (hz : z ∈ Hosts) (hw : w ∈ Hosts) :
    ¬ (defSplitGraph Core Def Hosts).Adj z w := by
  rintro ⟨-, hcase⟩
  rcases hcase with h | h | h
  · exact (Finset.disjoint_left.mp hd (Finset.mem_union_left _ h.1)) hz
  · exact (Finset.disjoint_left.mp hd h.1) hz
  · exact (Finset.disjoint_left.mp hd h.2) hw

/-- Every neighbour of a defective vertex is a host. -/
theorem mem_hosts_of_adj_def {Core Def Hosts : Finset V}
    (hCD : Disjoint Core Def) (hDH : Disjoint Def Hosts)
    {d x : V} (hdD : d ∈ Def) (hadj : (defSplitGraph Core Def Hosts).Adj d x) :
    x ∈ Hosts := by
  have hdC : d ∉ Core := Finset.disjoint_right.mp hCD hdD
  have hdH : d ∉ Hosts := Finset.disjoint_left.mp hDH hdD
  obtain ⟨-, hcase⟩ := hadj
  rcases hcase with h | h | h
  · exact absurd h.1 hdC
  · exact h.2
  · exact absurd h.1 hdH

/-- The literal edge set of the comparator. -/
theorem graphEdges_defSplitGraph [Fintype V] {Core Def Hosts : Finset V}
    (hd : Disjoint (Core ∪ Def) Hosts) :
    graphEdges (defSplitGraph Core Def Hosts)
      = pieceEdges Core ∪ crossEdges (Core ∪ Def) Hosts := by
  ext e
  induction e with
  | _ a b =>
    have hunion : s(a, b) ∈ pieceEdges Core ∪ crossEdges (Core ∪ Def) Hosts ↔
        s(a, b) ∈ pieceEdges Core ∨ s(a, b) ∈ crossEdges (Core ∪ Def) Hosts := Finset.mem_union
    rw [mem_graphEdges, SimpleGraph.mem_edgeSet, defSplitGraph_adj_iff, hunion,
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

theorem disjoint_inner_cross_def {Core Def Hosts : Finset V}
    (hd : Disjoint (Core ∪ Def) Hosts) :
    Disjoint (pieceEdges Core) (crossEdges (Core ∪ Def) Hosts) := by
  rw [Finset.disjoint_left]
  intro e he hc
  rw [mem_crossEdges] at hc
  obtain ⟨x, hx, z, hz, rfl⟩ := hc
  rw [mem_pieceEdges_mk] at he
  exact (Finset.disjoint_left.mp hd (Finset.mem_union_left _ he.2.1)) hz

/-- The exact edge count: `C(r,2)` core edges and `(r+s)*h` links. -/
theorem card_graphEdges_defSplitGraph [Fintype V] {Core Def Hosts : Finset V}
    (hCD : Disjoint Core Def) (hd : Disjoint (Core ∪ Def) Hosts) :
    (graphEdges (defSplitGraph Core Def Hosts)).card
      = Core.card.choose 2 + (Core.card + Def.card) * Hosts.card := by
  rw [graphEdges_defSplitGraph hd,
    Finset.card_union_of_disjoint (disjoint_inner_cross_def hd),
    card_pieceEdges, card_crossEdges hd, Finset.card_union_of_disjoint hCD]

theorem crossEdges_subset_graphEdges_def [Fintype V] {Core Def Hosts : Finset V}
    (hd : Disjoint (Core ∪ Def) Hosts) :
    crossEdges (Core ∪ Def) Hosts ⊆ graphEdges (defSplitGraph Core Def Hosts) := by
  rw [graphEdges_defSplitGraph hd]; exact Finset.subset_union_right

theorem innerEdges_subset_graphEdges_def [Fintype V] {Core Def Hosts : Finset V}
    (hd : Disjoint (Core ∪ Def) Hosts) :
    pieceEdges Core ⊆ graphEdges (defSplitGraph Core Def Hosts) := by
  rw [graphEdges_defSplitGraph hd]; exact Finset.subset_union_left

end PaperIV.DefectComparatorGraph
