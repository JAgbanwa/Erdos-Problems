import PaperIV.VertexCopySelector
import PaperIV.CloneMeasure

/-!
# A strict rank for fine vertex copies, and its exact scope (DV157–RD09)

The class-copy dynamics of `PaperIV.CloneMeasure` strictly decreases the number
of open-neighbourhood classes.  For the *fine* (one-vertex) copy
`VertexCopy.graph G u v` the situation is genuinely weaker, and this module
determines it exactly.

* `cloneClassCount_vertexCopy_le` : one fine copy never *increases* the number
  of open-neighbourhood classes.  (Classes cannot split: two vertices with the
  same old neighbourhood also have the same new one, and the copy target joins
  the class of the source.)
* `cloneClassCount_vertexCopy_lt` : if the copy **target** `u` is alone in its
  open-neighbourhood class, the count strictly drops, so the fine copy dynamics
  restricted to such targets is well founded.
* `Counterexample` : a literal four-vertex chordal graph with an admissible fine
  copy (distinct, nonadjacent, simplicial source) which changes the graph but
  leaves the clone-class count unchanged.  So the clone-class count is **not**
  a strict rank for arbitrary fine copies; the singleton-target hypothesis
  above cannot be dropped.
-/

namespace PaperIV.VertexCopyRank

open Finset
open PaperIV.CloneMeasure

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The new open neighbourhood of a vertex other than the copy target,
expressed from its old one. -/
def shiftNbhd (u v : V) (S : Finset V) : Finset V :=
  S.erase u ∪ (if v ∈ S then {u} else ∅)

variable (G : SimpleGraph V) [DecidableRel G.Adj] {u v : V}

theorem neighborFinset_copy_of_ne (hnadj : ¬ G.Adj u v) {w : V} (hw : w ≠ u) :
    (VertexCopy.graph G u v).neighborFinset w = shiftNbhd u v (G.neighborFinset w) := by
  ext b
  rw [SimpleGraph.mem_neighborFinset]
  unfold shiftNbhd
  rw [Finset.mem_union, Finset.mem_erase, SimpleGraph.mem_neighborFinset]
  by_cases hb : b = u
  · rw [hb]
    by_cases hvw : G.Adj w v
    · have h1 : (VertexCopy.graph G u v).Adj w u :=
        ((VertexCopy.adj_copied_iff G hnadj w).mpr hvw.symm).symm
      simp [h1, hvw, SimpleGraph.mem_neighborFinset]
    · have h1 : ¬ (VertexCopy.graph G u v).Adj w u := by
        intro h
        exact hvw (((VertexCopy.adj_copied_iff G hnadj w).mp h.symm).symm)
      simp [h1, hvw, SimpleGraph.mem_neighborFinset]
  · constructor
    · intro h
      exact Or.inl ⟨hb, (VertexCopy.adj_of_ne_left_of_ne_right G hw hb).mp h⟩
    · rintro (⟨-, h⟩ | h)
      · exact (VertexCopy.adj_of_ne_left_of_ne_right G hw hb).mpr h
      · exfalso
        by_cases hvw : v ∈ G.neighborFinset w
        · rw [if_pos hvw, Finset.mem_singleton] at h
          exact hb h
        · rw [if_neg hvw] at h
          exact absurd h (by simp)

theorem neighborFinset_copy_source (hne : u ≠ v) (hnadj : ¬ G.Adj u v) :
    (VertexCopy.graph G u v).neighborFinset v = G.neighborFinset v := by
  rw [neighborFinset_copy_of_ne G hnadj (Ne.symm hne), shiftNbhd]
  have hu : u ∉ G.neighborFinset v := by
    simpa [SimpleGraph.mem_neighborFinset] using fun h => hnadj h.symm
  have hv : v ∉ G.neighborFinset v := by simp
  rw [Finset.erase_eq_of_notMem hu, if_neg hv]
  simp

/-- The image of the new neighbourhood map is the shift of the image of the old
one over the vertices other than the target. -/
theorem image_neighborFinset_copy (hne : u ≠ v) (hnadj : ¬ G.Adj u v) :
    (Finset.univ.image fun w : V => (VertexCopy.graph G u v).neighborFinset w)
      = ((Finset.univ.erase u).image fun w : V => G.neighborFinset w).image
          (shiftNbhd u v) := by
  have hstep : (Finset.univ.image fun w : V => (VertexCopy.graph G u v).neighborFinset w)
      = (Finset.univ.erase u).image
          (fun w : V => (VertexCopy.graph G u v).neighborFinset w) := by
    apply Finset.Subset.antisymm
    · intro S hS
      obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp hS
      by_cases hw : w = u
      · subst hw
        refine Finset.mem_image.mpr ⟨v, Finset.mem_erase.mpr ⟨Ne.symm hne, Finset.mem_univ v⟩, ?_⟩
        rw [neighborFinset_copy_source G hne hnadj, VertexCopy.neighborFinset_copied G hnadj]
      · exact Finset.mem_image.mpr ⟨w, Finset.mem_erase.mpr ⟨hw, Finset.mem_univ w⟩, rfl⟩
    · exact Finset.image_subset_image (Finset.erase_subset _ _)
  rw [hstep, Finset.image_image]
  refine Finset.image_congr ?_
  intro w hw
  exact neighborFinset_copy_of_ne G hnadj (Finset.mem_erase.mp hw).1

/-- **A fine copy never increases the number of clone classes.** -/
theorem cloneClassCount_vertexCopy_le (hne : u ≠ v) (hnadj : ¬ G.Adj u v) :
    cloneClassCount (VertexCopy.graph G u v) ≤ cloneClassCount G := by
  unfold cloneClassCount
  rw [image_neighborFinset_copy G hne hnadj]
  calc (((Finset.univ.erase u).image fun w : V => G.neighborFinset w).image
        (shiftNbhd u v)).card
      ≤ ((Finset.univ.erase u).image fun w : V => G.neighborFinset w).card :=
        Finset.card_image_le
    _ ≤ (Finset.univ.image fun w : V => G.neighborFinset w).card :=
        Finset.card_le_card (Finset.image_subset_image (Finset.erase_subset _ _))

/-- **A strict well-founded rank for the fine copy, in its exact scope.**  If
the copy target `u` is the only vertex with its open neighbourhood, one fine
copy strictly decreases the number of clone classes. -/
theorem cloneClassCount_vertexCopy_lt (hne : u ≠ v) (hnadj : ¬ G.Adj u v)
    (hsingle : ∀ w : V, G.neighborFinset w = G.neighborFinset u → w = u) :
    cloneClassCount (VertexCopy.graph G u v) < cloneClassCount G := by
  unfold cloneClassCount
  rw [image_neighborFinset_copy G hne hnadj]
  have hsub : ((Finset.univ.erase u).image fun w : V => G.neighborFinset w)
      ⊆ (Finset.univ.image fun w : V => G.neighborFinset w).erase (G.neighborFinset u) := by
    intro S hS
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hS
    refine Finset.mem_erase.mpr ⟨fun h => (Finset.mem_erase.mp hw).1 (hsingle w h), ?_⟩
    exact Finset.mem_image.mpr ⟨w, Finset.mem_univ w, rfl⟩
  have hmem : G.neighborFinset u ∈ Finset.univ.image fun w : V => G.neighborFinset w :=
    Finset.mem_image.mpr ⟨u, Finset.mem_univ u, rfl⟩
  calc (((Finset.univ.erase u).image fun w : V => G.neighborFinset w).image
        (shiftNbhd u v)).card
      ≤ ((Finset.univ.erase u).image fun w : V => G.neighborFinset w).card :=
        Finset.card_image_le
    _ ≤ ((Finset.univ.image fun w : V => G.neighborFinset w).erase
          (G.neighborFinset u)).card := Finset.card_le_card hsub
    _ < (Finset.univ.image fun w : V => G.neighborFinset w).card :=
        Finset.card_erase_lt_of_mem hmem

/-! ### Chordality from a small edge set -/

/-- A graph with at most three edges has no cycle of length four or more, hence
is vacuously chordal. -/
theorem isChordal_of_card_edgeFinset_le (H : SimpleGraph V) [DecidableRel H.Adj]
    (h : H.edgeFinset.card ≤ 3) : PaperIV.IsChordal H := by
  intro v c hc hlen
  exfalso
  have hsub : c.edges.toFinset ⊆ H.edgeFinset := by
    intro e he
    rw [List.mem_toFinset] at he
    rw [SimpleGraph.mem_edgeFinset]
    exact c.edges_subset_edgeSet he
  have hcard : c.edges.toFinset.card = c.edges.length :=
    List.toFinset_card_of_nodup hc.edges_nodup
  have hlen' : c.edges.length = c.length := c.length_edges
  have := Finset.card_le_card hsub
  omega

/-! ### The clone-class count is not a strict rank for arbitrary fine copies -/

section Counterexample

/-- Adjacency generator of the counterexample: the path `0 — 3 — 2`, with `1`
isolated. -/
def cexRel : Fin 4 → Fin 4 → Prop := fun a b => (a = 0 ∧ b = 3) ∨ (a = 2 ∧ b = 3)

instance : DecidableRel cexRel := fun a b => by unfold cexRel; infer_instance

/-- The four-vertex counterexample graph. -/
def cexG : SimpleGraph (Fin 4) := SimpleGraph.fromRel cexRel

instance : DecidableRel cexG.Adj := fun a b =>
  decidable_of_iff _ (SimpleGraph.fromRel_adj cexRel a b).symm

theorem cexG_edgeFinset_card : cexG.edgeFinset.card = 2 := by decide

theorem cexG_chordal : PaperIV.IsChordal cexG :=
  isChordal_of_card_edgeFinset_le cexG (by rw [cexG_edgeFinset_card]; norm_num)

theorem cexG_isolated : ∀ x : Fin 4, ¬ cexG.Adj 1 x := by decide

theorem cexG_source_simplicial : PaperIV.ChordalBasics.IsSimplicial cexG 1 := by
  intro x hx
  exact absurd hx (cexG_isolated x)

/-- The copy of the simplicial vertex `1` onto the nonadjacent vertex `0` is an
admissible fine copy in the sense of the selector. -/
def cexCopy : PaperIV.VertexCopySelector.AdmissibleVertexCopy cexG where
  target := 0
  source := 1
  distinct := by decide
  nonadjacent := by decide
  source_simplicial := cexG_source_simplicial

/-- The copy really changes the graph: the edge `0 — 3` disappears. -/
theorem cexCopy_changes_graph :
    cexG.Adj 0 3 ∧ ¬ (VertexCopy.graph cexG cexCopy.target cexCopy.source).Adj 0 3 := by
  constructor
  · decide
  · decide

/-- **The clone-class count is not a strict rank for arbitrary fine copies.**
This admissible, graph-changing copy leaves the number of open-neighbourhood
classes unchanged, so no descent argument can use that measure without
restricting the copy target. -/
theorem cexCopy_cloneClassCount_eq :
    cloneClassCount (VertexCopy.graph cexG cexCopy.target cexCopy.source)
      = cloneClassCount cexG := by decide

end Counterexample

end PaperIV.VertexCopyRank
