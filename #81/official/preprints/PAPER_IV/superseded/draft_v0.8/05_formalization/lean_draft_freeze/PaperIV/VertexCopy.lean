import PaperIV.ChordalBasics
import PaperIV.ChordalCopy
import PaperIV.CopyPathNearEntry

/-!
# One-vertex copying for the near-regime copy path (DV157–RD09)

This module formalizes the fine one-vertex copy move.  Given distinct,
nonadjacent `u v`, it changes only pairs incident with `u` and installs the
old neighbourhood of `v` at `u`.
-/

namespace PaperIV.VertexCopy

open Finset
open scoped symmDiff
open SimpleGraph
open PaperIV.EditMetric

variable {V : Type*} [DecidableEq V]

/-- The adjacency relation of the one-vertex copy. -/
def rel (G : SimpleGraph V) (u v : V) (a b : V) : Prop :=
  if a = u then G.Adj v b else if b = u then G.Adj v a else G.Adj a b

instance instDecidableRel (G : SimpleGraph V) [DecidableRel G.Adj] (u v a b : V) :
    Decidable (rel G u v a b) := by
  unfold rel
  infer_instance

/-- Copy vertex `v` onto `u`, retaining irreflexivity explicitly. -/
def graph (G : SimpleGraph V) (u v : V) : SimpleGraph V where
  Adj a b := a ≠ b ∧ rel G u v a b
  symm := by
    rintro a b ⟨hne, h⟩
    refine ⟨hne.symm, ?_⟩
    unfold rel at h ⊢
    by_cases hau : a = u
    · by_cases hbu : b = u
      · exact absurd (hau.trans hbu.symm) hne
      · simp only [hau, hbu, if_true, if_false] at h ⊢
        simpa using h
    · by_cases hbu : b = u
      · simp only [hau, hbu, if_true, if_false] at h ⊢
        simpa using h
      · simp only [hau, hbu, if_false] at h ⊢
        exact h.symm
  loopless := ⟨fun _ h => h.1 rfl⟩

instance instDecidableRelGraphAdj (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V) :
    DecidableRel (graph G u v).Adj := fun a b =>
  inferInstanceAs (Decidable (a ≠ b ∧ rel G u v a b))

theorem graph_adj_iff (G : SimpleGraph V) (u v a b : V) :
    (graph G u v).Adj a b ↔ a ≠ b ∧ rel G u v a b := Iff.rfl

theorem graph_not_adj_self (G : SimpleGraph V) (u v a : V) : ¬ (graph G u v).Adj a a :=
  fun h => h.1 rfl

/-- No edge avoiding `u` changes. -/
theorem adj_of_ne_left_of_ne_right (G : SimpleGraph V) {u v a b : V}
    (ha : a ≠ u) (hb : b ≠ u) : (graph G u v).Adj a b ↔ G.Adj a b := by
  constructor
  · rintro ⟨-, h⟩
    unfold rel at h
    simpa only [ha, hb, if_false] using h
  · intro h
    refine ⟨h.ne, ?_⟩
    unfold rel
    simpa only [ha, hb, if_false] using h

/-- The new neighbours of `u` are the old neighbours of `v`. -/
theorem adj_copied_iff (G : SimpleGraph V) {u v : V} (hnadj : ¬ G.Adj u v) (b : V) :
    (graph G u v).Adj u b ↔ G.Adj v b := by
  constructor
  · rintro ⟨-, h⟩
    unfold rel at h
    simpa using h
  · intro h
    have hbu : b ≠ u := by
      rintro rfl
      exact hnadj (G.symm h)
    refine ⟨fun hub => hbu hub.symm, ?_⟩
    unfold rel
    simpa using h

theorem neighborSet_copied (G : SimpleGraph V) {u v : V} (hnadj : ¬ G.Adj u v) :
    (graph G u v).neighborSet u = G.neighborSet v := by
  ext b
  simpa only [SimpleGraph.mem_neighborSet] using adj_copied_iff G hnadj b

variable [Fintype V]

theorem neighborFinset_copied (G : SimpleGraph V) [DecidableRel G.Adj] {u v : V}
    (hnadj : ¬ G.Adj u v) :
    (graph G u v).neighborFinset u = G.neighborFinset v := by
  ext b
  simpa only [SimpleGraph.mem_neighborFinset] using adj_copied_iff G hnadj b

/-- The unordered edges whose status changes under one copy. -/
def changedEdges (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V) : Finset (Sym2 V) :=
  G.edgeFinset ∆ (graph G u v).edgeFinset

theorem mem_changedEdges_incident (G : SimpleGraph V) [DecidableRel G.Adj] {u v : V}
    {e : Sym2 V} (he : e ∈ changedEdges G u v) : u ∈ e := by
  induction e using Sym2.ind with
  | _ a b =>
    by_cases ha : a = u
    · simp [ha]
    by_cases hb : b = u
    · simp [hb]
    have hmem : s(a, b) ∈ (graph G u v).edgeFinset ↔ s(a, b) ∈ G.edgeFinset := by
      simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using
        adj_of_ne_left_of_ne_right G ha hb
    rcases Finset.mem_symmDiff.mp he with h | h
    · exact absurd (hmem.mpr h.1) h.2
    · exact absurd (hmem.mp h.1) h.2

theorem not_mem_changedEdges_pair (G : SimpleGraph V) [DecidableRel G.Adj] {u v : V}
    (hnadj : ¬ G.Adj u v) : s(u, v) ∉ changedEdges G u v := by
  have hold : s(u, v) ∉ G.edgeFinset := by
    simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using hnadj
  have hnew : s(u, v) ∉ (graph G u v).edgeFinset := by
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    intro hadj
    exact G.irrefl ((adj_copied_iff G hnadj v).mp hadj)
  intro he
  rcases Finset.mem_symmDiff.mp he with h | h
  · exact hold h.1
  · exact hnew h.1

theorem exists_eq_of_mem_changedEdges (G : SimpleGraph V) [DecidableRel G.Adj] {u v : V}
    (hnadj : ¬ G.Adj u v) {e : Sym2 V} (he : e ∈ changedEdges G u v) :
    ∃ w : V, w ≠ u ∧ w ≠ v ∧ e = s(u, w) := by
  have hu : u ∈ e := mem_changedEdges_incident G he
  obtain ⟨w, rfl⟩ := Sym2.mem_iff_exists.mp hu
  refine ⟨w, ?_, ?_, rfl⟩
  · rintro rfl
    have : s(w, w) ∉ G.edgeFinset := by simp
    have hnew : s(w, w) ∉ (graph G w v).edgeFinset := by simp
    rcases Finset.mem_symmDiff.mp he with h | h
    · exact this h.1
    · exact hnew h.1
  · rintro rfl
    exact not_mem_changedEdges_pair G hnadj he

theorem changedEdges_subset_image (G : SimpleGraph V) [DecidableRel G.Adj] {u v : V}
    (hnadj : ¬ G.Adj u v) :
    changedEdges G u v ⊆ ((Finset.univ.erase u).erase v).image fun w => s(u, w) := by
  intro e he
  obtain ⟨w, hwu, hwv, rfl⟩ := exists_eq_of_mem_changedEdges G hnadj he
  exact Finset.mem_image.mpr ⟨w, by simp [hwu, hwv], rfl⟩

theorem card_changedEdges_le (G : SimpleGraph V) [DecidableRel G.Adj] {u v : V}
    (hne : u ≠ v) (hnadj : ¬ G.Adj u v) :
    (changedEdges G u v).card ≤ Fintype.card V - 2 := by
  have hcard : (((Finset.univ.erase u).erase v)).card = Fintype.card V - 2 := by
    rw [Finset.card_erase_of_mem (by simp [Ne.symm hne]), Finset.card_erase_of_mem (by simp),
      Finset.card_univ]
    omega
  calc (changedEdges G u v).card
      ≤ (((Finset.univ.erase u).erase v).image fun w => s(u, w)).card :=
        Finset.card_le_card (changedEdges_subset_image G hnadj)
    _ ≤ ((Finset.univ.erase u).erase v).card := Finset.card_image_le
    _ = Fintype.card V - 2 := hcard

theorem isChordal_graph (G : SimpleGraph V) {u v : V} (hnadj : ¬ G.Adj u v)
    (hG : IsChordal G) (hv : G.IsClique (G.neighborSet v)) :
    IsChordal (graph G u v) := by
  intro v0 c hc hlen
  by_cases hu : u ∈ c.support
  · obtain ⟨a, b, hua, hub, hab, hnab⟩ := PaperIV.cycle_two_neighbors c hc hlen hu
    have hadja : G.Adj v a := (adj_copied_iff G hnadj a).mp (c.adj_of_mem_edges hua)
    have hadjb : G.Adj v b := (adj_copied_iff G hnadj b).mp (c.adj_of_mem_edges hub)
    have hau : a ≠ u := by
      rintro rfl
      exact hnadj (G.symm hadja)
    have hbu : b ≠ u := by
      rintro rfl
      exact hnadj (G.symm hadjb)
    have hchord : G.Adj a b := hv hadja hadjb hab
    exact ⟨a, b, c.snd_mem_support_of_mem_edges hua, c.snd_mem_support_of_mem_edges hub,
      (adj_of_ne_left_of_ne_right G hau hbu).mpr hchord, hnab⟩
  · have hEsub : ∀ e ∈ c.edges, e ∈ G.edgeSet := by
      intro e he
      refine Sym2.ind (fun x y he => ?_) e he
      have hx := c.fst_mem_support_of_mem_edges he
      have hy := c.snd_mem_support_of_mem_edges he
      have hxu : x ≠ u := by rintro rfl; exact hu hx
      have hyu : y ≠ u := by rintro rfl; exact hu hy
      rw [SimpleGraph.mem_edgeSet]
      exact (adj_of_ne_left_of_ne_right G hxu hyu).mp (c.adj_of_mem_edges he)
    have hcH : (c.transfer G hEsub).IsCycle := hc.transfer hEsub
    have hlenH : 4 ≤ (c.transfer G hEsub).length := by
      rw [SimpleGraph.Walk.length_transfer]
      exact hlen
    obtain ⟨x, y, hx, hy, hadj, hedge⟩ := hG (c.transfer G hEsub) hcH hlenH
    rw [SimpleGraph.Walk.support_transfer] at hx hy
    rw [SimpleGraph.Walk.edges_transfer] at hedge
    have hxu : x ≠ u := by rintro rfl; exact hu hx
    have hyu : y ≠ u := by rintro rfl; exact hu hy
    exact ⟨x, y, hx, hy, (adj_of_ne_left_of_ne_right G hxu hyu).mpr hadj, hedge⟩

theorem isChordal_graph_of_isSimplicial (G : SimpleGraph V) {u v : V}
    (hnadj : ¬ G.Adj u v) (hG : IsChordal G)
    (hv : PaperIV.ChordalBasics.IsSimplicial G v) :
    IsChordal (graph G u v) :=
  isChordal_graph G hnadj hG hv

theorem editDist_edgeFinset_eq_card_changedEdges (G : SimpleGraph V) [DecidableRel G.Adj]
    (u v : V) :
    editDist G.edgeFinset (graph G u v).edgeFinset = (changedEdges G u v).card := rfl

theorem editDist_edgeFinset_le (G : SimpleGraph V) [DecidableRel G.Adj] {u v : V}
    (hne : u ≠ v) (hnadj : ¬ G.Adj u v) :
    editDist G.edgeFinset (graph G u v).edgeFinset ≤ Fintype.card V - 2 :=
  card_changedEdges_le G hne hnadj

theorem editDist_edgeFinset_le' (G : SimpleGraph V) [DecidableRel G.Adj] {u v : V}
    (hne : u ≠ v) (hnadj : ¬ G.Adj u v) :
    editDist (graph G u v).edgeFinset G.edgeFinset ≤ Fintype.card V - 2 := by
  rw [editDist_comm]
  exact editDist_edgeFinset_le G hne hnadj

theorem normalized_editDist_le_inv (G : SimpleGraph V) [DecidableRel G.Adj] {u v : V}
    (hn : 2 ≤ Fintype.card V) (hne : u ≠ v) (hnadj : ¬ G.Adj u v) :
    (editDist G.edgeFinset (graph G u v).edgeFinset : ℚ) / (Fintype.card V : ℚ) ^ 2
      ≤ 1 / (Fintype.card V : ℚ) := by
  have hstep : (editDist G.edgeFinset (graph G u v).edgeFinset : ℚ)
      ≤ ((Fintype.card V - 2 : ℕ) : ℚ) := by
    exact_mod_cast editDist_edgeFinset_le G hne hnadj
  calc (editDist G.edgeFinset (graph G u v).edgeFinset : ℚ) / (Fintype.card V : ℚ) ^ 2
      ≤ ((Fintype.card V - 2 : ℕ) : ℚ) / (Fintype.card V : ℚ) ^ 2 :=
        div_le_div_of_nonneg_right hstep (by positivity)
    _ ≤ 1 / (Fintype.card V : ℚ) :=
        PaperIV.CopyPathWindow.copy_step_normalized_le_inv _ hn

omit [DecidableEq V] in
theorem edgeFinset_congr {G H : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel H.Adj]
    (h : G = H) : G.edgeFinset = H.edgeFinset := by
  ext e
  simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, h]

theorem exists_window_and_near_value_of_vertexCopy_path {N : ℕ}
    (hn : 2 ≤ Fintype.card V)
    (Gs : Fin (N + 1) → SimpleGraph V) [inst : ∀ i, DecidableRel (Gs i).Adj]
    (src tgt : Fin N → V)
    (hcopy : ∀ i : Fin N, Gs i.succ = graph (Gs i.castSucc) (tgt i) (src i))
    (hne : ∀ i : Fin N, tgt i ≠ src i)
    (hnadj : ∀ i : Fin N, ¬ (Gs i.castSucc).Adj (tgt i) (src i))
    (F : Finset (Finset (Sym2 V))) (hF : F.Nonempty)
    (r Q δ : ℚ) (value : Fin (N + 1) → ℚ)
    (hstart : r ≤ famDistNorm F hF (Gs 0).edgeFinset ((Fintype.card V : ℚ) ^ 2))
    (hend : famDistNorm F hF (Gs (Fin.last N)).edgeFinset ((Fintype.card V : ℚ) ^ 2) < r)
    (hupper : ∀ i, value i ≤ Q)
    (hmono : ∀ i, value 0 ≤ value i)
    (hnear : Q - value 0 ≤ δ) :
    ∃ j : Fin (N + 1),
      (∀ i : Fin (N + 1),
          famDistNorm F hF (Gs i).edgeFinset ((Fintype.card V : ℚ) ^ 2) < r → j ≤ i) ∧
      r - 1 / (Fintype.card V : ℚ)
          ≤ famDistNorm F hF (Gs j).edgeFinset ((Fintype.card V : ℚ) ^ 2) ∧
      famDistNorm F hF (Gs j).edgeFinset ((Fintype.card V : ℚ) ^ 2) < r ∧
      Q - δ ≤ value j := by
  refine PaperIV.CopyPathNearEntry.exists_window_and_near_value_of_copy_steps
    (Fintype.card V) hn F hF (fun i => (Gs i).edgeFinset) r Q δ value hstart hend ?_
    hupper hmono hnear
  intro i
  have hEq : (Gs i.succ).edgeFinset = (graph (Gs i.castSucc) (tgt i) (src i)).edgeFinset :=
    edgeFinset_congr (hcopy i)
  show editDist (Gs i.succ).edgeFinset (Gs i.castSucc).edgeFinset ≤ Fintype.card V - 2
  rw [hEq]
  exact editDist_edgeFinset_le' (Gs i.castSucc) (hne i) (hnadj i)

end PaperIV.VertexCopy
