import PaperIV.PhysicalCompletion
import PaperIV.SplitEdgeCount

/-!
# The exact obstruction to covering a complete split graph by `K3`/`K4` pieces

The construction of `PaperIV.SplitTriangleFactor` covers every cross edge of a complete
split graph as soon as the number of hosts is at most `#Core - 1`.  This module proves
that this restriction is *necessary*, and quantifies the failure exactly.

The mechanism is a strictly local resource inequality.  A piece of a `K3`/`K4` packing
of `splitGraph Core Hosts` is a clique with at most one host, so it carries `c` cross
edges and `C(c,2)` inner edges where `c` is its number of core vertices, and
`c ≤ 2 * C(c,2)` whenever `c ≥ 2`.  Hence in *any* `K3`/`K4` packing

    #(covered cross edges) ≤ 2 * #(covered inner edges) ≤ 2 * C(k,2) = k * (k-1) .

Since the split graph has `k * h` cross edges, at least `k * h - k * (k-1)` edges are
left uncovered.  In particular, for `h ≥ k` the uncovered set has size at least
`k * (h - k + 1)`, which is *not* linearly bounded in the size of the graph: the
"cover all but linearly many edges" target is false outside the regime `h ≤ k - 1`
in which `PaperIV.SplitTriangleFactor` works.
-/

namespace PaperIV.SplitPackingObstruction

open Finset PaperIV.Model PaperIV.SplitUniformIncidence PaperIV.SplitEdgeCount
open PaperIV.PhysicalCompletion

variable {V : Type*} [Fintype V] [DecidableEq V] {Core Hosts : Finset V}

/-! ## Local structure of a single piece -/

/-- A clique of the complete split graph with at least two vertices is contained in
`Core ∪ Hosts`: vertices outside both sides are isolated. -/
theorem subset_core_union_hosts {s : Finset V}
    (hclique : (splitGraph Core Hosts).IsClique (s : Set V)) (hcard : 2 ≤ s.card) :
    s ⊆ Core ∪ Hosts := by
  intro v hv
  obtain ⟨u, hu, huv⟩ : ∃ u ∈ s, u ≠ v := by
    by_contra hcon
    push_neg at hcon
    have : s ⊆ {v} := fun x hx => Finset.mem_singleton.mpr (hcon x hx)
    have := Finset.card_le_card this
    simp at this
    omega
  have hadj : (splitGraph Core Hosts).Adj v u := hclique hv hu (Ne.symm huv)
  rcases hadj.2 with h | h | h
  · exact Finset.mem_union_left _ h.1
  · exact Finset.mem_union_left _ h.1
  · exact Finset.mem_union_right _ h.1

/-- A clique of the complete split graph contains at most one host. -/
theorem card_inter_hosts_le_one (hd : Disjoint Core Hosts) {s : Finset V}
    (hclique : (splitGraph Core Hosts).IsClique (s : Set V)) : (s ∩ Hosts).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  rw [Finset.mem_inter] at ha hb
  by_contra hab
  exact splitGraph_not_adj_hosts hd ha.2 hb.2 (hclique ha.1 hb.1 hab)

variable (Core Hosts) in
/-- The cross resources of a piece. -/
def crossPart (s : Finset V) : Finset (Sym2 V) :=
  (pieceEdges s).filter fun e => e ∈ crossEdges Core Hosts

variable (Core) in
/-- The inner resources of a piece. -/
def innerPart (s : Finset V) : Finset (Sym2 V) :=
  (pieceEdges s).filter fun e => e ∈ pieceEdges Core

omit [Fintype V] in
theorem innerPart_eq (s : Finset V) : innerPart Core s = pieceEdges (s ∩ Core) := by
  ext e
  simp only [innerPart, Finset.mem_filter, mem_pieceEdges]
  constructor
  · rintro ⟨⟨hs, hd⟩, ⟨hc, -⟩⟩
    exact ⟨fun a ha => Finset.mem_inter.mpr ⟨hs a ha, hc a ha⟩, hd⟩
  · rintro ⟨hsc, hd⟩
    exact ⟨⟨fun a ha => (Finset.mem_inter.mp (hsc a ha)).1, hd⟩,
      ⟨fun a ha => (Finset.mem_inter.mp (hsc a ha)).2, hd⟩⟩

omit [Fintype V] in
/-- With a host `z` in the piece, the cross resources of the piece are exactly the pairs
`{x, z}` with `x` a core vertex of the piece. -/
theorem crossPart_eq_image (hd : Disjoint Core Hosts) {s : Finset V} {z : V}
    (hz : s ∩ Hosts = {z}) :
    crossPart Core Hosts s = (s ∩ Core).image fun x => s(x, z) := by
  have hzs : z ∈ s ∧ z ∈ Hosts := by
    have : z ∈ s ∩ Hosts := by rw [hz]; exact Finset.mem_singleton_self z
    exact Finset.mem_inter.mp this
  ext e
  simp only [crossPart, Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨hpe, hcross⟩
    rw [mem_crossEdges] at hcross
    obtain ⟨x, hx, w, hw, rfl⟩ := hcross
    rw [mem_pieceEdges_mk] at hpe
    have hws : w ∈ s ∩ Hosts := Finset.mem_inter.mpr ⟨hpe.2.1, hw⟩
    rw [hz, Finset.mem_singleton] at hws
    subst hws
    exact ⟨x, Finset.mem_inter.mpr ⟨hpe.1, hx⟩, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    rw [Finset.mem_inter] at hx
    have hxz : x ≠ z := fun h => (Finset.disjoint_left.mp hd hx.2) (h ▸ hzs.2)
    refine ⟨?_, ?_⟩
    · rw [mem_pieceEdges_mk]; exact ⟨hx.1, hzs.1, hxz⟩
    · rw [mem_crossEdges]; exact ⟨x, hx.2, z, hzs.2, rfl⟩

omit [Fintype V] in
theorem card_crossPart_of_host (hd : Disjoint Core Hosts) {s : Finset V} {z : V}
    (hz : s ∩ Hosts = {z}) : (crossPart Core Hosts s).card = (s ∩ Core).card := by
  have hzH : z ∈ Hosts := by
    have : z ∈ s ∩ Hosts := by rw [hz]; exact Finset.mem_singleton_self z
    exact (Finset.mem_inter.mp this).2
  rw [crossPart_eq_image hd hz, Finset.card_image_of_injOn]
  intro x hx y hy hxy
  simp only [Finset.mem_coe, Finset.mem_inter] at hx hy
  simp only [Sym2.eq_iff] at hxy
  rcases hxy with ⟨rfl, -⟩ | ⟨rfl, hzy⟩
  · rfl
  · exact absurd hzH (Finset.disjoint_left.mp hd hx.2)

omit [Fintype V] in
/-- Without a host the piece carries no cross resource. -/
theorem crossPart_eq_empty_of_no_host {s : Finset V} (hz : s ∩ Hosts = ∅) :
    crossPart Core Hosts s = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro e he
  simp only [crossPart, Finset.mem_filter] at he
  rw [mem_crossEdges] at he
  obtain ⟨x, hx, w, hw, rfl⟩ := he.2
  rw [mem_pieceEdges_mk] at he
  have : w ∈ s ∩ Hosts := Finset.mem_inter.mpr ⟨he.1.2.1, hw⟩
  rw [hz] at this
  exact absurd this (Finset.notMem_empty w)

/-- **The local resource inequality.**  Every `K3`/`K4` piece of a complete split graph
carries at most twice as many cross resources as inner resources. -/
theorem card_crossPart_le (hd : Disjoint Core Hosts) {s : Finset V}
    (hclique : (splitGraph Core Hosts).IsClique (s : Set V)) (hcard : s.card = 3 ∨ s.card = 4) :
    (crossPart Core Hosts s).card ≤ 2 * (innerPart Core s).card := by
  have h3 : 3 ≤ s.card := by rcases hcard with h | h <;> omega
  by_cases hhost : s ∩ Hosts = ∅
  · rw [crossPart_eq_empty_of_no_host hhost]
    simp
  · -- the piece has exactly one host
    obtain ⟨z, hzmem⟩ : ∃ z, z ∈ s ∩ Hosts := Finset.nonempty_iff_ne_empty.mpr hhost
    have hone : s ∩ Hosts = {z} := by
      refine Finset.eq_singleton_iff_unique_mem.mpr ⟨hzmem, fun x hx => ?_⟩
      have := card_inter_hosts_le_one hd hclique
      rw [Finset.card_le_one] at this
      exact this x hx z hzmem
    -- the core part of the piece has at least two vertices
    have hsplit : (s ∩ Core).card + (s ∩ Hosts).card = s.card := by
      rw [← Finset.card_union_of_disjoint]
      · congr 1
        rw [← Finset.inter_union_distrib_left]
        exact Finset.inter_eq_left.mpr (subset_core_union_hosts hclique (by omega))
      · refine Finset.disjoint_left.mpr ?_
        intro a ha hb
        exact (Finset.disjoint_left.mp hd (Finset.mem_inter.mp ha).2) (Finset.mem_inter.mp hb).2
    have hcore : 2 ≤ (s ∩ Core).card := by
      rw [hone, Finset.card_singleton] at hsplit
      omega
    rw [card_crossPart_of_host hd hone, innerPart_eq, card_pieceEdges]
    obtain ⟨m, hm⟩ : ∃ m, (s ∩ Core).card = m + 2 := ⟨(s ∩ Core).card - 2, by omega⟩
    have hkey : (m + 2) * (m + 1) = 2 * (m + 2).choose 2 := by
      simpa using PaperIV.SplitUniformIncidence.mul_pred_eq_two_mul_choose_two (m + 2)
    rw [hm]
    nlinarith [hkey]

/-! ## The global obstruction -/

variable {P : Finset (Finset V)}

theorem filter_coveredEdges (p : Sym2 V → Prop) [DecidablePred p]
    (hP : IsPacking (splitGraph Core Hosts) P) :
    ((coveredEdges P).filter p).card = ∑ s ∈ P, ((pieceEdges s).filter p).card := by
  rw [coveredEdges, Finset.filter_biUnion]
  refine Finset.card_biUnion ?_
  intro s hs t ht hst
  exact Finset.disjoint_filter_filter (hP.edgeDisjoint s hs t ht hst)

/-- **The global resource inequality.**  In any `K3`/`K4` packing of a complete split
graph, at most twice as many cross edges are covered as inner edges. -/
theorem card_cross_covered_le (hd : Disjoint Core Hosts)
    (hP : IsK34Packing (splitGraph Core Hosts) P) :
    ((coveredEdges P).filter fun e => e ∈ crossEdges Core Hosts).card
      ≤ 2 * ((coveredEdges P).filter fun e => e ∈ pieceEdges Core).card := by
  rw [filter_coveredEdges _ hP.toIsPacking, filter_coveredEdges _ hP.toIsPacking,
    Finset.mul_sum]
  refine Finset.sum_le_sum ?_
  intro s hs
  exact card_crossPart_le hd (hP.pieces s hs).clique (hP.big s hs)

/-- **The obstruction.**  In any `K3`/`K4` packing of the complete split graph at least
`k*h - k*(k-1)` edges remain uncovered. -/
theorem card_uncovered_lower_bound (hd : Disjoint Core Hosts)
    (hP : IsK34Packing (splitGraph Core Hosts) P) :
    Core.card * Hosts.card ≤
      (graphEdges (splitGraph Core Hosts) \ coveredEdges P).card
        + Core.card * (Core.card - 1) := by
  classical
  -- the covered inner edges are at most all inner edges
  have hinner : ((coveredEdges P).filter fun e => e ∈ pieceEdges Core).card
      ≤ Core.card.choose 2 := by
    rw [← card_pieceEdges Core]
    refine Finset.card_le_card ?_
    intro e he
    exact (Finset.mem_filter.mp he).2
  have hcross := card_cross_covered_le hd hP
  -- the cross edges split into covered and uncovered ones
  have hsplit : (crossEdges Core Hosts \ coveredEdges P).card
      + ((coveredEdges P).filter fun e => e ∈ crossEdges Core Hosts).card
      = (crossEdges Core Hosts).card := by
    rw [← Finset.card_sdiff_add_card_inter (crossEdges Core Hosts) (coveredEdges P)]
    congr 1
    rw [Finset.inter_comm]
    rfl
  have hsub : crossEdges Core Hosts \ coveredEdges P ⊆
      graphEdges (splitGraph Core Hosts) \ coveredEdges P := by
    intro e he
    rw [Finset.mem_sdiff] at he ⊢
    exact ⟨crossEdges_subset_graphEdges hd he.1, he.2⟩
  have hmono := Finset.card_le_card hsub
  have hcard := card_crossEdges hd
  have hchoose := PaperIV.SplitUniformIncidence.mul_pred_eq_two_mul_choose_two Core.card
  omega

/-- **Failure of the universal target.**  As soon as there are at least as many hosts as
core vertices, every `K3`/`K4` packing leaves at least `k * (h - k + 1)` edges uncovered
— a residue that grows without linear bound in the number of hosts. -/
theorem card_uncovered_lower_bound_of_many_hosts (hd : Disjoint Core Hosts)
    (hP : IsK34Packing (splitGraph Core Hosts) P) (hh : Core.card ≤ Hosts.card) :
    Core.card * (Hosts.card - Core.card + 1) ≤
      (graphEdges (splitGraph Core Hosts) \ coveredEdges P).card := by
  have hmain := card_uncovered_lower_bound hd hP
  rcases Nat.eq_zero_or_pos Core.card with h0 | h0
  · simp [h0]
  · have hk : Core.card * (Hosts.card - Core.card + 1) + Core.card * (Core.card - 1)
        = Core.card * Hosts.card := by
      rw [← Nat.mul_add]
      congr 1
      omega
    omega

end PaperIV.SplitPackingObstruction
