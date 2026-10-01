import PaperIV.DefectComparatorGraph
import PaperIV.RootedSimplicialDefect

/-!
# The comparator has rooted simplicial defect at most `s`

The comparator is genuinely inside the defect-`s` class.  Given a root clique `R`
inside a set `U`, an eliminable vertex is found as follows.

* If some host `z` lies in `U \ R`, take it: its neighbourhood inside `U` is
  contained in `Core ∪ Def`, its core part is a clique, and only the at most
  `s` defective vertices have to be discarded.
* Otherwise every host of `U` lies in the clique `R`, so `U` contains at most one
  host.  Then *any* vertex of `U \ R` is genuinely simplicial: the neighbourhood
  of a core vertex is a clique (core vertices plus the unique host), and the
  neighbourhood of a defective vertex has at most one element.
-/

namespace PaperIV.DefectComparatorRootedDefect

open Finset
open PaperIV.DefectComparatorGraph PaperIV.RootedSimplicialDefect

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
/-- Every neighbour of a host lies in `Core ∪ Def`. -/
theorem mem_coreDef_of_adj_host {Core Def Hosts : Finset V}
    (hd : Disjoint (Core ∪ Def) Hosts) {z x : V} (hz : z ∈ Hosts)
    (hadj : (defSplitGraph Core Def Hosts).Adj z x) : x ∈ Core ∪ Def := by
  obtain ⟨-, hcase⟩ := hadj
  rcases hcase with h | h | h
  · exact absurd hz (Finset.disjoint_left.mp hd (Finset.mem_union_left _ h.1))
  · exact absurd hz (Finset.disjoint_left.mp hd h.1)
  · exact h.2

omit [Fintype V] in
/-- Every neighbour of a core vertex is a core vertex or a host. -/
theorem mem_coreHosts_of_adj_core {Core Def Hosts : Finset V}
    (hCH : Disjoint Core Hosts) {v x : V} (hv : v ∈ Core)
    (hadj : (defSplitGraph Core Def Hosts).Adj v x) : x ∈ Core ∨ x ∈ Hosts := by
  obtain ⟨-, hcase⟩ := hadj
  rcases hcase with h | h | h
  · exact Or.inl h.2
  · exact Or.inr h.2
  · exact absurd h.1 (Finset.disjoint_left.mp hCH hv)

omit [Fintype V] in
/-- **The comparator has rooted simplicial defect at most `#Def`.** -/
theorem rootedDefectAt_defSplitGraph {Core Def Hosts : Finset V}
    (hCD : Disjoint Core Def) (hDH : Disjoint Def Hosts) (hCH : Disjoint Core Hosts)
    (hcover : ∀ x : V, x ∈ Core ∨ x ∈ Def ∨ x ∈ Hosts)
    {s : ℕ} (hs : Def.card ≤ s) :
    RootedDefectAt (defSplitGraph Core Def Hosts) s := by
  have hd : Disjoint (Core ∪ Def) Hosts := Finset.disjoint_union_left.mpr ⟨hCH, hDH⟩
  intro U R hRU hR hne
  by_cases hhost : ∃ z ∈ U \ R, z ∈ Hosts
  · -- a host outside the root: discard the defective neighbours
    obtain ⟨z, hzU, hzH⟩ := hhost
    refine ⟨z, hzU, (neighborsIn (defSplitGraph Core Def Hosts) U z).filter (fun w => w ∈ Core),
      Finset.filter_subset _ _, ?_, ?_⟩
    · intro a ha b hb hab
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at ha hb
      exact defSplitGraph_adj_inner ha.2 hb.2 hab
    · have hsplit := Finset.card_filter_add_card_filter_not
        (s := neighborsIn (defSplitGraph Core Def Hosts) U z) (p := fun w => w ∈ Core)
      have hsub : ((neighborsIn (defSplitGraph Core Def Hosts) U z).filter
          (fun w => ¬ w ∈ Core)) ⊆ Def := by
        intro w hw
        rw [Finset.mem_filter] at hw
        have hadj : (defSplitGraph Core Def Hosts).Adj z w :=
          (Finset.mem_filter.mp hw.1).2
        rcases Finset.mem_union.mp (mem_coreDef_of_adj_host hd hzH hadj) with h | h
        · exact absurd h hw.2
        · exact h
      have hle : ((neighborsIn (defSplitGraph Core Def Hosts) U z).filter
          (fun w => ¬ w ∈ Core)).card ≤ Def.card := Finset.card_le_card hsub
      omega
  · -- no host outside the root: `U` contains at most one host
    push_neg at hhost
    have hUhost : ∀ z ∈ U, z ∈ Hosts → z ∈ R := by
      intro z hzU hzH
      by_contra hzR
      exact hhost z (Finset.mem_sdiff.mpr ⟨hzU, hzR⟩) hzH
    have hone : ∀ a ∈ U, ∀ b ∈ U, a ∈ Hosts → b ∈ Hosts → a = b := by
      intro a haU b hbU haH hbH
      by_contra hab
      exact not_adj_of_mem_hosts hd haH hbH
        (hR (by simpa using hUhost a haU haH) (by simpa using hUhost b hbU hbH) hab)
    obtain ⟨v, hv⟩ := hne
    have hvU : v ∈ U := (Finset.mem_sdiff.mp hv).1
    refine ⟨v, hv, neighborsIn (defSplitGraph Core Def Hosts) U v, Finset.Subset.rfl, ?_,
      by omega⟩
    intro a ha b hb hab
    simp only [Finset.mem_coe, neighborsIn, Finset.mem_filter] at ha hb
    obtain ⟨haU, hadja⟩ := ha
    obtain ⟨hbU, hadjb⟩ := hb
    rcases hcover v with hvC | hvD | hvH
    · -- core vertex: the neighbourhood is core vertices plus at most one host
      rcases mem_coreHosts_of_adj_core hCH hvC hadja with haC | haH
      · rcases mem_coreHosts_of_adj_core hCH hvC hadjb with hbC | hbH
        · exact defSplitGraph_adj_inner haC hbC hab
        · exact defSplitGraph_adj_cross hd (Finset.mem_union_left _ haC) hbH
      · rcases mem_coreHosts_of_adj_core hCH hvC hadjb with hbC | hbH
        · exact (defSplitGraph_adj_cross hd (Finset.mem_union_left _ hbC) haH).symm
        · exact absurd (hone a haU b hbU haH hbH) hab
    · -- defective vertex: the neighbourhood consists of hosts, hence of one vertex
      have haH : a ∈ Hosts := mem_hosts_of_adj_def hCD hDH hvD hadja
      have hbH : b ∈ Hosts := mem_hosts_of_adj_def hCD hDH hvD hadjb
      exact absurd (hone a haU b hbU haH hbH) hab
    · exact absurd (hUhost v hvU hvH) (Finset.mem_sdiff.mp hv).2

end PaperIV.DefectComparatorRootedDefect
