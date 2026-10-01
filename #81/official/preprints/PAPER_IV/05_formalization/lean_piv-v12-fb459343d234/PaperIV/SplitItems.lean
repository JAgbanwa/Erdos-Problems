import PaperIV.FarRounding
import PaperIV.SplitUniformIncidence

/-!
# Selected split cliques are canonical mixed items

This is the support-side bridge for C3-A: each literal clique used by the
uniform split construction belongs to the finite item family of the canonical
mixed packing program.
-/

namespace PaperIV.SplitItems

open PaperIV.FarRounding
open PaperIV.SplitUniformIncidence

variable {V : Type*} [Fintype V] [DecidableEq V]

local instance (Core Hosts : Finset V) : DecidableRel (splitGraph Core Hosts).Adj := by
  intro x y
  unfold splitGraph
  infer_instance

theorem famK3_subset_items {Core Hosts : Finset V} (hd : Disjoint Core Hosts) :
    famK3 Core Hosts ⊆ items (splitGraph Core Hosts) := by
  intro K hK
  rw [mem_items]
  obtain ⟨hclique, hcard⟩ := famK3_isClique hd hK
  exact ⟨fun a ha b hb hab => hclique ha hb hab, Or.inl hcard⟩

theorem famK4_subset_items {Core Hosts : Finset V} (hd : Disjoint Core Hosts) :
    famK4 Core Hosts ⊆ items (splitGraph Core Hosts) := by
  intro K hK
  rw [mem_items]
  obtain ⟨hclique, hcard⟩ := famK4_isClique hd hK
  exact ⟨fun a ha b hb hab => hclique ha hb hab, Or.inr hcard⟩

theorem famK4core_subset_items (Core Hosts : Finset V) :
    famK4core Core ⊆ items (splitGraph Core Hosts) := by
  intro K hK
  rw [mem_items]
  obtain ⟨hclique, hcard⟩ := famK4core_isClique (Hosts := Hosts) hK
  exact ⟨fun a ha b hb hab => hclique ha hb hab, Or.inr hcard⟩

end PaperIV.SplitItems
