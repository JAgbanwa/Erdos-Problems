import PaperIV.RootedEliminationOrder

/-!
An exact finite formulation of rooted simplicial defect.  The parameter `s`
is a bound on the number of neighbours that must be discarded to leave a
clique, in every induced subgraph and outside every prescribed proper clique.
No result about the sharp `Q_s(n)` partition bound is assumed here.
-/

namespace PaperIV.RootedSimplicialDefect

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def neighborsIn (U : Finset V) (v : V) : Finset V :=
  U.filter (fun w => G.Adj v w)

def DefectSimplicialOn (U : Finset V) (s : ℕ) (v : V) : Prop :=
  ∃ C : Finset V, C ⊆ neighborsIn G U v ∧ G.IsClique (C : Set V) ∧
    (neighborsIn G U v).card ≤ C.card + s

/-- Rooted defect at most `s`: the root is allowed to be empty. -/
def RootedDefectAt (s : ℕ) : Prop :=
  ∀ U R : Finset V, R ⊆ U → G.IsClique (R : Set V) →
    (U \ R).Nonempty → ∃ v ∈ U \ R, DefectSimplicialOn G U s v

theorem rootedDefectAt_mono {s t : ℕ} (hst : s ≤ t)
    (h : RootedDefectAt G s) : RootedDefectAt G t := by
  intro U R hRU hR hne
  obtain ⟨v, hv, C, hCsub, hCclique, hcard⟩ := h U R hRU hR hne
  exact ⟨v, hv, C, hCsub, hCclique, by omega⟩

/-- The parameter is finite for every finite graph; this bound is intentionally
coarse and is not the fixed-defect theorem. -/
theorem rootedDefectAt_card : RootedDefectAt G (Fintype.card V) := by
  intro U R _ _ hne
  obtain ⟨v, hv⟩ := hne
  refine ⟨v, hv, ∅, Finset.empty_subset _, by simp, ?_⟩
  have hcard := Finset.card_le_card (Finset.subset_univ (neighborsIn G U v))
  simpa using hcard

/-- Literal local edit budget: after retaining a clique in the current
neighbourhood, at most `s` incident edges point to exceptional neighbours.
This is one elimination step, not a global `Q_s(n)` partition theorem. -/
theorem exists_root_step_with_exceptional_budget {s : ℕ}
    (h : RootedDefectAt G s) {U R : Finset V}
    (hRU : R ⊆ U) (hR : G.IsClique (R : Set V))
    (hne : (U \ R).Nonempty) :
    ∃ v ∈ U \ R, ∃ C : Finset V,
      C ⊆ neighborsIn G U v ∧ G.IsClique (C : Set V) ∧
        (neighborsIn G U v \ C).card ≤ s := by
  obtain ⟨v, hv, C, hCsub, hCclique, hcard⟩ := h U R hRU hR hne
  refine ⟨v, hv, C, hCsub, hCclique, ?_⟩
  rw [Finset.card_sdiff_of_subset hCsub]
  omega

/-- All finite chordal graphs satisfy the rooted condition with defect zero. -/
theorem chordal_rootedDefect_zero (hG : PaperIV.IsChordal G) :
    RootedDefectAt G 0 := by
  intro U R hRU hR hne
  let H : SimpleGraph (U : Set V) := G.induce (U : Set V)
  let R' : Set (U : Set V) := {x | x.val ∈ R}
  have hR' : H.IsClique R' := by
    intro a ha b hb hab
    exact hR ha hb (fun h => hab (Subtype.ext h))
  have hout : ∃ x : (U : Set V), x ∉ R' := by
    obtain ⟨v, hv⟩ := hne
    exact ⟨⟨v, (Finset.mem_sdiff.mp hv).1⟩, (Finset.mem_sdiff.mp hv).2⟩
  obtain ⟨x, hxR, hxSimp⟩ :=
    PaperIV.RootedEliminationOrder.exists_simplicial_outside_clique
      (G := H) (hG.induce (U : Set V)) hR' hout
  let v : V := x.val
  have hv : v ∈ U \ R :=
    Finset.mem_sdiff.mpr ⟨x.property, hxR⟩
  have hc : G.IsClique {w | w ∈ (U : Set V) ∧ G.Adj v w} :=
    PaperIV.RootedEliminationOrder.clique_of_simplicial_induce x.property hxSimp
  refine ⟨v, hv, neighborsIn G U v, Finset.Subset.rfl, ?_, by omega⟩
  intro a ha b hb hab
  exact hc (Finset.mem_filter.mp ha) (Finset.mem_filter.mp hb) hab

end PaperIV.RootedSimplicialDefect

