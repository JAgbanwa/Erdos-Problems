/-
# Nibble — Ch2b core : dependency locality of edge survival (deterministic)

Standalone, Mathlib-only. The combinatorial heart of the Chebyshev independence step: an edge `e`
survives (avoids the covered set) depending only on which edges *in its dependency neighbourhood*
`depNbhd H e` are retained. This "read-k" structure is what makes the survival indicators of
far-apart edges independent (⇒ zero covariance, Ch2).

`depNbhd H e` = the edges of `H` that meet `e`, together with all their conflicts. If two retained
sets agree on `depNbhd H e`, then `e` has the same survival status under both.

Deterministic; holds for any `R, R' ⊆ H`. Sorry-free, axiom-clean.
-/
import Nibble.Basic
import Nibble.Round
import Nibble.Conflict

open Finset

namespace Hypergraph

variable {V : Type*} [DecidableEq V]

/-- The dependency neighbourhood of `e`: edges of `H` meeting `e`, plus all of their conflicts. -/
def depNbhd (H : Finset (Finset V)) (e : Finset V) : Finset (Finset V) :=
  (H.filter (fun f => ¬ Disjoint e f)).biUnion (fun f => insert f (conflicts H f))

/-- `e` avoids the covered set iff no edge of the round's matching meets `e`. -/
theorem disjoint_covered_iff (R : Finset (Finset V)) (e : Finset V) :
    Disjoint e (covered R) ↔ ∀ f ∈ roundMatching R, Disjoint e f := by
  rw [covered, support, Finset.disjoint_biUnion_right]
  simp

/-- If a matched edge `f` meets `e`, then `f` and all its conflicts lie in `depNbhd H e`. -/
theorem mem_depNbhd_of_touch {H : Finset (Finset V)} {e f : Finset V}
    (hfH : f ∈ H) (htouch : ¬ Disjoint e f) : f ∈ depNbhd H e :=
  Finset.mem_biUnion.mpr ⟨f, Finset.mem_filter.mpr ⟨hfH, htouch⟩, Finset.mem_insert_self _ _⟩

theorem conflict_mem_depNbhd {H : Finset (Finset V)} {e f g : Finset V}
    (hfH : f ∈ H) (htouch : ¬ Disjoint e f) (hg : g ∈ conflicts H f) : g ∈ depNbhd H e :=
  Finset.mem_biUnion.mpr ⟨f, Finset.mem_filter.mpr ⟨hfH, htouch⟩, Finset.mem_insert_of_mem hg⟩

/-- **Ch2b-core — survival is local.** If `R, R' ⊆ H` agree on `depNbhd H e`, then `e` avoids the
covered set under `R` iff it does under `R'`. -/
theorem survival_local {H : Finset (Finset V)} {e : Finset V} {R R' : Finset (Finset V)}
    (hRH : R ⊆ H) (hR'H : R' ⊆ H)
    (hag : ∀ g ∈ depNbhd H e, (g ∈ R ↔ g ∈ R')) :
    Disjoint e (covered R) ↔ Disjoint e (covered R') := by
  -- It suffices to transfer matched-edges-meeting-`e` between R and R'; symmetric, so prove one way.
  have key : ∀ {S S' : Finset (Finset V)}, S ⊆ H → S' ⊆ H →
      (∀ g ∈ depNbhd H e, (g ∈ S ↔ g ∈ S')) →
      (∀ f ∈ roundMatching S, Disjoint e f) → (∀ f ∈ roundMatching S', Disjoint e f) := by
    intro S S' hSH hS'H hagree hS f hf
    by_contra hnd
    -- f ∈ roundMatching S', ¬Disjoint e f  ⟹  show f ∈ roundMatching S, then use hS
    rw [roundMatching, Finset.mem_filter] at hf
    obtain ⟨hfS', hiso'⟩ := hf
    have hfH : f ∈ H := hS'H hfS'
    have hfdep : f ∈ depNbhd H e := mem_depNbhd_of_touch hfH hnd
    have hfS : f ∈ S := (hagree f hfdep).mpr hfS'
    have hfmatchS : f ∈ roundMatching S := by
      rw [roundMatching, Finset.mem_filter]
      refine ⟨hfS, ?_⟩
      intro g hgS hgf
      by_contra hgnd
      -- g ∈ S, g ≠ f, ¬Disjoint f g ⟹ g ∈ conflicts H f ⊆ depNbhd ⟹ g ∈ S' ⟹ contradiction with hiso'
      have hgH : g ∈ H := hSH hgS
      have hgconf : g ∈ conflicts H f := by
        rw [conflicts, Finset.mem_filter]
        exact ⟨hgH, hgf, Finset.not_disjoint_iff_nonempty_inter.mp hgnd⟩
      have hgdep : g ∈ depNbhd H e := conflict_mem_depNbhd hfH hnd hgconf
      have hgS' : g ∈ S' := (hagree g hgdep).mp hgS
      exact hgnd (hiso' g hgS' hgf)
    exact hnd (hS f hfmatchS)
  rw [disjoint_covered_iff, disjoint_covered_iff]
  exact ⟨key hRH hR'H hag, key hR'H hRH fun g hg => (hag g hg).symm⟩

end Hypergraph
