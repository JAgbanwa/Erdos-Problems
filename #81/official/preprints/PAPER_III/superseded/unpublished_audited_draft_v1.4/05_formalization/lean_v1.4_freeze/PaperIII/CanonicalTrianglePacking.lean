/-
# Paper III — canonical triangle-packing interface

The manuscript-facing quantities are `PaperIII.nu3` and `PaperIII.nu3Star`.
The nibble development uses an edge-hypergraph representation with its own
`Nibble.YusterE.nu3` and `Nibble.YusterE.nu3star`.  This module proves the
identifications once and exposes AX1 in the packing-side form stated in the
manuscript.  The Nibble definitions remain implementation details.
-/
import PaperIII.AXDefs
import Nibble.StrongDualityInst
import Nibble.YusterBridgePacking
import Nibble.YusterBridgeFrac

namespace PaperIII

open Finset SimpleGraph

variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

omit [Fintype V] [DecidableRel G.Adj] in
/-- The manuscript and edge-hypergraph predicates for integral triangle packings
are definitionally identical. -/
theorem isTrianglePacking_iff_yuster (T : Finset (Finset V)) :
    PaperIII.IsTrianglePacking G T ↔ Nibble.YusterE.IsTrianglePacking G T :=
  Iff.rfl

/-- The manuscript integral packing number equals the maximum matching number of
the edge-based triangle hypergraph. -/
theorem nu3_eq_yuster :
    PaperIII.nu3 G = Nibble.YusterE.nu3 G := by
  rw [PaperIII.nu3]
  exact (Nibble.YusterE.nu3_eq_trianglePacking_sSup G).symm

/-- The manuscript vertex-set and nibble triangle-edge-set presentations induce
the same fractional feasible region after the canonical triangle reindexing. -/
theorem isFracPacking_iff_yuster (w : Finset V → ℝ) :
    PaperIII.IsFracPacking G w ↔ Nibble.YusterE.IsTriangleFracPacking G w := by
  constructor
  · rintro ⟨hnn, hsupp, hcap⟩
    refine ⟨hnn, hsupp, ?_⟩
    intro e he
    let isEdge : Finset V → Prop :=
      fun f => ∃ e' ∈ G.edgeFinset, Sym2.toFinset e' = f
    by_cases hedge : isEdge e
    · obtain ⟨e', he'G, he'e⟩ := hedge
      have hc := hcap e' he'G
      have hfilter :
          (G.cliqueFinset 3).filter (fun t => e ⊆ t) =
            (G.cliqueFinset 3).filter (fun t => ∀ v ∈ e', v ∈ t) := by
        ext t
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨ht, hsub⟩
          refine ⟨ht, ?_⟩
          intro v hv
          apply hsub
          rw [← he'e]
          exact Sym2.mem_toFinset.mpr hv
        · rintro ⟨ht, hall⟩
          refine ⟨ht, ?_⟩
          intro v hv
          rw [← he'e] at hv
          exact hall v (Sym2.mem_toFinset.mp hv)
      rw [hfilter]
      exact hc
    · have hempty :
          (G.cliqueFinset 3).filter (fun t => e ⊆ t) = ∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        intro t ht hsub
        rw [SimpleGraph.mem_cliqueFinset_iff] at ht
        obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp he
        apply hedge
        refine ⟨s(a, b), ?_, ?_⟩
        · rw [SimpleGraph.mem_edgeFinset]
          exact ht.isClique (hsub (by simp)) (hsub (by simp)) hab
        · ext v
          simp [Sym2.mem_toFinset]
      simp [hempty]
  · rintro ⟨hnn, hsupp, hcap⟩
    refine ⟨hnn, hsupp, ?_⟩
    intro e he
    have heCard : e.toFinset.card = 2 := by
      rcases e with ⟨a, b⟩
      simp [SimpleGraph.mem_edgeFinset, Sym2.toFinset, Sym2.toMultiset] at he ⊢
      simpa using Finset.card_pair he.ne
    have hc := hcap e.toFinset heCard
    have hfilter :
        (G.cliqueFinset 3).filter (fun t => ∀ v ∈ e, v ∈ t) =
          (G.cliqueFinset 3).filter (fun t => e.toFinset ⊆ t) := by
      ext t
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨ht, hall⟩
        refine ⟨ht, ?_⟩
        intro v hv
        exact hall v (Sym2.mem_toFinset.mp hv)
      · rintro ⟨ht, hsub⟩
        refine ⟨ht, ?_⟩
        intro v hv
        exact hsub (Sym2.mem_toFinset.mpr hv)
    rw [hfilter]
    exact hc

/-- The fractional optimum in the manuscript equals the fractional optimum of
the edge-based triangle hypergraph. -/
theorem nu3Star_eq_yuster :
    PaperIII.nu3Star G = Nibble.YusterE.nu3star G := by
  rw [Nibble.YusterE.nu3star_eq_triangleFrac_sSup]
  unfold PaperIII.nu3Star
  congr 1
  ext x
  constructor
  · rintro ⟨w, hw, hx⟩
    exact ⟨w, (isFracPacking_iff_yuster G w).mp hw, hx⟩
  · rintro ⟨w, hw, hx⟩
    exact ⟨w, (isFracPacking_iff_yuster G w).mpr hw, hx⟩

/-- The two cover-side definitions used by Paper III and the AX1 implementation
are definitionally identical. -/
theorem tau3Star_eq_yuster_cover :
    PaperIII.tau3Star G = Nibble.AX1.tau3Star G :=
  rfl

/-- Finite LP strong duality in the manuscript-facing namespace. -/
theorem tau3Star_eq_nu3Star :
    PaperIII.tau3Star G = PaperIII.nu3Star G := by
  apply le_antisymm
  · calc
      PaperIII.tau3Star G = Nibble.AX1.tau3Star G := tau3Star_eq_yuster_cover G
      _ ≤ Nibble.YusterE.nu3star G := Nibble.AX1.tau3Star_le_nu3star G
      _ = PaperIII.nu3Star G := (nu3Star_eq_yuster G).symm
  · exact PaperIII.nu3Star_le_tau3Star G

/-- Packing-side AX1 statement, using exactly the quantities appearing in the
manuscript. -/
abbrev AX1PackingStatement : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ,
    ∀ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
      (H : SimpleGraph V) (_ : DecidableRel H.Adj),
      n₀ ≤ Fintype.card V →
      nu3Star H - (nu3 H : ℝ) ≤ ε * (Fintype.card V : ℝ) ^ 2

/-- The cover-side assembly interface and the manuscript packing-side AX1
statement are equivalent. -/
theorem AX1Assumption_iff_packing_form :
    PaperIII.AX1Assumption ↔ PaperIII.AX1PackingStatement := by
  constructor
  · intro h ε hε
    obtain ⟨n₀, hn₀⟩ := h ε hε
    refine ⟨n₀, ?_⟩
    intro W fW dW H dH hn
    letI : Fintype W := fW
    letI : DecidableEq W := dW
    letI : DecidableRel H.Adj := dH
    have hh := hn₀ W fW dW H dH hn
    rw [tau3Star_eq_nu3Star H] at hh
    exact hh
  · intro h ε hε
    obtain ⟨n₀, hn₀⟩ := h ε hε
    refine ⟨n₀, ?_⟩
    intro W fW dW H dH hn
    letI : Fintype W := fW
    letI : DecidableEq W := dW
    letI : DecidableRel H.Adj := dH
    have hh := hn₀ W fW dW H dH hn
    rw [tau3Star_eq_nu3Star H]
    exact hh

end PaperIII
