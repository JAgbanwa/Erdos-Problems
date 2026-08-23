/-
# Nibble — `ν₃*` splits over a cover of the triangles by spanning subgraphs

Every route that lifts the coupled block-allocation residual from near-uniform to general cluster
densities has to *split* the fractional optimum: band the cluster densities, and account for the
triangles of the regularity-reduced graph one band pattern at a time.  The step that makes such a
split legitimate is the sub-additivity of `ν₃*` over a family of spanning subgraphs that between
them contain every triangle:

* `Nibble.AX1.nu3star_le_sum_of_subgraph_cover` — if every triangle of `G` is a triangle of one of
  `H 0, …, H (k-1) ≤ G`, then `ν₃*(G) ≤ ∑ i < k, ν₃*(H i)`.

The proof is the obvious one: a fractional packing of `G` is cut into `k` pieces along the index of
a subgraph containing the triangle, and each piece is a fractional packing of that subgraph,
because its edge loads are only smaller.

Note that the family is *not* required to be disjoint or to consist of induced subgraphs; the
bound is one-sided, which is the direction the residual needs.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.CoreGapAX1

open Finset SimpleGraph Nibble.YusterE

namespace Nibble.AX1

variable {V : Type} [Fintype V] [DecidableEq V]

/-- **`ν₃*` is sub-additive over a cover of the triangles by spanning subgraphs.**  If each `H i`,
`i < k`, is a subgraph of `G` and every triangle of `G` is a triangle of some `H i`, then the
fractional triangle-packing number of `G` is at most the sum of those of the `H i`. -/
theorem nu3star_le_sum_of_subgraph_cover (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ}
    (H : ℕ → SimpleGraph V) [∀ i, DecidableRel (H i).Adj]
    (hsub : ∀ i < k, H i ≤ G)
    (hcov : ∀ t ∈ G.cliqueFinset 3, ∃ i < k, t ∈ (H i).cliqueFinset 3) :
    nu3star G ≤ ∑ i ∈ Finset.range k, nu3star (H i) := by
  classical
  -- the hypergraph of each piece sits inside that of `G`
  have hmono : ∀ i < k, triangleHypergraphE (H i) ⊆ triangleHypergraphE G := fun i hi =>
    triangleHypergraphE_mono G (H i) (hsub i hi)
  -- every hyperedge of `G` is a hyperedge of some piece
  have hex : ∀ T ∈ triangleHypergraphE G, ∃ i, i < k ∧ T ∈ triangleHypergraphE (H i) := by
    intro T hT
    rw [triangleHypergraphE, Finset.mem_image] at hT
    obtain ⟨t, ht, rfl⟩ := hT
    obtain ⟨i, hi, hti⟩ := hcov t ht
    exact ⟨i, hi, Finset.mem_image_of_mem _ hti⟩
  obtain ⟨idx, hidx⟩ : ∃ idx : Finset (Finset V) → ℕ, ∀ T ∈ triangleHypergraphE G,
      idx T < k ∧ T ∈ triangleHypergraphE (H (idx T)) := by
    refine ⟨fun T => if h : ∃ i, i < k ∧ T ∈ triangleHypergraphE (H i) then h.choose else 0, ?_⟩
    intro T hT
    have h : ∃ i, i < k ∧ T ∈ triangleHypergraphE (H i) := hex T hT
    simp only [dif_pos h]
    exact h.choose_spec
  refine csSup_le ⟨0, ⟨fun _ => 0, ⟨fun _ => le_rfl, fun _ _ => rfl, fun e => by simp⟩, by simp⟩⟩ ?_
  rintro x ⟨w, hw, rfl⟩
  -- the piece of the packing that lives on the `i`-th subgraph
  set wp : ℕ → Finset (Finset V) → ℝ := fun i T =>
    if T ∈ triangleHypergraphE G ∧ idx T = i then w T else 0 with hwpdef
  have hwp0 : ∀ i T, 0 ≤ wp i T := by
    intro i T
    simp only [hwpdef]
    split_ifs with h
    · exact hw.1 T
    · exact le_rfl
  have hwple : ∀ i T, wp i T ≤ w T := by
    intro i T
    simp only [hwpdef]
    split_ifs with h
    · exact le_rfl
    · exact hw.1 T
  -- each piece is a fractional packing of its subgraph
  have hpack : ∀ i < k, IsFracPacking (H i) (wp i) := by
    intro i hi
    refine ⟨hwp0 i, ?_, ?_⟩
    · intro T hT
      simp only [hwpdef]
      split_ifs with h
      · exact absurd (h.2 ▸ (hidx T h.1).2) hT
      · rfl
    · intro e
      have hsubset : (triangleHypergraphE (H i)).filter (fun T => e ∈ T)
          ⊆ (triangleHypergraphE G).filter (fun T => e ∈ T) := by
        intro T hT
        rw [Finset.mem_filter] at hT ⊢
        exact ⟨hmono i hi hT.1, hT.2⟩
      calc ∑ T ∈ (triangleHypergraphE (H i)).filter (fun T => e ∈ T), wp i T
          ≤ ∑ T ∈ (triangleHypergraphE (H i)).filter (fun T => e ∈ T), w T :=
            Finset.sum_le_sum fun T _ => hwple i T
        _ ≤ ∑ T ∈ (triangleHypergraphE G).filter (fun T => e ∈ T), w T :=
            Finset.sum_le_sum_of_subset_of_nonneg hsubset fun T _ _ => hw.1 T
        _ ≤ 1 := hw.2.2 e
  -- the value of the piece is at most `ν₃*` of its subgraph
  have hvalue : ∀ i < k, ∑ T ∈ triangleHypergraphE (H i), wp i T ≤ nu3star (H i) := by
    intro i hi
    exact le_csSup (nu3star_bddAbove (H i)) ⟨wp i, hpack i hi, rfl⟩
  -- the pieces of a hyperedge of `G` add up to its weight
  have hsplit : ∀ T ∈ triangleHypergraphE G, ∑ i ∈ Finset.range k, wp i T = w T := by
    intro T hT
    have hik : idx T ∈ Finset.range k := Finset.mem_range.mpr (hidx T hT).1
    rw [Finset.sum_eq_single (idx T)]
    · simp [hwpdef, hT]
    · intro i _ hne
      simp [hwpdef, hT, Ne.symm hne]
    · intro h; exact absurd hik h
  -- the value of a piece may be summed over the hypergraph of `G`
  have hover : ∀ i < k, ∑ T ∈ triangleHypergraphE G, wp i T
      = ∑ T ∈ triangleHypergraphE (H i), wp i T := by
    intro i hi
    refine (Finset.sum_subset (hmono i hi) ?_).symm
    intro T hT hTn
    simp only [hwpdef]
    split_ifs with h
    · exact absurd (h.2 ▸ (hidx T h.1).2) hTn
    · rfl
  calc ∑ T ∈ triangleHypergraphE G, w T
      = ∑ T ∈ triangleHypergraphE G, ∑ i ∈ Finset.range k, wp i T :=
        (Finset.sum_congr rfl fun T hT => (hsplit T hT).symm)
    _ = ∑ i ∈ Finset.range k, ∑ T ∈ triangleHypergraphE G, wp i T := Finset.sum_comm
    _ = ∑ i ∈ Finset.range k, ∑ T ∈ triangleHypergraphE (H i), wp i T :=
        Finset.sum_congr rfl fun i hi => hover i (Finset.mem_range.mp hi)
    _ ≤ ∑ i ∈ Finset.range k, nu3star (H i) :=
        Finset.sum_le_sum fun i hi => hvalue i (Finset.mem_range.mp hi)

/-! ### Axiom check -/

section AxCheck

#print axioms Nibble.AX1.nu3star_le_sum_of_subgraph_cover

end AxCheck

end Nibble.AX1
