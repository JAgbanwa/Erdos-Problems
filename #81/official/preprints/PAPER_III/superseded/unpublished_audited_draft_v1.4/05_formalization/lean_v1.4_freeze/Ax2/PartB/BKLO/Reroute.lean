/-
  Part B (Phase 2) — the rerouting move of the absorption method.

  A **transformer bank** indexed by `I`: for each `i`, a base triangle decomposition `B i`
  and an absorbing decomposition `Ab i` covering `B i`'s edges plus a config `S i`
  (`coveredEdges (Ab i) = coveredEdges (B i) ∪ S i`), all pairwise edge-disjoint.

  KEY INSIGHT (the rerouting move): to absorb any sub-collection `J ⊆ I` of configs, use the
  absorbing decomposition on `J` and the base one elsewhere:
      `P = (⋃_{i∈J} Ab i) ∪ (⋃_{i∈I∖J} B i)`.
  Then `P` is an edge-disjoint triangle family covering exactly
  `(⋃_{i∈I} coveredEdges (B i)) ∪ (⋃_{i∈J} S i)` — the absorber edges plus the chosen leftover.

  This is the combinatorial heart of the transformer; it reduces `build_absorber` to the
  EXISTENCE of such a bank (a transformer per possible leftover config, disjointly reserved),
  which is the remaining research kernel.
-/
import Ax2.PartB.BKLO.Defs

namespace Ax2.BKLO

open Finset Ax2

variable {V : Type*} [DecidableEq V] {ι : Type*} [DecidableEq ι]

/-- **The rerouting move.** A transformer bank absorbs any sub-collection `J` of its configs:
using absorbing decompositions on `J` and base decompositions off `J` yields an edge-disjoint
triangle family covering the absorber edges together with exactly the chosen configs. -/
theorem reroute (I J : Finset ι) (hJI : J ⊆ I)
    (B Ab : ι → Finset (Finset V)) (S : ι → Finset (Sym2 V))
    (hAbcov : ∀ i ∈ I, coveredEdges (Ab i) = coveredEdges (B i) ∪ S i)
    (hBd : ∀ i ∈ I, EdgeDisjoint (B i)) (hAbd : ∀ i ∈ I, EdgeDisjoint (Ab i))
    (hcross : ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
      Disjoint (coveredEdges (B i) ∪ S i) (coveredEdges (B j) ∪ S j)) :
    ∃ P : Finset (Finset V),
      P ⊆ (I \ J).biUnion (fun i => B i) ∪ J.biUnion (fun i => Ab i) ∧ EdgeDisjoint P ∧
      coveredEdges P = (I.biUnion (fun i => coveredEdges (B i))) ∪ (J.biUnion S) := by
  -- Define P: for i in I \ J use B i, for i in J use Ab i
  let P := (I \ J).biUnion (fun i => B i) ∪ J.biUnion (fun i => Ab i)
  use P
  refine ⟨Finset.Subset.refl _, ?_, ?_⟩
  · -- EdgeDisjoint P
    intro t₁ ht₁ t₂ ht₂ hne
    simp only [P] at ht₁ ht₂
    rw [Finset.mem_union] at ht₁ ht₂
    cases ht₁ with
    | inl ht₁B =>
      -- t₁ ∈ (I \ J).biUnion B
      obtain ⟨i, hiIJ, ht₁Bi⟩ := Finset.mem_biUnion.mp ht₁B
      rw [Finset.mem_sdiff] at hiIJ
      cases ht₂ with
      | inl ht₂B =>
        -- t₂ ∈ (I \ J).biUnion B
        obtain ⟨j, hjIJ, ht₂Bj⟩ := Finset.mem_biUnion.mp ht₂B
        rw [Finset.mem_sdiff] at hjIJ
        -- Both in B, use hBd or hcross
        by_cases hij : i = j
        · -- i = j, use hBd
          subst hij
          exact (hBd i hiIJ.1) t₁ ht₁Bi t₂ ht₂Bj hne
        · -- i ≠ j, use hcross
          have hcross' := hcross i hiIJ.1 j hjIJ.1 hij
          simp only [coveredEdges] at hcross'
          apply Finset.disjoint_of_subset_left _ (Finset.disjoint_of_subset_right _ hcross')
          · intro e he
            simp only [mem_union]
            left
            exact Finset.mem_biUnion.mpr ⟨t₁, ht₁Bi, he⟩
          · intro e he
            simp only [mem_union]
            left
            exact Finset.mem_biUnion.mpr ⟨t₂, ht₂Bj, he⟩
      | inr ht₂Ab =>
        -- t₂ ∈ J.biUnion Ab
        obtain ⟨j, hjJ, ht₂Abj⟩ := Finset.mem_biUnion.mp ht₂Ab
        -- t₁ ∈ B i (i ∈ I \ J), t₂ ∈ Ab j (j ∈ J)
        -- Use hcross: triEdges t₁ ⊆ coveredEdges (B i), triEdges t₂ ⊆ coveredEdges (Ab j) = coveredEdges (B j) ∪ S j
        -- i ∈ I, j ∈ J ⊆ I, and i ≠ j (since i ∉ J but j ∈ J)
        have hij : i ≠ j := fun h => hiIJ.2 (h ▸ hjJ)
        have hcross' := hcross i hiIJ.1 j (hJI hjJ) hij
        simp only [coveredEdges] at hcross'
        apply Finset.disjoint_of_subset_left _ (Finset.disjoint_of_subset_right _ hcross')
        · intro e he
          simp only [mem_union]
          left
          exact Finset.mem_biUnion.mpr ⟨t₁, ht₁Bi, he⟩
        · -- triEdges t₂ ⊆ coveredEdges (B j) ∪ S j
          have hcov := hAbcov j (hJI hjJ)
          simp only [coveredEdges] at hcov
          intro e he
          have he' : e ∈ (Ab j).biUnion triEdges := Finset.mem_biUnion.mpr ⟨t₂, ht₂Abj, he⟩
          rw [hcov] at he'
          exact he'
    | inr ht₁Ab =>
      -- t₁ ∈ J.biUnion Ab
      cases ht₂ with
      | inl ht₂B =>
        -- t₂ ∈ (I \ J).biUnion B
        obtain ⟨i, hiJ, ht₁Ab_i⟩ := Finset.mem_biUnion.mp ht₁Ab
        obtain ⟨j, hjIJ, ht₂Bj⟩ := Finset.mem_biUnion.mp ht₂B
        rw [Finset.mem_sdiff] at hjIJ
        -- t₁ ∈ Ab i (i ∈ J), t₂ ∈ B j (j ∈ I \ J)
        -- Use hcross: triEdges t₁ ⊆ coveredEdges (Ab i) = coveredEdges (B i) ∪ S i, triEdges t₂ ⊆ coveredEdges (B j)
        -- i ∈ J ⊆ I, j ∈ I, and i ≠ j (since i ∈ J but j ∉ J)
        have hij : i ≠ j := fun h => hjIJ.2 (h ▸ hiJ)
        have hcross' := hcross j hjIJ.1 i (hJI hiJ) hij.symm
        simp only [coveredEdges] at hcross'
        -- hcross' : Disjoint ((B j).biUnion triEdges ∪ S j) ((B i).biUnion triEdges ∪ S i)
        -- triEdges t₁ ⊆ (B i).biUnion triEdges ∪ S i
        -- triEdges t₂ ⊆ (B j).biUnion triEdges ∪ S j
        have hT1 : triEdges t₁ ⊆ (B i).biUnion triEdges ∪ S i := by
          have hcov := hAbcov i (hJI hiJ)
          simp only [coveredEdges] at hcov
          exact Finset.subset_iff.mpr (fun e he => by rw [← hcov]; exact Finset.mem_biUnion.mpr ⟨t₁, ht₁Ab_i, he⟩)
        have hT2 : triEdges t₂ ⊆ (B j).biUnion triEdges ∪ S j := by
          exact Finset.subset_iff.mpr (fun e he => Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨t₂, ht₂Bj, he⟩))
        exact (Finset.disjoint_of_subset_left hT2 (Finset.disjoint_of_subset_right hT1 hcross')).symm
      | inr ht₂Ab =>
        -- t₂ ∈ J.biUnion Ab
        obtain ⟨i, hiJ, ht₁Ab_i⟩ := Finset.mem_biUnion.mp ht₁Ab
        obtain ⟨j, hjJ, ht₂Ab_j⟩ := Finset.mem_biUnion.mp ht₂Ab
        by_cases hij : i = j
        · -- i = j, use hAbd
          subst hij
          exact hAbd i (hJI hiJ) t₁ ht₁Ab_i t₂ ht₂Ab_j hne
        · -- i ≠ j, use hcross
          have hcross' := hcross j (hJI hjJ) i (hJI hiJ) (Ne.symm hij)
          have hT1 : triEdges t₁ ⊆ (B i).biUnion triEdges ∪ S i := by
            have hcov := hAbcov i (hJI hiJ)
            simp only [coveredEdges] at hcov
            exact Finset.subset_iff.mpr (fun e he => by rw [← hcov]; exact Finset.mem_biUnion.mpr ⟨t₁, ht₁Ab_i, he⟩)
          have hT2 : triEdges t₂ ⊆ (B j).biUnion triEdges ∪ S j := by
            have hcov := hAbcov j (hJI hjJ)
            simp only [coveredEdges] at hcov
            exact Finset.subset_iff.mpr (fun e he => by rw [← hcov]; exact Finset.mem_biUnion.mpr ⟨t₂, ht₂Ab_j, he⟩)
          exact (Finset.disjoint_of_subset_left hT2 (Finset.disjoint_of_subset_right hT1 hcross')).symm
  · -- coveredEdges P = (I.biUnion fun i => coveredEdges (B i)) ∪ J.biUnion S
    simp only [coveredEdges]
    -- P = (I \ J).biUnion B ∪ J.biUnion Ab
    have hP : P = (I \ J).biUnion B ∪ J.biUnion (fun i => Ab i) := rfl
    simp only [P]
    ext e
    simp only [mem_biUnion, mem_union, mem_sdiff]
    constructor
    · intro ⟨a, haP, hai_tri⟩
      cases haP with
      | inl hB =>
        -- a ∈ B i for some i ∈ I \ J
        obtain ⟨i, ⟨hiI, hiJ⟩, hai⟩ := hB
        left
        exact ⟨i, hiI, a, hai, hai_tri⟩
      | inr hAb =>
        -- a ∈ Ab i for some i ∈ J
        obtain ⟨i, hiJ, hai⟩ := hAb
        -- By hAbcov, coveredEdges (Ab i) = coveredEdges (B i) ∪ S i
        have hcov := hAbcov i (hJI hiJ)
        rw [coveredEdges] at hcov
        -- e ∈ triEdges a ⊆ (Ab i).biUnion triEdges
        have he : e ∈ (Ab i).biUnion triEdges := Finset.mem_biUnion.mpr ⟨a, hai, hai_tri⟩
        rw [hcov] at he
        rw [Finset.mem_union] at he
        cases he with
        | inl hBcov =>
          -- e ∈ coveredEdges (B i), so e ∈ (B i).biUnion triEdges
          rw [coveredEdges] at hBcov
          obtain ⟨b, hbB, hb_tri⟩ := Finset.mem_biUnion.mp hBcov
          left
          exact ⟨i, hJI hiJ, b, hbB, hb_tri⟩
        | inr hSi =>
          -- e ∈ S i
          right
          exact ⟨i, hiJ, hSi⟩
    · intro h
      cases h with
      | inl hBI =>
        -- ∃ i ∈ I, ∃ b ∈ B i, e ∈ triEdges b
        obtain ⟨i, hiI, b, hbB, hb_tri⟩ := hBI
        by_cases hiJ : i ∈ J
        · -- i ∈ J, need to find b' ∈ Ab i with e ∈ triEdges b'
          have hcov := hAbcov i hiI
          rw [coveredEdges] at hcov
          -- e ∈ triEdges b ⊆ (B i).biUnion triEdges ⊆ coveredEdges (B i) ⊆ coveredEdges (Ab i)
          have heb_cov : e ∈ (B i).biUnion triEdges := Finset.mem_biUnion.mpr ⟨b, hbB, hb_tri⟩
          have he_Ab : e ∈ (Ab i).biUnion triEdges := by
            rw [hcov]
            exact Finset.mem_union.mpr (Or.inl heb_cov)
          obtain ⟨b', hb'Ab, hb'_tri⟩ := Finset.mem_biUnion.mp he_Ab
          exact ⟨b', Or.inr ⟨i, hiJ, hb'Ab⟩, hb'_tri⟩
        · -- i ∈ I \ J, use b directly
          exact ⟨b, Or.inl ⟨i, ⟨hiI, hiJ⟩, hbB⟩, hb_tri⟩
      | inr hSj =>
        -- ∃ i ∈ J, e ∈ S i
        obtain ⟨i, hiJ, hei⟩ := hSj
        have hcov := hAbcov i (hJI hiJ)
        rw [coveredEdges] at hcov
        -- e ∈ S i ⊆ coveredEdges (Ab i) = (Ab i).biUnion triEdges
        have he_Ab : e ∈ (Ab i).biUnion triEdges := by
          rw [hcov]
          exact Finset.mem_union.mpr (Or.inr hei)
        obtain ⟨b', hb'Ab, hb'_tri⟩ := Finset.mem_biUnion.mp he_Ab
        exact ⟨b', Or.inr ⟨i, hiJ, hb'Ab⟩, hb'_tri⟩

end Ax2.BKLO
