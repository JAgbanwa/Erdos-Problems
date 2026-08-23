/-
  Part B (Phase 2) — the absorber, correctly decomposed via the `reroute` engine.

  The octahedral `FlexUnit` route is a DEAD END for absorption: its two decompositions cover the
  same edges (`cover1 = cover2`), so `reroute` yields empty configs and cannot absorb a nonempty
  leftover. The correct atom is a *transformer* with a nonempty config `S` (`coveredEdges (Ab i) =
  coveredEdges (B i) ∪ S i`), which is exactly what the (proved) `reroute` consumes.

  This file proves `absorber_of_transformer_bank`: a reserved bank of pairwise edge-disjoint
  transformers whose configs can realise EVERY admissible leftover (the `hrich` hypothesis) is a
  `TriangleAbsorber`. All the `reroute`-application bookkeeping is discharged here; the sole
  remaining (genuinely hard, BKLO) obligation is `hrich` — the existence of such a rich bank in a
  graph with `δ ≥ 9n/10`.
-/
import Ax2.PartB.BKLO.Reroute

namespace Ax2.BKLO

open SimpleGraph Finset Ax2

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `coveredEdges` of a `biUnion` of triangle families is the `biUnion` of their `coveredEdges`. -/
theorem coveredEdges_biUnion {ι : Type*} [DecidableEq ι] (I : Finset ι)
    (B : ι → Finset (Finset V)) :
    coveredEdges (I.biUnion B) = I.biUnion (fun i => coveredEdges (B i)) := by
  unfold coveredEdges
  rw [Finset.biUnion_biUnion]

/-- **Absorber from a transformer bank.** A family `(B i, Ab i, S i)_{i∈I}` of `G`-triangle
transformers — `Ab i` covers `B i`'s edges plus the config `S i`, pairwise edge-disjoint — whose
configs can realise every admissible leftover (`hrich`) is a `β`-absorber with core
`A = ⋃_{i∈I} B i`. Proof: `reroute` on the sub-collection `J` realising the given leftover. -/
theorem absorber_of_transformer_bank (G : SimpleGraph V) [DecidableRel G.Adj] (β : ℝ)
    {ι : Type*} [DecidableEq ι] (I : Finset ι)
    (B Ab : ι → Finset (Finset V)) (S : ι → Finset (Sym2 V))
    (hBcl : ∀ i ∈ I, ∀ t ∈ B i, G.IsNClique 3 t)
    (hAbcl : ∀ i ∈ I, ∀ t ∈ Ab i, G.IsNClique 3 t)
    (hAbcov : ∀ i ∈ I, coveredEdges (Ab i) = coveredEdges (B i) ∪ S i)
    (hBd : ∀ i ∈ I, EdgeDisjoint (B i)) (hAbd : ∀ i ∈ I, EdgeDisjoint (Ab i))
    (hcross : ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
      Disjoint (coveredEdges (B i) ∪ S i) (coveredEdges (B j) ∪ S j))
    (hrich : ∀ L : Finset (Sym2 V), L ⊆ G.edgeFinset →
      Disjoint L (I.biUnion (fun i => coveredEdges (B i))) →
      (L.card : ℝ) ≤ β * (Fintype.card V : ℝ) ^ 2 → 3 ∣ L.card →
      (∀ v : V, Even ((L.filter (fun e => v ∈ e)).card)) →
      ∃ J ⊆ I, J.biUnion S = L) :
    TriangleAbsorber G (I.biUnion (fun i => B i)) β := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · -- every triangle of the core is a `G`-triangle
    intro t ht
    obtain ⟨i, hiI, hti⟩ := Finset.mem_biUnion.mp ht
    exact hBcl i hiI t hti
  · -- the core is edge-disjoint
    intro t₁ ht₁ t₂ ht₂ hne
    obtain ⟨i, hiI, ht₁i⟩ := Finset.mem_biUnion.mp ht₁
    obtain ⟨j, hjI, ht₂j⟩ := Finset.mem_biUnion.mp ht₂
    by_cases hij : i = j
    · subst hij; exact hBd i hiI t₁ ht₁i t₂ ht₂j hne
    · have hc := hcross i hiI j hjI hij
      have hT1 : triEdges t₁ ⊆ coveredEdges (B i) ∪ S i :=
        (Finset.subset_biUnion_of_mem triEdges ht₁i).trans Finset.subset_union_left
      have hT2 : triEdges t₂ ⊆ coveredEdges (B j) ∪ S j :=
        (Finset.subset_biUnion_of_mem triEdges ht₂j).trans Finset.subset_union_left
      exact Finset.disjoint_of_subset_left hT1 (Finset.disjoint_of_subset_right hT2 hc)
  · -- absorb an admissible leftover `L`
    intro L hLsub hLdisj hLcard hLdiv hLeven
    have hAcov : coveredEdges (I.biUnion (fun i => B i))
        = I.biUnion (fun i => coveredEdges (B i)) := coveredEdges_biUnion I B
    rw [hAcov] at hLdisj
    obtain ⟨J, hJI, hJcfg⟩ := hrich L hLsub hLdisj hLcard hLdiv hLeven
    obtain ⟨P, hPmem, hPd, hPcov⟩ :=
      reroute I J hJI B Ab S hAbcov hBd hAbd hcross
    refine ⟨P, ?_, hPd, ?_⟩
    · -- `P`'s triangles are `G`-triangles: `P` lives inside `⋃_{I∖J} B ∪ ⋃_J Ab`
      intro t ht
      have hts := hPmem ht
      rw [Finset.mem_union] at hts
      rcases hts with h | h
      · obtain ⟨i, hiIJ, hti⟩ := Finset.mem_biUnion.mp h
        exact hBcl i (Finset.mem_sdiff.mp hiIJ).1 t hti
      · obtain ⟨i, hiJ, hti⟩ := Finset.mem_biUnion.mp h
        exact hAbcl i (hJI hiJ) t hti
    · -- coverage: `coveredEdges P = coveredEdges A ∪ L`
      rw [hPcov, hAcov, hJcfg]
end Ax2.BKLO
