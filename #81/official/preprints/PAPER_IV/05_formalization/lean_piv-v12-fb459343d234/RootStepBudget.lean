import PaperIV.RootedSimplicialDefect

/-!
The graph-theoretic producer of the improved exceptional-row charge.
In an elimination step outside a prescribed clique, a maximum neighbourhood
clique misses at most min(s, number of remaining exterior vertices).
This strengthens the uniform s-per-row charge of the signed-star argument.
-/
namespace PaperIV.SublinearResearch
open Finset PaperIV.RootedSimplicialDefect

theorem exists_root_step_with_capped_budget {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {s : ℕ} (hG : RootedDefectAt G s)
    {U R : Finset V} (hRU : R ⊆ U) (hR : G.IsClique (R : Set V))
    (hne : (U \ R).Nonempty) :
    ∃ v ∈ U \ R, ∃ P : Finset V,
      P ⊆ neighborsIn G U v ∧ G.IsClique (P : Set V) ∧
      (neighborsIn G U v \ P).card ≤ min s ((U \ R).card-1) := by
  classical
  obtain ⟨v,hv,P0,hP0,hP0cl,hP0card⟩ := hG U R hRU hR hne
  let N := neighborsIn G U v
  let F : Finset (Finset V) := N.powerset.filter (fun (P : Finset V) => G.IsClique (P : Set V))
  have hP0F : P0 ∈ F := mem_filter.mpr ⟨mem_powerset.mpr hP0,hP0cl⟩
  obtain ⟨P,hPF,hmax⟩ := exists_max_image F card ⟨P0,hP0F⟩
  have hPN : P ⊆ N := mem_powerset.mp (mem_filter.mp hPF).1
  have hPcl : G.IsClique (P : Set V) := (mem_filter.mp hPF).2
  have hNRF : N ∩ R ∈ F := by
    apply mem_filter.mpr
    refine ⟨mem_powerset.mpr inter_subset_left,?_⟩
    intro a ha b hb hab
    exact hR (mem_inter.mp ha).2 (mem_inter.mp hb).2 hab
  have hmax0 := hmax P0 hP0F
  have hmaxR := hmax (N ∩ R) hNRF
  have hsub : N \ (N ∩ R) ⊆ (U \ R).erase v := by
    intro b hb
    obtain ⟨hbN,hbNR⟩ := mem_sdiff.mp hb
    have hbU : b ∈ U := (mem_filter.mp hbN).1
    have hbR : b ∉ R := fun h => hbNR (mem_inter.mpr ⟨hbN,h⟩)
    have hbv : b ≠ v := fun h => G.ne_of_adj (mem_filter.mp hbN).2 h.symm
    exact mem_erase.mpr ⟨hbv,mem_sdiff.mpr ⟨hbU,hbR⟩⟩
  have hcard := card_le_card hsub
  rw [card_sdiff_of_subset inter_subset_left, card_erase_of_mem hv] at hcard
  refine ⟨v,hv,P,hPN,hPcl,?_⟩
  rw [card_sdiff_of_subset hPN]
  apply le_min
  · change N.card ≤ P0.card+s at hP0card
    omega
  · omega

end PaperIV.SublinearResearch
#print axioms PaperIV.SublinearResearch.exists_root_step_with_capped_budget
