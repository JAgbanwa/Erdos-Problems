import PaperIV.RootedSimplicialDefect
import PaperIV.CliqueTree.Characterization

/-!
# Rooted simplicial defect zero is exactly chordality

`PaperIV.RootedSimplicialDefect.chordal_rootedDefect_zero` already shows that a
chordal graph has rooted defect `0`.  This module proves the converse, so that
`RootedDefectAt G 0` is a *literal* reformulation of chordality and the `s = 0`
instance of the fixed-defect clique-partition target is a genuine theorem about
the predicate `RootedDefectAt`, not about a different hypothesis.

The proof extracts a simplicial vertex of every induced subgraph directly from
the definition with the empty root, builds a perfect elimination order by
induction on the vertex set (the same induction used for the chordal direction
in `PaperIV.CliqueTree.PEO`), and closes with `SimpleGraph.IsPEO.isChordal`.
-/

namespace PaperIV.RootedDefectZero

open Finset
open PaperIV.RootedSimplicialDefect

variable {V : Type*} [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Defect `0` means: in every nonempty induced subgraph there is a vertex whose
neighbourhood inside that subgraph is a clique. -/
theorem exists_simplicial_in_of_rootedDefect_zero (h : RootedDefectAt G 0)
    {S : Finset V} (hS : S.Nonempty) :
    ∃ z ∈ S, ∀ a ∈ S, ∀ b ∈ S, G.Adj z a → G.Adj z b → a ≠ b → G.Adj a b := by
  have hne : (S \ (∅ : Finset V)).Nonempty := by simpa using hS
  obtain ⟨z, hz, C, hCsub, hCclique, hcard⟩ :=
    h S ∅ (Finset.empty_subset _) (by simp) hne
  have hzS : z ∈ S := (Finset.mem_sdiff.mp hz).1
  have hCeq : C = neighborsIn G S z :=
    Finset.eq_of_subset_of_card_le hCsub (by omega)
  refine ⟨z, hzS, ?_⟩
  intro a ha b hb hza hzb hab
  have haC : a ∈ C := by
    rw [hCeq]; exact Finset.mem_filter.mpr ⟨ha, hza⟩
  have hbC : b ∈ C := by
    rw [hCeq]; exact Finset.mem_filter.mpr ⟨hb, hzb⟩
  exact hCclique (by exact_mod_cast haC) (by exact_mod_cast hbC) hab

/-- Induction step producing a perfect elimination order on any vertex subset. -/
private theorem exists_peo_aux_of_defect_zero (h : RootedDefectAt G 0) :
    ∀ (m : ℕ) (S : Finset V), S.card = m → ∃ f : V → ℕ, Set.InjOn f S ∧
      ∀ v ∈ S, G.IsClique {u | u ∈ S ∧ f v < f u ∧ G.Adj v u} := by
  intro m
  induction m with
  | zero =>
      intro S hS
      rw [Finset.card_eq_zero] at hS
      subst hS
      exact ⟨fun _ => 0, by simp, by simp⟩
  | succ m ih =>
      intro S hS
      have hSne : S.Nonempty := Finset.card_pos.1 (by omega)
      obtain ⟨z, hzS, hsimp⟩ := exists_simplicial_in_of_rootedDefect_zero h hSne
      obtain ⟨f', hinj', hcl'⟩ := ih (S.erase z)
        (by rw [Finset.card_erase_of_mem hzS, hS]; omega)
      refine ⟨fun u => if u = z then 0 else f' u + 1, ?_, ?_⟩
      · intro a ha b hb hab
        simp only at hab
        by_cases haz : a = z
        · by_cases hbz : b = z
          · rw [haz, hbz]
          · rw [if_pos haz, if_neg hbz] at hab
            exact absurd hab.symm (Nat.succ_ne_zero _)
        · by_cases hbz : b = z
          · rw [if_neg haz, if_pos hbz] at hab
            exact absurd hab (Nat.succ_ne_zero _)
          · rw [if_neg haz, if_neg hbz] at hab
            exact hinj' (Finset.mem_coe.2 (Finset.mem_erase.2 ⟨haz, Finset.mem_coe.1 ha⟩))
              (Finset.mem_coe.2 (Finset.mem_erase.2 ⟨hbz, Finset.mem_coe.1 hb⟩)) (by omega)
      · intro u hu
        by_cases huz : u = z
        · subst huz
          intro a ha b hb hab
          exact hsimp a ha.1 b hb.1 ha.2.2 hb.2.2 hab
        · have hmem : u ∈ S.erase z := Finset.mem_erase.2 ⟨huz, hu⟩
          refine (hcl' u hmem).subset ?_
          intro x hx
          obtain ⟨hxS, hlt, hadj⟩ := hx
          simp only [huz, if_false] at hlt
          have hxz : x ≠ z := by
            rintro rfl
            simp at hlt
          refine ⟨Finset.mem_erase.2 ⟨hxz, hxS⟩, ?_, hadj⟩
          simp only [hxz, if_false] at hlt
          omega

/-- A graph of rooted simplicial defect `0` has a perfect elimination order. -/
theorem exists_isPEO_of_rootedDefect_zero [Fintype V] (h : RootedDefectAt G 0) :
    ∃ ord : V → ℕ, G.IsPEO ord := by
  obtain ⟨f, hinj, hclique⟩ :=
    exists_peo_aux_of_defect_zero h (Finset.univ.card) Finset.univ rfl
  refine ⟨f, ⟨fun a b hab => hinj (Finset.mem_coe.2 (Finset.mem_univ a))
      (Finset.mem_coe.2 (Finset.mem_univ b)) hab, fun v => ?_⟩⟩
  refine (hclique v (Finset.mem_univ v)).subset ?_
  intro u hu
  exact ⟨Finset.mem_univ u, hu.1, hu.2⟩

/-- **Defect zero implies chordality.** -/
theorem isChordal_of_rootedDefect_zero [Fintype V] (h : RootedDefectAt G 0) :
    SimpleGraph.IsChordal G := by
  obtain ⟨ord, hord⟩ := exists_isPEO_of_rootedDefect_zero h
  exact hord.isChordal

/-- **Rooted simplicial defect zero is exactly chordality.** -/
theorem rootedDefect_zero_iff_isChordal [Fintype V] :
    RootedDefectAt G 0 ↔ SimpleGraph.IsChordal G :=
  ⟨isChordal_of_rootedDefect_zero, fun hG => chordal_rootedDefect_zero G hG⟩

end PaperIV.RootedDefectZero
