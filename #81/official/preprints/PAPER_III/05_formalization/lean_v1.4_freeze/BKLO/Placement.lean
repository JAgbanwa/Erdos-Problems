/-
# Placing the abstract absorbers inside the host graph (§5 applied to §8.1).

`BKLO.AbsorberExists` produces, for every triangle-divisible edge set `H` over `ℕ`, an absorber `A`
that uses fresh vertices.  `BKLO.exists_embedding` (§5) places one such gadget inside a host graph
with large common neighbourhoods.  Here we iterate the placement over a *finite family* of abstract
absorbers, giving each its own private set of fresh host vertices.  This is exactly the absorbing
structure that §11 reserves inside `G` before running the near-optimal decomposition.

The output is recorded by the predicate `Placement`: a family `B` of edge sets of `G`, with private
vertex sets `W`, such that `B H` absorbs the copy of `H` inside `G`, every edge of `B H` meets
`W H`, and the `W H` are pairwise disjoint and disjoint from the root set.
-/
import BKLO.TransportV

open Finset

namespace BKLO

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A triangle-decomposable edge set has no loops. -/
theorem TriDecomp.loopless {W : Type*} [DecidableEq W] {E : Finset (Sym2 W)} (h : TriDecomp E) :
    ∀ e ∈ E, ¬ e.IsDiag := by
  obtain ⟨P, _, _, he⟩ := h
  intro e heE
  rw [← he] at heE
  obtain ⟨t, _, het⟩ := Finset.mem_biUnion.1 heE
  exact (mem_cliqueEdgesV.1 het).2

/-- The data produced by placing a finite family of abstract absorbers inside `G`, on the roots
`e₀ '' [0, C)` = `U'`. -/
structure Placement (G : SimpleGraph V) [DecidableRel G.Adj] (C : ℕ) (e₀ : ℕ → V) (U' : Finset V)
    (Hs : Finset (Finset (Sym2 ℕ))) (Abs : Finset (Sym2 ℕ) → Finset (Sym2 ℕ))
    (B : Finset (Sym2 ℕ) → Finset (Sym2 V)) (W : Finset (Sym2 ℕ) → Finset V) : Prop where
  sub : ∀ H ∈ Hs, B H ⊆ G.edgeFinset
  absorber : ∀ H ∈ Hs, IsAbsorber (B H) (H.image (Sym2.map e₀))
  card_le : ∀ H ∈ Hs, (B H).card ≤ (Abs H).card
  fresh_disj : ∀ H ∈ Hs, Disjoint (W H) U'
  edge_meets : ∀ H ∈ Hs, ∀ f ∈ B H, ∃ v ∈ f, v ∈ W H
  edge_in : ∀ H ∈ Hs, ∀ f ∈ B H, ∀ v ∈ f, v ∈ U' ∨ v ∈ W H
  pairwise : ∀ H₁ ∈ Hs, ∀ H₂ ∈ Hs, H₁ ≠ H₂ → Disjoint (W H₁) (W H₂)

/-- Placing a single abstract absorber. -/
theorem exists_place_one (G : SimpleGraph V) [DecidableRel G.Adj] (C : ℕ)
    (e₀ : ℕ → V) (hinj : ∀ u < C, ∀ v < C, e₀ u = e₀ v → u = v)
    (U' : Finset V) (hU' : U' = (Finset.range C).image e₀)
    {H A : Finset (Sym2 ℕ)} (hH : ∀ v ∈ supp H, v < C) (hSA : SparseAbsorber 9 C H A)
    (F : Finset V) (hUF : U' ⊆ F)
    (hroom : ∀ S : Finset V, S.card ≤ 9 → F.card + (supp A).card < (commonNbrs G S).card) :
    ∃ (B : Finset (Sym2 V)) (W : Finset V),
      B ⊆ G.edgeFinset ∧ IsAbsorber B (H.image (Sym2.map e₀)) ∧ B.card ≤ A.card ∧
      Disjoint W F ∧ W.card ≤ (supp A).card ∧
      (∀ f ∈ B, ∃ v ∈ f, v ∈ W) ∧ (∀ f ∈ B, ∀ v ∈ f, v ∈ U' ∨ v ∈ W) := by
  classical
  obtain ⟨habs, htouch, hsupp, hdeg⟩ := hSA
  have hloop : ∀ e ∈ A, ¬ e.IsDiag := habs.2.1.loopless
  obtain ⟨f, hfb, hfF, hfinjA, hfe⟩ :=
    exists_embedding G hdeg hloop htouch e₀ F
      (fun u _ v _ hu hv h => hinj u hu v hv h) hroom
  -- `f` agrees with `e₀` on the roots
  have hfH : ∀ e ∈ H, Sym2.map f e = Sym2.map e₀ e := by
    intro e he
    induction e using Sym2.ind with
    | _ x y =>
      have hx : x < C := hH x (mem_supp.2 ⟨_, he, by simp⟩)
      have hy : y < C := hH y (mem_supp.2 ⟨_, he, by simp⟩)
      simp [hfb x hx, hfb y hy]
  -- injectivity of `f` on the vertices of `A ∪ H`
  have hsuppU : supp (A ∪ H) = supp A ∪ supp H := supp_union A H
  have hkey : ∀ u ∈ supp (A ∪ H), ∀ v ∈ supp (A ∪ H), f u = f v → u = v := by
    have hbase : ∀ u ∈ supp (A ∪ H), (u < C ∧ f u = e₀ u) ∨ (C ≤ u ∧ u ∈ supp A ∧ f u ∉ F) := by
      intro u hu
      rw [hsuppU, Finset.mem_union] at hu
      rcases hu with hu | hu
      · rcases hsupp u hu with h | h
        · exact Or.inl ⟨hH u h, hfb u (hH u h)⟩
        · exact Or.inr ⟨h, hu, hfF u hu h⟩
      · exact Or.inl ⟨hH u hu, hfb u (hH u hu)⟩
    intro u hu v hv heq
    rcases hbase u hu with ⟨hu1, hu2⟩ | ⟨hu1, hu2, hu3⟩ <;>
      rcases hbase v hv with ⟨hv1, hv2⟩ | ⟨hv1, hv2, hv3⟩
    · exact hinj u hu1 v hv1 (by rw [← hu2, ← hv2]; exact heq)
    · exact absurd (heq ▸ hu2 ▸ hUF (hU' ▸ Finset.mem_image_of_mem e₀
        (Finset.mem_range.2 hu1))) hv3
    · exact absurd (heq ▸ hv2 ▸ hUF (hU' ▸ Finset.mem_image_of_mem e₀
        (Finset.mem_range.2 hv1))) (by rw [heq] at hu3 ⊢; exact hu3)
    · exact hfinjA u hu2 v hv2 heq
  refine ⟨A.image (Sym2.map f), ((supp A).filter (fun v => C ≤ v)).image f, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · intro e he
    obtain ⟨e', he', rfl⟩ := Finset.mem_image.1 he
    exact hfe e' he'
  · have := IsAbsorber.mapOn hkey habs
    have himg : H.image (Sym2.map f) = H.image (Sym2.map e₀) :=
      Finset.image_congr (fun e he => hfH e he)
    rwa [himg] at this
  · exact Finset.card_image_le
  · rw [Finset.disjoint_left]
    rintro w hw hwF
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hw
    obtain ⟨hxA, hxC⟩ := Finset.mem_filter.1 hx
    exact hfF x hxA hxC hwF
  · exact le_trans Finset.card_image_le (Finset.card_filter_le _ _)
  · rintro g hg
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hg
    obtain ⟨x, hx, hxC⟩ := htouch e he
    exact ⟨f x, Sym2.mem_map.2 ⟨x, hx, rfl⟩,
      Finset.mem_image_of_mem f (Finset.mem_filter.2 ⟨mem_supp.2 ⟨e, he, hx⟩, hxC⟩)⟩
  · rintro g hg v hv
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hg
    obtain ⟨x, hx, rfl⟩ := Sym2.mem_map.1 hv
    have hxA : x ∈ supp A := mem_supp.2 ⟨e, he, hx⟩
    by_cases hxC : C ≤ x
    · exact Or.inr (Finset.mem_image_of_mem f (Finset.mem_filter.2 ⟨hxA, hxC⟩))
    · push_neg at hxC
      rw [hfb x hxC, hU']
      exact Or.inl (Finset.mem_image_of_mem e₀ (Finset.mem_range.2 hxC))

/-- The inductive form of the placement: everything already used is collected in `F`. -/
theorem exists_placement_aux (G : SimpleGraph V) [DecidableRel G.Adj] (C : ℕ)
    (e₀ : ℕ → V) (hinj : ∀ u < C, ∀ v < C, e₀ u = e₀ v → u = v)
    (U' : Finset V) (hU' : U' = (Finset.range C).image e₀)
    (Abs : Finset (Sym2 ℕ) → Finset (Sym2 ℕ)) :
    ∀ (Hs : Finset (Finset (Sym2 ℕ))) (F : Finset V), U' ⊆ F →
      (∀ H ∈ Hs, ∀ v ∈ supp H, v < C) → (∀ H ∈ Hs, SparseAbsorber 9 C H (Abs H)) →
      (∀ S : Finset V, S.card ≤ 9 →
        F.card + (∑ H ∈ Hs, (supp (Abs H)).card) < (commonNbrs G S).card) →
      ∃ B W, Placement G C e₀ U' Hs Abs B W ∧ (∀ H ∈ Hs, Disjoint (W H) F) := by
  classical
  intro Hs
  induction Hs using Finset.induction_on with
  | empty =>
    intro F _ _ _ _
    exact ⟨fun _ => ∅, fun _ => ∅, ⟨by simp, by simp, by simp, by simp, by simp, by simp, by simp⟩,
      by simp⟩
  | insert H₀ Hs hH₀ ih =>
    intro F hUF hsupp hSA hroom
    have hmemins : ∀ H ∈ Hs, H ∈ insert H₀ Hs := fun H hH => Finset.mem_insert_of_mem hH
    have hsum : (∑ H ∈ insert H₀ Hs, (supp (Abs H)).card)
        = (supp (Abs H₀)).card + ∑ H ∈ Hs, (supp (Abs H)).card := Finset.sum_insert hH₀
    -- place `H₀`
    obtain ⟨B₀, W₀, hB₀sub, hB₀abs, hB₀card, hW₀F, hW₀card, hB₀meets, hB₀in⟩ :=
      exists_place_one G C e₀ hinj U' hU' (hsupp H₀ (Finset.mem_insert_self _ _))
        (hSA H₀ (Finset.mem_insert_self _ _)) F hUF
        (fun S hS => lt_of_le_of_lt (by omega) (hroom S hS))
    -- place the rest, avoiding `W₀` as well
    obtain ⟨B, W, hP, hWF⟩ := ih (F ∪ W₀) (Finset.Subset.trans hUF Finset.subset_union_left)
      (fun H hH => hsupp H (hmemins H hH)) (fun H hH => hSA H (hmemins H hH))
      (fun S hS => by
        have h1 : (F ∪ W₀).card ≤ F.card + (supp (Abs H₀)).card :=
          le_trans (Finset.card_union_le _ _) (Nat.add_le_add_left hW₀card _)
        exact lt_of_le_of_lt (by omega) (hroom S hS))
    have hneH : ∀ H ∈ Hs, H ≠ H₀ := by
      intro H hH h
      subst h
      exact hH₀ hH
    have hBupd : ∀ H ∈ Hs, Function.update B H₀ B₀ H = B H := fun H hH =>
      Function.update_of_ne (hneH H hH) _ _
    have hWupd : ∀ H ∈ Hs, Function.update W H₀ W₀ H = W H := fun H hH =>
      Function.update_of_ne (hneH H hH) _ _
    refine ⟨Function.update B H₀ B₀, Function.update W H₀ W₀, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · intro H hH
      rcases Finset.mem_insert.1 hH with rfl | hH'
      · rw [Function.update_self]; exact hB₀sub
      · rw [hBupd H hH']; exact hP.sub H hH'
    · intro H hH
      rcases Finset.mem_insert.1 hH with rfl | hH'
      · rw [Function.update_self]; exact hB₀abs
      · rw [hBupd H hH']; exact hP.absorber H hH'
    · intro H hH
      rcases Finset.mem_insert.1 hH with rfl | hH'
      · rw [Function.update_self]; exact hB₀card
      · rw [hBupd H hH']; exact hP.card_le H hH'
    · intro H hH
      rcases Finset.mem_insert.1 hH with rfl | hH'
      · rw [Function.update_self]; exact Finset.disjoint_of_subset_right hUF hW₀F
      · rw [hWupd H hH']; exact hP.fresh_disj H hH'
    · intro H hH
      rcases Finset.mem_insert.1 hH with rfl | hH'
      · rw [Function.update_self, Function.update_self]; exact hB₀meets
      · rw [hBupd H hH', hWupd H hH']; exact hP.edge_meets H hH'
    · intro H hH
      rcases Finset.mem_insert.1 hH with rfl | hH'
      · rw [Function.update_self, Function.update_self]; exact hB₀in
      · rw [hBupd H hH', hWupd H hH']; exact hP.edge_in H hH'
    · intro H₁ h₁ H₂ h₂ hne
      rcases Finset.mem_insert.1 h₁ with rfl | h₁' <;>
        rcases Finset.mem_insert.1 h₂ with rfl | h₂'
      · exact absurd rfl hne
      · rw [Function.update_self, hWupd H₂ h₂']
        exact (Finset.disjoint_of_subset_right Finset.subset_union_right (hWF H₂ h₂')).symm
      · rw [Function.update_self, hWupd H₁ h₁']
        exact Finset.disjoint_of_subset_right Finset.subset_union_right (hWF H₁ h₁')
      · rw [hWupd H₁ h₁', hWupd H₂ h₂']
        exact hP.pairwise H₁ h₁' H₂ h₂' hne
    · intro H hH
      rcases Finset.mem_insert.1 hH with rfl | hH'
      · rw [Function.update_self]; exact hW₀F
      · rw [hWupd H hH']
        exact Finset.disjoint_of_subset_right Finset.subset_union_left (hWF H hH')

/-- **Placing the whole family.**  If the host has large enough common neighbourhoods for `9`-sets,
every finite family of `9`-degenerate abstract absorbers rooted below `C` can be placed inside `G`
on pairwise disjoint sets of fresh vertices. -/
theorem exists_placement (G : SimpleGraph V) [DecidableRel G.Adj] (C : ℕ)
    (e₀ : ℕ → V) (hinj : ∀ u < C, ∀ v < C, e₀ u = e₀ v → u = v)
    (U' : Finset V) (hU' : U' = (Finset.range C).image e₀)
    (Hs : Finset (Finset (Sym2 ℕ))) (Abs : Finset (Sym2 ℕ) → Finset (Sym2 ℕ))
    (hsub : ∀ H ∈ Hs, ∀ v ∈ supp H, v < C)
    (hSA : ∀ H ∈ Hs, SparseAbsorber 9 C H (Abs H))
    (hroom : ∀ S : Finset V, S.card ≤ 9 →
      C + 2 * (∑ H ∈ Hs, (supp (Abs H)).card) < (commonNbrs G S).card) :
    ∃ B W, Placement G C e₀ U' Hs Abs B W := by
  have hU'card : U'.card ≤ C := by
    rw [hU']
    exact le_trans Finset.card_image_le (by simp)
  obtain ⟨B, W, hP, -⟩ :=
    exists_placement_aux G C e₀ hinj U' hU' Abs Hs U' (Finset.Subset.refl U') hsub hSA
      (fun S hS => lt_of_le_of_lt (by omega) (hroom S hS))
  exact ⟨B, W, hP⟩

end BKLO
