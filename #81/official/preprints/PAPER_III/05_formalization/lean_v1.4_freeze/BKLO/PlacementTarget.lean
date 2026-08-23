/-
# BKLO §5: placing a family of absorbers with prescribed targets

`BKLO.exists_placement` places a finite family of `9`-degenerate abstract absorbers inside a host
graph, edge-disjointly, with no control on *where* the new vertices go.  For the §11 cells route
the location matters: the reservation has to be spread at the scale of a single bottom cell of the
vortex, so each new vertex must be routed to its own prescribed region (in the application, its own
bottom cell).

This file proves the corresponding variant, `BKLO.exists_placement_target`, on top of
`BKLO.exists_embedding_target`.  Besides the data of `BKLO.Placement` it records two extra facts
that the cells route needs:

* `fresh_mem` / `fresh_one` — every new vertex lies in its own target set, and each target set
  receives at most one new vertex;
* `root_deg` — a vertex sends at most `9` placed edges to the root set.  This is the degeneracy of
  the abstract absorbers, and it is what bounds the reserved degree *into a cell*.
-/
import BKLO.EmbeddingTarget
import BKLO.Placement

open Finset

namespace BKLO

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The data produced by placing a finite family of abstract absorbers inside `G` on the roots
`e₀ '' [0, C)` = `U'`, with each new vertex of the absorber of `H` routed into its own target set
`Y H u`. -/
structure PlacementT (G : SimpleGraph V) [DecidableRel G.Adj] (C : ℕ) (e₀ : ℕ → V) (U' : Finset V)
    (Hs : Finset (Finset (Sym2 ℕ))) (Abs : Finset (Sym2 ℕ) → Finset (Sym2 ℕ))
    (Y : Finset (Sym2 ℕ) → ℕ → Finset V)
    (B : Finset (Sym2 ℕ) → Finset (Sym2 V)) (W : Finset (Sym2 ℕ) → Finset V) : Prop where
  sub : ∀ H ∈ Hs, B H ⊆ G.edgeFinset
  absorber : ∀ H ∈ Hs, IsAbsorber (B H) (H.image (Sym2.map e₀))
  card_le : ∀ H ∈ Hs, (B H).card ≤ (Abs H).card
  fresh_disj : ∀ H ∈ Hs, Disjoint (W H) U'
  edge_meets : ∀ H ∈ Hs, ∀ f ∈ B H, ∃ v ∈ f, v ∈ W H
  edge_in : ∀ H ∈ Hs, ∀ f ∈ B H, ∀ v ∈ f, v ∈ U' ∨ v ∈ W H
  pairwise : ∀ H₁ ∈ Hs, ∀ H₂ ∈ Hs, H₁ ≠ H₂ → Disjoint (W H₁) (W H₂)
  fresh_mem : ∀ H ∈ Hs, ∀ v ∈ W H, ∃ u ∈ supp (Abs H), C ≤ u ∧ v ∈ Y H u
  fresh_one : ∀ H ∈ Hs, ∀ u ∈ supp (Abs H), C ≤ u → (W H ∩ Y H u).card ≤ 1
  root_deg : ∀ H ∈ Hs, ∀ x : V, (U'.filter (fun r => s(x, r) ∈ B H)).card ≤ 9

/-- Placing a single abstract absorber, with each new vertex routed into its own target set. -/
theorem exists_place_one_target (G : SimpleGraph V) [DecidableRel G.Adj] (C : ℕ)
    (e₀ : ℕ → V) (hinj : ∀ u < C, ∀ v < C, e₀ u = e₀ v → u = v)
    (U' : Finset V) (hU' : U' = (Finset.range C).image e₀)
    {H A : Finset (Sym2 ℕ)} (hH : ∀ v ∈ supp H, v < C) (hSA : SparseAbsorber 9 C H A)
    (F : Finset V) (hUF : U' ⊆ F) (Y : ℕ → Finset V)
    (hYF : ∀ u ∈ supp A, C ≤ u → Disjoint (Y u) F)
    (hYdisj : ∀ u ∈ supp A, ∀ v ∈ supp A, C ≤ u → C ≤ v → u ≠ v → Disjoint (Y u) (Y v))
    (hroom : ∀ u ∈ supp A, C ≤ u → ∀ Q : Finset V, Q.card ≤ 9 →
      (commonNbrs G Q ∩ Y u).Nonempty) :
    ∃ (B : Finset (Sym2 V)) (W : Finset V),
      B ⊆ G.edgeFinset ∧ IsAbsorber B (H.image (Sym2.map e₀)) ∧ B.card ≤ A.card ∧
      Disjoint W F ∧ W.card ≤ (supp A).card ∧
      (∀ f ∈ B, ∃ v ∈ f, v ∈ W) ∧ (∀ f ∈ B, ∀ v ∈ f, v ∈ U' ∨ v ∈ W) ∧
      (∀ v ∈ W, ∃ u ∈ supp A, C ≤ u ∧ v ∈ Y u) ∧
      (∀ u ∈ supp A, C ≤ u → (W ∩ Y u).card ≤ 1) ∧
      (∀ x : V, (U'.filter (fun r => s(x, r) ∈ B)).card ≤ 9) := by
  classical
  obtain ⟨habs, htouch, hsupp, hdeg⟩ := hSA
  have hloop : ∀ e ∈ A, ¬ e.IsDiag := habs.2.1.loopless
  have hrootF : ∀ v ∈ supp A, v < C → e₀ v ∈ F := by
    intro v _ hvC
    exact hUF (hU' ▸ Finset.mem_image_of_mem e₀ (Finset.mem_range.2 hvC))
  obtain ⟨f, hfb, hfY, hfinjA, hfe⟩ :=
    exists_embedding_target G hdeg hloop htouch e₀ F Y
      (fun u _ v _ hu hv h => hinj u hu v hv h) hrootF hYF hYdisj hroom
  have hfF : ∀ v ∈ supp A, C ≤ v → f v ∉ F := by
    intro v hv hvC hcon
    exact (Finset.disjoint_left.1 (hYF v hv hvC)) (hfY v hv hvC) hcon
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
  set W : Finset V := ((supp A).filter (fun v => C ≤ v)).image f with hWdef
  have hWmem : ∀ v ∈ W, ∃ u, C ≤ u ∧ u ∈ supp A ∧ f u = v := by
    intro v hv
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hv
    obtain ⟨huA, huC⟩ := Finset.mem_filter.1 hu
    exact ⟨u, huC, huA, rfl⟩
  have hWF : Disjoint W F := by
    rw [Finset.disjoint_left]
    intro w hw hwF
    obtain ⟨x, hxC, hxA, rfl⟩ := hWmem w hw
    exact hfF x hxA hxC hwF
  have hWU' : Disjoint W U' := Finset.disjoint_of_subset_right hUF hWF
  set B : Finset (Sym2 V) := A.image (Sym2.map f) with hBdef
  have hedge_in : ∀ g ∈ B, ∀ v ∈ g, v ∈ U' ∨ v ∈ W := by
    rintro g hg v hv
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hg
    obtain ⟨x, hx, rfl⟩ := Sym2.mem_map.1 hv
    have hxA : x ∈ supp A := mem_supp.2 ⟨e, he, hx⟩
    by_cases hxC : C ≤ x
    · exact Or.inr (Finset.mem_image_of_mem f (Finset.mem_filter.2 ⟨hxA, hxC⟩))
    · push_neg at hxC
      rw [hfb x hxC, hU']
      exact Or.inl (Finset.mem_image_of_mem e₀ (Finset.mem_range.2 hxC))
  have hedge_meets : ∀ g ∈ B, ∃ v ∈ g, v ∈ W := by
    rintro g hg
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hg
    obtain ⟨x, hx, hxC⟩ := htouch e he
    exact ⟨f x, Sym2.mem_map.2 ⟨x, hx, rfl⟩,
      Finset.mem_image_of_mem f (Finset.mem_filter.2 ⟨mem_supp.2 ⟨e, he, hx⟩, hxC⟩)⟩
  refine ⟨B, W, ?_, ?_, ?_, hWF, ?_, hedge_meets, hedge_in, ?_, ?_, ?_⟩
  · intro e he
    obtain ⟨e', he', rfl⟩ := Finset.mem_image.1 he
    exact hfe e' he'
  · have := IsAbsorber.mapOn hkey habs
    have himg : H.image (Sym2.map f) = H.image (Sym2.map e₀) :=
      Finset.image_congr (fun e he => hfH e he)
    rwa [himg] at this
  · exact Finset.card_image_le
  · exact le_trans Finset.card_image_le (Finset.card_filter_le _ _)
  · intro v hv
    obtain ⟨u, huC, huA, rfl⟩ := hWmem v hv
    exact ⟨u, huA, huC, hfY u huA huC⟩
  · -- each target set receives at most one new vertex
    intro u huA0 huC
    refine le_trans (Finset.card_le_card (?_ : W ∩ Y u ⊆ {f u})) (by simp)
    intro v hv
    obtain ⟨hvW, hvY⟩ := Finset.mem_inter.1 hv
    obtain ⟨w, hwC, hwA, rfl⟩ := hWmem v hvW
    have hwY : f w ∈ Y w := hfY w hwA hwC
    by_cases hwu : w = u
    · simp [hwu]
    · exact absurd hvY (Finset.disjoint_left.1 (hYdisj w hwA u huA0 hwC huC hwu) hwY)
  · -- the degeneracy bound: at most `9` placed edges from a vertex to the roots
    intro x
    by_cases hxW : x ∈ W
    · obtain ⟨w, hwC, hwA, rfl⟩ := hWmem x hxW
      have hsub : U'.filter (fun r => s(f w, r) ∈ B) ⊆ (backNbrs A w).image f := by
        intro r hr
        obtain ⟨hrU, hrB⟩ := Finset.mem_filter.1 hr
        obtain ⟨e, heA, hemap⟩ := Finset.mem_image.1 hrB
        induction e using Sym2.ind with
        | _ a b =>
          have haA : a ∈ supp A := mem_supp.2 ⟨_, heA, by simp⟩
          have hbA : b ∈ supp A := mem_supp.2 ⟨_, heA, by simp⟩
          rw [Sym2.map_pair_eq, Sym2.eq_iff] at hemap
          have key : ∀ p q : ℕ, p ∈ supp A → q ∈ supp A → s(p, q) ∈ A → f p = f w → f q = r →
              r ∈ (backNbrs A w).image f := by
            intro p q hpA hqA hpq hpw hqr
            have hpw' : p = w := hfinjA p hpA w hwA hpw
            subst hpw'
            have hqC : q < C := by
              by_contra hcon
              push_neg at hcon
              exact (Finset.disjoint_left.1 (hYF q hqA hcon)) (hqr ▸ hfY q hqA hcon) (hUF hrU)
            refine Finset.mem_image.2 ⟨q, Finset.mem_filter.2 ⟨hqA, by omega, ?_⟩, hqr⟩
            rw [Sym2.eq_swap]; exact hpq
          rcases hemap with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact key a b haA hbA heA h1 h2
          · exact key b a hbA haA (by rw [Sym2.eq_swap]; exact heA) h2 h1
      exact le_trans (Finset.card_le_card hsub) (le_trans Finset.card_image_le (hdeg w))
    · -- `x` carries no placed edge at all, or it is a root and its placed edges avoid `U'`
      have hempty : U'.filter (fun r => s(x, r) ∈ B) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro r hrU hrB
        obtain ⟨v, hv, hvW⟩ := hedge_meets _ hrB
        rcases Sym2.mem_iff.1 hv with rfl | rfl
        · exact hxW hvW
        · exact (Finset.disjoint_left.1 hWU') hvW hrU
      rw [hempty]; simp

/-- The inductive form of the targeted placement: everything already used is collected in `F`. -/
theorem exists_placement_target_aux (G : SimpleGraph V) [DecidableRel G.Adj] (C : ℕ)
    (e₀ : ℕ → V) (hinj : ∀ u < C, ∀ v < C, e₀ u = e₀ v → u = v)
    (U' : Finset V) (hU' : U' = (Finset.range C).image e₀)
    (Abs : Finset (Sym2 ℕ) → Finset (Sym2 ℕ)) (Y : Finset (Sym2 ℕ) → ℕ → Finset V) :
    ∀ (Hs : Finset (Finset (Sym2 ℕ))) (F : Finset V), U' ⊆ F →
      (∀ H ∈ Hs, ∀ u ∈ supp (Abs H), C ≤ u → Disjoint (Y H u) F) →
      (∀ H₁ ∈ Hs, ∀ H₂ ∈ Hs, ∀ u ∈ supp (Abs H₁), ∀ v ∈ supp (Abs H₂),
        C ≤ u → C ≤ v → (H₁ ≠ H₂ ∨ u ≠ v) → Disjoint (Y H₁ u) (Y H₂ v)) →
      (∀ H ∈ Hs, ∀ u ∈ supp (Abs H), C ≤ u → ∀ Q : Finset V, Q.card ≤ 9 →
        (commonNbrs G Q ∩ Y H u).Nonempty) →
      (∀ H ∈ Hs, ∀ v ∈ supp H, v < C) → (∀ H ∈ Hs, SparseAbsorber 9 C H (Abs H)) →
      ∃ B W, PlacementT G C e₀ U' Hs Abs Y B W ∧ (∀ H ∈ Hs, Disjoint (W H) F) := by
  classical
  intro Hs
  induction Hs using Finset.induction_on with
  | empty =>
    intro F _ _ _ _ _ _
    exact ⟨fun _ => ∅, fun _ => ∅,
      ⟨by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp⟩,
      by simp⟩
  | insert H₀ Hs hH₀ ih =>
    intro F hUF hYFall hYdisj hroom hsupp hSA
    have hmemins : ∀ H ∈ Hs, H ∈ insert H₀ Hs := fun H hH => Finset.mem_insert_of_mem hH
    -- place `H₀`
    obtain ⟨B₀, W₀, hB₀sub, hB₀abs, hB₀card, hW₀F, hW₀card, hB₀meets, hB₀in, hB₀mem, hB₀one,
      hB₀root⟩ :=
      exists_place_one_target G C e₀ hinj U' hU' (hsupp H₀ (Finset.mem_insert_self _ _))
        (hSA H₀ (Finset.mem_insert_self _ _)) F hUF (Y H₀)
        (fun u huA hu => hYFall H₀ (Finset.mem_insert_self _ _) u huA hu)
        (fun u huA v hvA hu hv hne => hYdisj H₀ (Finset.mem_insert_self _ _) H₀
          (Finset.mem_insert_self _ _) u huA v hvA hu hv (Or.inr hne))
        (fun u huA hu => hroom H₀ (Finset.mem_insert_self _ _) u huA hu)
    -- place the rest, avoiding `W₀` as well
    obtain ⟨B, W, hP, hWF⟩ := ih (F ∪ W₀) (Finset.Subset.trans hUF Finset.subset_union_left)
      (fun H hH u huA hu => by
        refine Finset.disjoint_union_right.2 ⟨hYFall H (hmemins H hH) u huA hu, ?_⟩
        refine Finset.disjoint_left.2 fun v hvY hvW => ?_
        obtain ⟨u', hu'A, hu'C, hu'Y⟩ := hB₀mem v hvW
        have hne : H ≠ H₀ := by rintro rfl; exact hH₀ hH
        exact (Finset.disjoint_left.1 (hYdisj H (hmemins H hH) H₀ (Finset.mem_insert_self _ _)
          u huA u' hu'A hu hu'C (Or.inl hne))) hvY hu'Y)
      (fun H₁ h₁ H₂ h₂ => hYdisj H₁ (hmemins H₁ h₁) H₂ (hmemins H₂ h₂))
      (fun H hH => hroom H (hmemins H hH))
      (fun H hH => hsupp H (hmemins H hH)) (fun H hH => hSA H (hmemins H hH))
    have hneH : ∀ H ∈ Hs, H ≠ H₀ := by
      intro H hH h
      subst h
      exact hH₀ hH
    have hBupd : ∀ H ∈ Hs, Function.update B H₀ B₀ H = B H := fun H hH =>
      Function.update_of_ne (hneH H hH) _ _
    have hWupd : ∀ H ∈ Hs, Function.update W H₀ W₀ H = W H := fun H hH =>
      Function.update_of_ne (hneH H hH) _ _
    refine ⟨Function.update B H₀ B₀, Function.update W H₀ W₀,
      ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
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
      · rw [Function.update_self]; exact hB₀mem
      · rw [hWupd H hH']; exact hP.fresh_mem H hH'
    · intro H hH
      rcases Finset.mem_insert.1 hH with rfl | hH'
      · rw [Function.update_self]; exact hB₀one
      · rw [hWupd H hH']; exact hP.fresh_one H hH'
    · intro H hH
      rcases Finset.mem_insert.1 hH with rfl | hH'
      · rw [Function.update_self]; exact hB₀root
      · rw [hBupd H hH']; exact hP.root_deg H hH'
    · intro H hH
      rcases Finset.mem_insert.1 hH with rfl | hH'
      · rw [Function.update_self]; exact hW₀F
      · rw [hWupd H hH']
        exact Finset.disjoint_of_subset_right Finset.subset_union_left (hWF H hH')

/-- **Placing the whole family into prescribed targets.**  If every target set meets the common
neighbourhood of any `9` vertices of `G`, and the target sets are pairwise disjoint and avoid the
roots, then every finite family of `9`-degenerate abstract absorbers rooted below `C` can be placed
inside `G` with each new vertex in its own target set. -/
theorem exists_placement_target (G : SimpleGraph V) [DecidableRel G.Adj] (C : ℕ)
    (e₀ : ℕ → V) (hinj : ∀ u < C, ∀ v < C, e₀ u = e₀ v → u = v)
    (U' : Finset V) (hU' : U' = (Finset.range C).image e₀)
    (Hs : Finset (Finset (Sym2 ℕ))) (Abs : Finset (Sym2 ℕ) → Finset (Sym2 ℕ))
    (Y : Finset (Sym2 ℕ) → ℕ → Finset V)
    (hsub : ∀ H ∈ Hs, ∀ v ∈ supp H, v < C)
    (hSA : ∀ H ∈ Hs, SparseAbsorber 9 C H (Abs H))
    (hYU : ∀ H ∈ Hs, ∀ u ∈ supp (Abs H), C ≤ u → Disjoint (Y H u) U')
    (hYdisj : ∀ H₁ ∈ Hs, ∀ H₂ ∈ Hs, ∀ u ∈ supp (Abs H₁), ∀ v ∈ supp (Abs H₂),
      C ≤ u → C ≤ v → (H₁ ≠ H₂ ∨ u ≠ v) → Disjoint (Y H₁ u) (Y H₂ v))
    (hroom : ∀ H ∈ Hs, ∀ u ∈ supp (Abs H), C ≤ u → ∀ Q : Finset V, Q.card ≤ 9 →
      (commonNbrs G Q ∩ Y H u).Nonempty) :
    ∃ B W, PlacementT G C e₀ U' Hs Abs Y B W := by
  obtain ⟨B, W, hP, -⟩ :=
    exists_placement_target_aux G C e₀ hinj U' hU' Abs Y Hs U'
      (Finset.Subset.refl U') (fun H hH u huA hu => hYU H hH u huA hu) hYdisj hroom hsub hSA
  exact ⟨B, W, hP⟩

end BKLO
