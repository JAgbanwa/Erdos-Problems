/-
# BKLO §5: placing a family of absorbers avoiding a conflict relation

`BKLO.exists_placement` places a finite family of `9`-degenerate abstract absorbers inside a host
graph, edge-disjointly, with no control on *where* the new vertices go.  For the §11 cells route
the location matters: the reservation has to be spread at the scale of a single bottom cell of the
vortex.

This file proves the variant `BKLO.exists_placement_conf`, on top of
`BKLO.exists_embedding_conf`: every new vertex avoids the forbidden set `F` and is in conflict
neither with the prescribed set `Z` (which contains the roots) nor with any other new vertex.
Besides the data of `BKLO.Placement` it records

* `fresh_notF`, `fresh_confZ`, `fresh_conf` — the location control, and
* `root_deg` — a vertex sends at most `9` placed edges to the root set.  This is the degeneracy of
  the abstract absorbers, and it is what bounds the reserved degree *into the core cell*.
-/
import BKLO.EmbeddingConf
import BKLO.Placement

open Finset

namespace BKLO

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The data produced by placing a finite family of abstract absorbers inside `G` on the roots
`e₀ '' [0, C)` = `U'`, with every new vertex avoiding `F` and all conflicts. -/
structure PlacementC (G : SimpleGraph V) [DecidableRel G.Adj] (C : ℕ) (e₀ : ℕ → V) (U' : Finset V)
    (Hs : Finset (Finset (Sym2 ℕ))) (Abs : Finset (Sym2 ℕ) → Finset (Sym2 ℕ))
    (F Z : Finset V) (conf : V → V → Prop)
    (B : Finset (Sym2 ℕ) → Finset (Sym2 V)) (W : Finset (Sym2 ℕ) → Finset V) : Prop where
  sub : ∀ H ∈ Hs, B H ⊆ G.edgeFinset
  absorber : ∀ H ∈ Hs, IsAbsorber (B H) (H.image (Sym2.map e₀))
  card_le : ∀ H ∈ Hs, (B H).card ≤ (Abs H).card
  fresh_card : ∀ H ∈ Hs, (W H).card ≤ (supp (Abs H)).card
  edge_meets : ∀ H ∈ Hs, ∀ f ∈ B H, ∃ v ∈ f, v ∈ W H
  edge_in : ∀ H ∈ Hs, ∀ f ∈ B H, ∀ v ∈ f, v ∈ U' ∨ v ∈ W H
  fresh_notF : ∀ H ∈ Hs, ∀ v ∈ W H, v ∉ F
  fresh_confZ : ∀ H ∈ Hs, ∀ v ∈ W H, ∀ z ∈ Z, ¬ conf v z
  fresh_conf : ∀ H₁ ∈ Hs, ∀ v ∈ W H₁, ∀ H₂ ∈ Hs, ∀ w ∈ W H₂, v ≠ w → ¬ conf v w
  pairwise : ∀ H₁ ∈ Hs, ∀ H₂ ∈ Hs, H₁ ≠ H₂ → Disjoint (W H₁) (W H₂)
  root_deg : ∀ H ∈ Hs, ∀ x : V, (U'.filter (fun r => s(x, r) ∈ B H)).card ≤ 9

/-- Placing a single abstract absorber, avoiding the forbidden set and all conflicts. -/
theorem exists_place_one_conf (G : SimpleGraph V) [DecidableRel G.Adj] (C Kb : ℕ)
    (e₀ : ℕ → V) (hinj : ∀ u < C, ∀ v < C, e₀ u = e₀ v → u = v)
    (U' : Finset V) (hU' : U' = (Finset.range C).image e₀)
    {H A : Finset (Sym2 ℕ)} (hH : ∀ v ∈ supp H, v < C) (hSA : SparseAbsorber 9 C H A)
    (F Z : Finset V) (conf : V → V → Prop) [DecidableRel conf]
    (hrefl : ∀ x, conf x x) (hsymm : ∀ x y, conf x y → conf y x)
    (hU'F : U' ⊆ F) (hbud : Z.card + (supp A).card ≤ Kb)
    (hroom : ∀ Bad : Finset V, Bad.card ≤ Kb → ∀ Q : Finset V, Q.card ≤ 9 →
      ∃ y ∈ commonNbrs G Q, y ∉ F ∧ ∀ z ∈ Bad, ¬ conf y z) :
    ∃ (B : Finset (Sym2 V)) (W : Finset V),
      B ⊆ G.edgeFinset ∧ IsAbsorber B (H.image (Sym2.map e₀)) ∧ B.card ≤ A.card ∧
      (∀ v ∈ W, v ∉ F) ∧ W.card ≤ (supp A).card ∧
      (∀ f ∈ B, ∃ v ∈ f, v ∈ W) ∧ (∀ f ∈ B, ∀ v ∈ f, v ∈ U' ∨ v ∈ W) ∧
      (∀ v ∈ W, ∀ z ∈ Z, ¬ conf v z) ∧ (∀ v ∈ W, ∀ w ∈ W, v ≠ w → ¬ conf v w) ∧
      (∀ x : V, (U'.filter (fun r => s(x, r) ∈ B)).card ≤ 9) := by
  classical
  obtain ⟨habs, htouch, hsupp, hdeg⟩ := hSA
  have hloop : ∀ e ∈ A, ¬ e.IsDiag := habs.2.1.loopless
  obtain ⟨f, hfb, hfF, hfZ, hfconf, hfinjA, hfe⟩ :=
    exists_embedding_conf (Kb := Kb) G hdeg hloop htouch e₀ F Z conf hrefl hsymm
      (fun u _ v _ hu hv h => hinj u hu v hv h) hbud hroom
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
    · exact absurd (heq ▸ hu2 ▸ hU'F (hU' ▸ Finset.mem_image_of_mem e₀
        (Finset.mem_range.2 hu1))) hv3
    · exact absurd (heq ▸ hv2 ▸ hU'F (hU' ▸ Finset.mem_image_of_mem e₀
        (Finset.mem_range.2 hv1))) (by rw [heq] at hu3 ⊢; exact hu3)
    · exact hfinjA u hu2 v hv2 heq
  set W : Finset V := ((supp A).filter (fun v => C ≤ v)).image f with hWdef
  have hWmem : ∀ v ∈ W, ∃ u, C ≤ u ∧ u ∈ supp A ∧ f u = v := by
    intro v hv
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hv
    obtain ⟨huA, huC⟩ := Finset.mem_filter.1 hu
    exact ⟨u, huC, huA, rfl⟩
  have hWF : ∀ v ∈ W, v ∉ F := by
    intro w hw
    obtain ⟨x, hxC, hxA, rfl⟩ := hWmem w hw
    exact hfF x hxA hxC
  have hWU' : Disjoint W U' :=
    Finset.disjoint_left.2 fun v hv hvU => hWF v hv (hU'F hvU)
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
  · intro v hv z hz
    obtain ⟨u, huC, huA, rfl⟩ := hWmem v hv
    exact hfZ u huA huC z hz
  · intro v hv w hw hne
    obtain ⟨u, huC, huA, rfl⟩ := hWmem v hv
    obtain ⟨u', hu'C, hu'A, rfl⟩ := hWmem w hw
    exact hfconf u huA u' hu'A huC (by rintro rfl; exact hne rfl)
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
              exact hfF q hqA hcon (hqr ▸ hU'F hrU)
            refine Finset.mem_image.2 ⟨q, Finset.mem_filter.2 ⟨hqA, by omega, ?_⟩, hqr⟩
            rw [Sym2.eq_swap]; exact hpq
          rcases hemap with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact key a b haA hbA heA h1 h2
          · exact key b a hbA haA (by rw [Sym2.eq_swap]; exact heA) h2 h1
      exact le_trans (Finset.card_le_card hsub) (le_trans Finset.card_image_le (hdeg w))
    · have hempty : U'.filter (fun r => s(x, r) ∈ B) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro r hrU hrB
        obtain ⟨v, hv, hvW⟩ := hedge_meets _ hrB
        rcases Sym2.mem_iff.1 hv with rfl | rfl
        · exact hxW hvW
        · exact (Finset.disjoint_left.1 hWU') hvW hrU
      rw [hempty]; simp

/-- The inductive form of the conflict-avoiding placement: the new vertices of the absorbers placed
so far are collected in `Z`. -/
theorem exists_placement_conf_aux (G : SimpleGraph V) [DecidableRel G.Adj] (C Kb : ℕ)
    (e₀ : ℕ → V) (hinj : ∀ u < C, ∀ v < C, e₀ u = e₀ v → u = v)
    (U' : Finset V) (hU' : U' = (Finset.range C).image e₀)
    (Abs : Finset (Sym2 ℕ) → Finset (Sym2 ℕ)) (F : Finset V)
    (conf : V → V → Prop) [DecidableRel conf]
    (hrefl : ∀ x, conf x x) (hsymm : ∀ x y, conf x y → conf y x) (hU'F : U' ⊆ F)
    (hroom : ∀ Bad : Finset V, Bad.card ≤ Kb → ∀ Q : Finset V, Q.card ≤ 9 →
      ∃ y ∈ commonNbrs G Q, y ∉ F ∧ ∀ z ∈ Bad, ¬ conf y z) :
    ∀ (Hs : Finset (Finset (Sym2 ℕ))) (Z : Finset V),
      Z.card + ∑ H ∈ Hs, (supp (Abs H)).card ≤ Kb →
      (∀ H ∈ Hs, ∀ v ∈ supp H, v < C) → (∀ H ∈ Hs, SparseAbsorber 9 C H (Abs H)) →
      ∃ B W, PlacementC G C e₀ U' Hs Abs F Z conf B W := by
  classical
  intro Hs
  induction Hs using Finset.induction_on with
  | empty =>
    intro Z _ _ _
    exact ⟨fun _ => ∅, fun _ => ∅,
      ⟨by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp,
        by simp⟩⟩
  | insert H₀ Hs hH₀ ih =>
    intro Z hbud hsupp hSA
    have hmemins : ∀ H ∈ Hs, H ∈ insert H₀ Hs := fun H hH => Finset.mem_insert_of_mem hH
    have hsum : ∑ H ∈ insert H₀ Hs, (supp (Abs H)).card
        = (supp (Abs H₀)).card + ∑ H ∈ Hs, (supp (Abs H)).card :=
      Finset.sum_insert hH₀
    -- place `H₀`
    obtain ⟨B₀, W₀, hB₀sub, hB₀abs, hB₀card, hW₀F, hW₀card, hB₀meets, hB₀in, hB₀Z, hB₀conf,
      hB₀root⟩ :=
      exists_place_one_conf G C Kb e₀ hinj U' hU'
        (hsupp H₀ (Finset.mem_insert_self _ _)) (hSA H₀ (Finset.mem_insert_self _ _))
        F Z conf hrefl hsymm hU'F (by omega) hroom
    -- place the rest, with the new vertices of `H₀` added to `Z`
    obtain ⟨B, W, hP⟩ := ih (Z ∪ W₀) (by
      have h1 : (Z ∪ W₀).card ≤ Z.card + W₀.card := Finset.card_union_le _ _
      omega)
      (fun H hH => hsupp H (hmemins H hH)) (fun H hH => hSA H (hmemins H hH))
    have hneH : ∀ H ∈ Hs, H ≠ H₀ := by
      intro H hH h
      subst h
      exact hH₀ hH
    have hBupd : ∀ H ∈ Hs, Function.update B H₀ B₀ H = B H := fun H hH =>
      Function.update_of_ne (hneH H hH) _ _
    have hWupd : ∀ H ∈ Hs, Function.update W H₀ W₀ H = W H := fun H hH =>
      Function.update_of_ne (hneH H hH) _ _
    -- the new vertices of the later absorbers avoid the conflicts of `W₀`
    have hlaterW₀ : ∀ H ∈ Hs, ∀ v ∈ W H, ∀ w ∈ W₀, ¬ conf v w := fun H hH v hv w hw =>
      hP.fresh_confZ H hH v hv w (Finset.mem_union_right _ hw)
    refine ⟨Function.update B H₀ B₀, Function.update W H₀ W₀,
      ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
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
      · rw [Function.update_self]; exact hW₀card
      · rw [hWupd H hH']; exact hP.fresh_card H hH'
    · intro H hH
      rcases Finset.mem_insert.1 hH with rfl | hH'
      · rw [Function.update_self, Function.update_self]; exact hB₀meets
      · rw [hBupd H hH', hWupd H hH']; exact hP.edge_meets H hH'
    · intro H hH
      rcases Finset.mem_insert.1 hH with rfl | hH'
      · rw [Function.update_self, Function.update_self]; exact hB₀in
      · rw [hBupd H hH', hWupd H hH']; exact hP.edge_in H hH'
    · intro H hH
      rcases Finset.mem_insert.1 hH with rfl | hH'
      · rw [Function.update_self]; exact hW₀F
      · rw [hWupd H hH']; exact hP.fresh_notF H hH'
    · intro H hH
      rcases Finset.mem_insert.1 hH with rfl | hH'
      · rw [Function.update_self]; exact hB₀Z
      · rw [hWupd H hH']
        exact fun v hv z hz => hP.fresh_confZ H hH' v hv z (Finset.mem_union_left _ hz)
    · intro H₁ h₁ v hv H₂ h₂ w hw hne
      rcases Finset.mem_insert.1 h₁ with rfl | h₁' <;>
        rcases Finset.mem_insert.1 h₂ with rfl | h₂'
      · rw [Function.update_self] at hv hw; exact hB₀conf v hv w hw hne
      · rw [Function.update_self] at hv
        rw [hWupd H₂ h₂'] at hw
        exact fun hc => hlaterW₀ H₂ h₂' w hw v hv (hsymm _ _ hc)
      · rw [Function.update_self] at hw
        rw [hWupd H₁ h₁'] at hv
        exact hlaterW₀ H₁ h₁' v hv w hw
      · rw [hWupd H₁ h₁'] at hv
        rw [hWupd H₂ h₂'] at hw
        exact hP.fresh_conf H₁ h₁' v hv H₂ h₂' w hw hne
    · intro H₁ h₁ H₂ h₂ hne
      rcases Finset.mem_insert.1 h₁ with rfl | h₁' <;>
        rcases Finset.mem_insert.1 h₂ with rfl | h₂'
      · exact absurd rfl hne
      · rw [Function.update_self, hWupd H₂ h₂']
        exact Finset.disjoint_left.2 fun v hv hv' =>
          hlaterW₀ H₂ h₂' v hv' v hv (hrefl v)
      · rw [Function.update_self, hWupd H₁ h₁']
        exact Finset.disjoint_left.2 fun v hv hv' =>
          hlaterW₀ H₁ h₁' v hv v hv' (hrefl v)
      · rw [hWupd H₁ h₁', hWupd H₂ h₂']
        exact hP.pairwise H₁ h₁' H₂ h₂' hne
    · intro H hH
      rcases Finset.mem_insert.1 hH with rfl | hH'
      · rw [Function.update_self]; exact hB₀root
      · rw [hBupd H hH']; exact hP.root_deg H hH'

/-- **Placing the whole family, avoiding a conflict relation.**  Every finite family of
`9`-degenerate abstract absorbers rooted below `C` can be placed inside `G` so that all the new
vertices avoid `F` and are pairwise conflict-free, and conflict-free with `Z ⊇ U'`, as soon as any
nine vertices have a common neighbour outside `F` avoiding the conflicts of any `Kb` vertices. -/
theorem exists_placement_conf (G : SimpleGraph V) [DecidableRel G.Adj] (C Kb : ℕ)
    (e₀ : ℕ → V) (hinj : ∀ u < C, ∀ v < C, e₀ u = e₀ v → u = v)
    (U' : Finset V) (hU' : U' = (Finset.range C).image e₀)
    (Hs : Finset (Finset (Sym2 ℕ))) (Abs : Finset (Sym2 ℕ) → Finset (Sym2 ℕ))
    (F Z : Finset V) (conf : V → V → Prop) [DecidableRel conf]
    (hrefl : ∀ x, conf x x) (hsymm : ∀ x y, conf x y → conf y x) (hU'F : U' ⊆ F)
    (hbud : Z.card + ∑ H ∈ Hs, (supp (Abs H)).card ≤ Kb)
    (hsub : ∀ H ∈ Hs, ∀ v ∈ supp H, v < C)
    (hSA : ∀ H ∈ Hs, SparseAbsorber 9 C H (Abs H))
    (hroom : ∀ Bad : Finset V, Bad.card ≤ Kb → ∀ Q : Finset V, Q.card ≤ 9 →
      ∃ y ∈ commonNbrs G Q, y ∉ F ∧ ∀ z ∈ Bad, ¬ conf y z) :
    ∃ B W, PlacementC G C e₀ U' Hs Abs F Z conf B W :=
  exists_placement_conf_aux G C Kb e₀ hinj U' hU' Abs F conf hrefl hsymm hU'F hroom Hs Z hbud
    hsub hSA

end BKLO
