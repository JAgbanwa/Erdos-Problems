/-
# The bounded-core absorber, placed avoiding a conflict relation

`BKLO.coreAbsorberExistence_bounded` (`BKLO/Section11CellsBuild.lean`) reserves, inside a dense
host, a bounded structure `R₂` that absorbs every triangle-divisible edge set inside a bounded core
`U`.  For the §11 cells route the *location* of `R₂` matters: its non-core vertices have to be
spread over the bottom cells of the vortex — one per cell, and in cells that carry no reserved edge
to the core yet — so that the reservation is spread at the scale of a single cell.

This file proves the corresponding statement, `BKLO.coreAbsorberExistence_conf`, on top of the
conflict-avoiding placement `BKLO.exists_placement_conf`.  The caller supplies a reflexive
symmetric conflict relation and only has to know that any nine vertices of the host have a common
neighbour outside the forbidden set which is in conflict with none of a bounded number of
prescribed vertices.  The reserved structure then satisfies

* `R₂ ⊆ cliqueEdges (U ∪ Fr)` with the new vertices `Fr` pairwise conflict-free, conflict-free with
  the core and with the prescribed set `Z`, and
* `degTo R₂ x U ≤ 9` for every vertex `x` — the degeneracy of the abstract absorbers of §8.1, which
  is what bounds the reserved degree *into the core cell itself*.
-/
import BKLO.CoreAbsorberExists
import BKLO.PlacementConf

open Finset

namespace BKLO

/-- **The bounded-core absorber, placed avoiding a conflict relation.**

For every core size `C` there are constants `M` (the size of the reserved structure) and `Kt` (the
number of new vertices it uses) such that: in any host `T ⊆ cliqueEdges S` with a `C`-element core
`U ⊆ S ∩ F`, and for any reflexive symmetric conflict relation for which any nine vertices of `S`
have a common neighbour outside `F` avoiding the conflicts of any `Z.card + Kt` prescribed
vertices, one can reserve `R₂ ⊆ T` of size at most `M` which is a core absorbing structure for `U`,
spans `U` together with at most `Kt` new vertices that are pairwise conflict-free and
conflict-free with `U` and `Z`, and sends at most `9` edges from any vertex into the core. -/
theorem coreAbsorberExistence_conf (C : ℕ) : ∃ M Kt : ℕ,
    ∀ {V : Type} [DecidableEq V] (T : Finset (Sym2 V)) (S U F Z : Finset V)
      (conf : V → V → Prop),
      T ⊆ cliqueEdges S → U ⊆ S → U.card = C → S.Nonempty → U ⊆ F → Z ⊆ S →
      (∀ x, conf x x) → (∀ x y, conf x y → conf y x) →
      (∀ Q : Finset V, Q ⊆ S → Q.card ≤ 9 → ∀ Bad : Finset V, Bad.card ≤ Z.card + Kt →
        ∃ y ∈ S, y ∉ F ∧ (∀ z ∈ Bad, ¬ conf y z) ∧ ∀ q ∈ Q, s(q, y) ∈ T) →
      ∃ (R₂ : Finset (Sym2 V)) (Fr : Finset V),
        R₂ ⊆ T ∧ R₂.card ≤ M ∧ CoreAbsorbers U R₂ ∧
        R₂ ⊆ cliqueEdges (U ∪ Fr) ∧ Fr ⊆ S ∧ Fr.card ≤ Kt ∧
        (∀ v ∈ Fr, v ∉ F) ∧
        (∀ v ∈ Fr, ∀ z ∈ Z, ¬ conf v z) ∧
        (∀ v ∈ Fr, ∀ z ∈ U, ¬ conf v z) ∧
        (∀ v ∈ Fr, ∀ w ∈ Fr, v ≠ w → ¬ conf v w) ∧
        (∀ x : V, degTo R₂ x U ≤ 9) := by
  classical

  -- the (finitely many) triangle-divisible edge sets on the roots `{0, …, C-1}`
  set Hs : Finset (Finset (Sym2 ℕ)) :=
    (cliqueEdges (Finset.range C)).powerset.filter (fun H => TriDivisible H) with hHsdef
  have hHsmem : ∀ H ∈ Hs, H ⊆ cliqueEdges (Finset.range C) ∧ TriDivisible H := by
    intro H hH
    obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hH
    exact ⟨Finset.mem_powerset.1 h1, h2⟩
  have hrootlt : ∀ H ∈ Hs, ∀ v ∈ supp H, v < C := by
    intro H hH v hv
    obtain ⟨e, he, hve⟩ := mem_supp.1 hv
    exact Finset.mem_range.1 ((mem_cliqueEdgesV.1 ((hHsmem H hH).1 he)).1 v hve)
  have hex : ∀ H ∈ Hs, ∃ A, SparseAbsorber 9 C H A := by
    intro H hH
    refine sparseAbsorberExistence_nine C H ?_ ?_ (hHsmem H hH).2
    · intro e he
      exact (mem_cliqueEdgesV.1 ((hHsmem H hH).1 he)).2
    · intro v hv
      exact hrootlt H hH v hv
  choose! Abs hAbs using hex
  set M : ℕ := ∑ H ∈ Hs, (Abs H).card with hMdef
  set Ktot : ℕ := ∑ H ∈ Hs, (supp (Abs H)).card with hKtotdef
  refine ⟨M, C + Ktot, ?_⟩
  intro V _ T S U F Z conf hTS hUS hUC hSne hUF hZS hrefl hsymm hroom
  have hloopT : ∀ e ∈ T, ¬ e.IsDiag := fun e he => (mem_cliqueEdgesV.1 (hTS he)).2

  obtain ⟨e₀, he₀inj, he₀mem⟩ := exists_root_enum hUS hUC hSne
  set U' : Finset {x // x ∈ S} := (Finset.range C).image e₀ with hU'def
  set val : {x // x ∈ S} → V := fun a => (a : V) with hvaldef
  have hvalinj : Function.Injective val := Subtype.val_injective
  -- the image of `U'` is `U`
  have hU'val : ∀ a : {x // x ∈ S}, a ∈ U' ↔ val a ∈ U := by
    intro a
    constructor
    · intro ha
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 ha
      exact (he₀mem (val (e₀ i))).2 ⟨i, Finset.mem_range.1 hi, rfl⟩
    · intro ha
      obtain ⟨i, hi, hval⟩ := (he₀mem (val a)).1 ha
      have : e₀ i = a := hvalinj hval
      exact this ▸ Finset.mem_image_of_mem e₀ (Finset.mem_range.2 hi)
  -- the conflict relation, the forbidden set and the prescribed set, on the host subtype
  set conf' : {x // x ∈ S} → {x // x ∈ S} → Prop := fun a b => conf (val a) (val b) with hconf'def
  have hconf'refl : ∀ a, conf' a a := fun a => hrefl _
  have hconf'symm : ∀ a b, conf' a b → conf' b a := fun a b h => hsymm _ _ h
  set F' : Finset {x // x ∈ S} := F.subtype (· ∈ S) with hF'def
  have hF'mem : ∀ a : {x // x ∈ S}, a ∈ F' ↔ val a ∈ F := by
    intro a; rw [hF'def, hvaldef]; simp [Finset.mem_subtype]
  set Z' : Finset {x // x ∈ S} := (Z ∪ U).subtype (· ∈ S) with hZ'def
  have hZ'mem : ∀ a : {x // x ∈ S}, a ∈ Z' ↔ val a ∈ Z ∪ U := by
    intro a; rw [hZ'def, hvaldef]; simp [Finset.mem_subtype]
  have hU'F' : U' ⊆ F' := fun a ha => (hF'mem a).2 (hUF ((hU'val a).1 ha))
  have hZ'card : Z'.card ≤ Z.card + C := by
    have h1 : Z'.card ≤ (Z ∪ U).card := by
      rw [hZ'def]
      rw [Finset.card_subtype]; exact Finset.card_filter_le _ _
    have h2 : (Z ∪ U).card ≤ Z.card + U.card := Finset.card_union_le _ _
    omega
  -- the room hypothesis, transported to the host subtype
  have hroom' : ∀ Bad : Finset {x // x ∈ S}, Bad.card ≤ Z.card + (C + Ktot) →
      ∀ Q : Finset {x // x ∈ S}, Q.card ≤ 9 →
      ∃ y ∈ commonNbrs (hostGraph T S) Q, y ∉ F' ∧ ∀ z ∈ Bad, ¬ conf' y z := by
    intro Bad hBad Q hQ
    have hQcard : (Q.image val).card ≤ 9 := le_trans Finset.card_image_le hQ
    have hQS : Q.image val ⊆ S := by
      intro x hx
      obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hx
      exact a.2
    have hBadcard : (Bad.image val).card ≤ Z.card + (C + Ktot) :=
      le_trans Finset.card_image_le hBad
    obtain ⟨y, hyS, hyF, hyBad, hyadj⟩ := hroom (Q.image val) hQS hQcard (Bad.image val) hBadcard
    refine ⟨⟨y, hyS⟩, ?_, ?_, ?_⟩
    · simp only [commonNbrs, Finset.mem_filter, Finset.mem_univ, true_and]
      intro a ha
      have hedge : s((a : V), y) ∈ T := hyadj (a : V) (Finset.mem_image_of_mem val ha)
      refine ⟨?_, hedge⟩
      intro hcon
      refine hloopT _ hedge ?_
      have : (a : V) = y := congrArg val hcon
      simp [Sym2.isDiag_iff_proj_eq, this]
    · exact fun hc => hyF ((hF'mem _).1 hc)
    · exact fun z hz => hyBad (val z) (Finset.mem_image_of_mem val hz)
  -- place the whole family
  obtain ⟨B, W, hP⟩ :=
    exists_placement_conf (hostGraph T S) C (Z.card + (C + Ktot)) e₀ he₀inj U' hU'def Hs Abs
      F' Z' conf' hconf'refl hconf'symm hU'F' (by
        have : ∑ H ∈ Hs, (supp (Abs H)).card = Ktot := hKtotdef.symm
        omega)
      hrootlt (fun H hH => hAbs H hH) hroom'
  have hfreshU' : ∀ H ∈ Hs, Disjoint (W H) U' :=
    fun H hH => Finset.disjoint_left.2 fun a ha haU => hP.fresh_notF H hH a ha (hU'F' haU)

  set R₂ : Finset (Sym2 V) := Hs.biUnion (fun H => (B H).image (Sym2.map val)) with hR₂def
  set Fr : Finset V := Hs.biUnion (fun H => (W H).image val) with hFrdef
  set Uc : Finset V := U with hUcdef
  have hUUc : U ⊆ Uc := Finset.Subset.refl _
  -- pairwise edge-disjointness of the placed absorbers
  have hBdisj : ∀ H₁ ∈ Hs, ∀ H₂ ∈ Hs, H₁ ≠ H₂ → Disjoint (B H₁) (B H₂) := by
    intro H₁ h₁ H₂ h₂ hne
    refine Finset.disjoint_left.2 fun f hf1 hf2 => ?_
    obtain ⟨v, hvf, hvW⟩ := hP.edge_meets H₁ h₁ f hf1
    rcases hP.edge_in H₂ h₂ f hf2 v hvf with hU | hW2
    · exact (Finset.disjoint_left.1 (hfreshU' H₁ h₁) hvW) hU
    · exact (Finset.disjoint_left.1 (hP.pairwise H₁ h₁ H₂ h₂ hne) hvW) hW2
  have himgdisj : ∀ H₁ ∈ Hs, ∀ H₂ ∈ Hs, H₁ ≠ H₂ →
      Disjoint ((B H₁).image (Sym2.map val)) ((B H₂).image (Sym2.map val)) := by
    intro H₁ h₁ H₂ h₂ hne
    exact (Finset.disjoint_image (Sym2.map.injective hvalinj)).2 (hBdisj H₁ h₁ H₂ h₂ hne)
  have hBdec : ∀ H ∈ Hs, TriDecomp ((B H).image (Sym2.map val)) := by
    intro H hH
    exact ((hP.absorber H hH).2.1).mapInj hvalinj
  -- a fresh vertex of the placement is not in the core
  have hWnotU : ∀ H ∈ Hs, ∀ a ∈ W H, val a ∉ U := by
    intro H hH a ha hcon
    exact (Finset.disjoint_left.1 (hfreshU' H hH)) ha ((hU'val a).2 hcon)
  have hFrmem : ∀ v ∈ Fr, ∃ H ∈ Hs, ∃ a ∈ W H, val a = v := by
    intro v hv
    obtain ⟨H, hH, hv'⟩ := Finset.mem_biUnion.1 hv
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hv'
    exact ⟨H, hH, a, ha, rfl⟩
  have hFrS : Fr ⊆ S := by
    intro v hv
    obtain ⟨H, hH, a, ha, rfl⟩ := hFrmem v hv
    exact a.2
  have hFrnotF : ∀ v ∈ Fr, v ∉ F := by
    intro v hv
    obtain ⟨H, hH, a, ha, rfl⟩ := hFrmem v hv
    exact fun hc => hP.fresh_notF H hH a ha ((hF'mem a).2 hc)
  refine ⟨R₂, Fr, ?_, ?_, ?_, ?_, hFrS, ?_, hFrnotF, ?_, ?_, ?_, ?_⟩

  · -- `R₂ ⊆ T`
    intro e he
    obtain ⟨H, hH, he'⟩ := Finset.mem_biUnion.1 he
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 he'
    exact hostGraph_edge_mem (hP.sub H hH hg)
  · -- the size bound
    rw [hMdef, hR₂def]
    refine le_trans Finset.card_biUnion_le (Finset.sum_le_sum fun H hH => ?_)
    exact le_trans Finset.card_image_le (hP.card_le H hH)
  · -- the core absorbing property
    constructor
    intro Y hYU hYdiv
    -- the `ℕ`-copy of `Y`
    have hinv : ∀ x ∈ Uc, ∃ i : ℕ, i < C ∧ ((e₀ i : {x // x ∈ S}) : V) = x :=
      fun x hx => (he₀mem x).1 hx
    choose! ρ hρlt hρeq using hinv
    have hρ : ∀ x ∈ Uc, ρ x < C ∧ ((e₀ (ρ x) : {x // x ∈ S}) : V) = x :=
      fun x hx => ⟨hρlt x hx, hρeq x hx⟩
    have hYUc : Y ⊆ cliqueEdges Uc := fun e he => cliqueEdges_mono hUUc (hYU he)
    have hYvert : ∀ e ∈ Y, ∀ x ∈ e, x ∈ Uc := fun e he x hx =>
      (mem_cliqueEdgesV.1 (hYUc he)).1 x hx
    set f : ℕ → V := fun i => ((e₀ i : {x // x ∈ S}) : V) with hfdef
    have hfρ : ∀ x ∈ Uc, f (ρ x) = x := fun x hx => (hρ x hx).2
    set HY : Finset (Sym2 ℕ) := Y.image (Sym2.map ρ) with hHYdef
    -- `HY` maps back onto `Y`
    have hHYmap : HY.image (Sym2.map f) = Y := by
      rw [hHYdef, Finset.image_image]
      refine Finset.image_congr ?_ |>.trans (Finset.image_id) |>.trans rfl
      intro e he
      induction e using Sym2.ind with
      | _ x y =>
        have hx := hYvert _ he x (by simp)
        have hy := hYvert _ he y (by simp)
        simp [Function.comp, hfρ x hx, hfρ y hy]
    have hfinj : ∀ u ∈ supp HY, ∀ v ∈ supp HY, f u = f v → u = v := by
      intro u hu v hv huv
      obtain ⟨e, he, hue⟩ := mem_supp.1 hu
      obtain ⟨e', he', hve⟩ := mem_supp.1 hv
      have hbound : ∀ w ∈ supp HY, w < C := by
        intro w hw
        obtain ⟨g, hg, hwg⟩ := mem_supp.1 hw
        obtain ⟨g', hg', rfl⟩ := Finset.mem_image.1 hg
        obtain ⟨z, hz, rfl⟩ := Sym2.mem_map.1 hwg
        exact (hρ z (hYvert _ hg' z hz)).1
      have hu' := hbound u hu
      have hv' := hbound v hv
      exact he₀inj u hu' v hv' (Subtype.ext huv)
    have hHYsub : HY ⊆ cliqueEdges (Finset.range C) := by
      intro e he
      obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 he
      refine mem_cliqueEdgesV.2 ⟨?_, ?_⟩
      · intro z hz
        obtain ⟨w, hw, rfl⟩ := Sym2.mem_map.1 hz
        exact Finset.mem_range.2 (hρ w (hYvert _ hg w hw)).1
      · intro hdiag
        refine (mem_cliqueEdgesV.1 (hYUc hg)).2 ?_
        induction g using Sym2.ind with
        | _ x y =>
          simp only [Sym2.map_pair_eq, Sym2.isDiag_iff_proj_eq] at hdiag
          have hx := hYvert _ hg x (by simp)
          have hy := hYvert _ hg y (by simp)
          have : x = y := by rw [← hfρ x hx, ← hfρ y hy, hdiag]
          simp [Sym2.isDiag_iff_proj_eq, this]
    have hHYdiv : TriDivisible HY := by
      refine triDivisible_of_image (f := f) hfinj ?_
      rw [hHYmap]
      exact hYdiv
    have hHYmemHs : HY ∈ Hs := by
      rw [hHsdef]
      exact Finset.mem_filter.2 ⟨Finset.mem_powerset.2 hHYsub, hHYdiv⟩
    refine ⟨(B HY).image (Sym2.map val), ?_, ?_, ?_⟩
    · rw [hR₂def]
      exact Finset.subset_biUnion_of_mem (fun H => (B H).image (Sym2.map val)) hHYmemHs
    · -- the placed absorber absorbs `Y`
      have habs := (hP.absorber HY hHYmemHs).mapInj hvalinj
      have himg : ((HY.image (Sym2.map e₀)).image (Sym2.map val)) = Y := by
        rw [Finset.image_image, ← hHYmap]
        refine Finset.image_congr ?_
        intro e he
        simp [Function.comp, Sym2.map_map, hfdef, hvaldef]
      rwa [himg] at habs
    · -- the rest of the reserved structure is decomposable
      have hsplit : R₂ \ (B HY).image (Sym2.map val)
          = (Hs.erase HY).biUnion (fun H => (B H).image (Sym2.map val)) := by
        ext e
        simp only [hR₂def, Finset.mem_sdiff, Finset.mem_biUnion, Finset.mem_erase]
        constructor
        · rintro ⟨⟨H, hH, heH⟩, hnot⟩
          refine ⟨H, ⟨?_, hH⟩, heH⟩
          rintro rfl
          exact hnot heH
        · rintro ⟨H, ⟨hne, hH⟩, heH⟩
          refine ⟨⟨H, hH, heH⟩, fun hcon => ?_⟩
          exact (Finset.disjoint_left.1 (himgdisj H hH HY hHYmemHs hne) heH) hcon
      rw [hsplit]
      refine TriDecomp.biUnion (fun H hH => hBdec H (Finset.mem_of_mem_erase hH)) ?_
      intro H₁ h₁ H₂ h₂ hne
      exact himgdisj H₁ (Finset.mem_of_mem_erase h₁) H₂ (Finset.mem_of_mem_erase h₂) hne

  · -- `R₂` lives on the core together with the placed vertices
    intro e he
    obtain ⟨H, hH, he'⟩ := Finset.mem_biUnion.1 he
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 he'
    have heT : Sym2.map val g ∈ T := hostGraph_edge_mem (hP.sub H hH hg)
    refine mem_cliqueEdgesV.2 ⟨?_, (mem_cliqueEdgesV.1 (hTS heT)).2⟩
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Sym2.mem_map.1 hx
    rcases hP.edge_in H hH g hg a ha with hU | hW
    · exact Finset.mem_union_left _ ((hU'val a).1 hU)
    · exact Finset.mem_union_right _
        (Finset.mem_biUnion.2 ⟨H, hH, Finset.mem_image_of_mem val hW⟩)
  · -- the number of new vertices
    refine le_trans Finset.card_biUnion_le ?_
    have : ∑ H ∈ Hs, ((W H).image val).card ≤ ∑ H ∈ Hs, (supp (Abs H)).card :=
      Finset.sum_le_sum fun H hH => le_trans Finset.card_image_le (hP.fresh_card H hH)
    omega
  · -- the new vertices are in conflict with nothing prescribed
    intro v hv z hz
    obtain ⟨H, hH, a, ha, rfl⟩ := hFrmem v hv
    exact hP.fresh_confZ H hH a ha ⟨z, hZS hz⟩ ((hZ'mem ⟨z, hZS hz⟩).2 (Finset.mem_union_left _ hz))
  · -- the new vertices are in conflict with no core vertex
    intro v hv z hz
    obtain ⟨H, hH, a, ha, rfl⟩ := hFrmem v hv
    exact hP.fresh_confZ H hH a ha ⟨z, hUS hz⟩ ((hZ'mem ⟨z, hUS hz⟩).2 (Finset.mem_union_right _ hz))
  · -- the new vertices are pairwise conflict-free
    intro v hv w hw hne
    obtain ⟨H₁, h₁, a, ha, rfl⟩ := hFrmem v hv
    obtain ⟨H₂, h₂, b, hb, rfl⟩ := hFrmem w hw
    exact hP.fresh_conf H₁ h₁ a ha H₂ h₂ b hb (fun hc => hne (congrArg val hc))

  · -- at most nine reserved edges from any vertex into the core
    intro x
    show (nbhdIn R₂ x U).card ≤ 9
    -- every edge of `R₂` at `x` comes from a placed absorber
    by_cases hxFr : x ∈ Fr
    · obtain ⟨H₀, hH₀, w, hw, hwx⟩ := hFrmem x hxFr
      have hxU : x ∉ U := hwx ▸ hWnotU H₀ hH₀ w hw
      have hsub : nbhdIn R₂ x U ⊆ (U'.filter (fun r => s(w, r) ∈ B H₀)).image val := by
        intro y hy
        rw [mem_nbhdIn] at hy
        obtain ⟨hyU, hxy⟩ := hy
        obtain ⟨H, hH, he'⟩ := Finset.mem_biUnion.1 hxy
        obtain ⟨g, hg, hgeq⟩ := Finset.mem_image.1 he'
        -- identify the two endpoints of `g`
        have key : ∀ p q : {x // x ∈ S}, s(p, q) ∈ B H → val p = x → val q = y →
            y ∈ (U'.filter (fun r => s(w, r) ∈ B H₀)).image val := by
          intro p q hpq hp hq
          have hqU' : q ∈ U' := (hU'val q).2 (by rw [hq]; exact hyU)
          have hpU' : p ∉ U' := fun hc => hxU (by rw [← hp]; exact (hU'val p).1 hc)
          have hpW : p ∈ W H := by
            rcases hP.edge_in H hH _ hpq p (by simp) with h | h
            · exact absurd h hpU'
            · exact h
          have hpw : p = w := hvalinj (by rw [hp, ← hwx])
          subst hpw
          have hHH : H = H₀ := by
            by_contra hcon
            exact (Finset.disjoint_left.1 (hP.pairwise H hH H₀ hH₀ hcon)) hpW hw
          subst hHH
          exact Finset.mem_image.2 ⟨q, Finset.mem_filter.2 ⟨hqU', hpq⟩, hq⟩
        induction g using Sym2.ind with
        | _ p q =>
          rw [Sym2.map_pair_eq, Sym2.eq_iff] at hgeq
          rcases hgeq with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact key p q hg h1 h2
          · exact key q p (by rw [Sym2.eq_swap]; exact hg) h2 h1
      calc (nbhdIn R₂ x U).card ≤ ((U'.filter (fun r => s(w, r) ∈ B H₀)).image val).card :=
            Finset.card_le_card hsub
        _ ≤ (U'.filter (fun r => s(w, r) ∈ B H₀)).card := Finset.card_image_le
        _ ≤ 9 := hP.root_deg H₀ hH₀ w
    · -- `x` carries no reserved edge into the core at all
      have hempty : nbhdIn R₂ x U = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro y hy
        rw [mem_nbhdIn] at hy
        obtain ⟨hyU, hxy⟩ := hy
        obtain ⟨H, hH, he'⟩ := Finset.mem_biUnion.1 hxy
        obtain ⟨g, hg, hgeq⟩ := Finset.mem_image.1 he'
        obtain ⟨v, hvg, hvW⟩ := hP.edge_meets H hH g hg
        have hval : val v ∈ Sym2.map val g := Sym2.mem_map.2 ⟨v, hvg, rfl⟩
        rw [hgeq] at hval
        rcases Sym2.mem_iff.1 hval with h | h
        · exact hxFr (h ▸ Finset.mem_biUnion.2 ⟨H, hH, Finset.mem_image_of_mem val hvW⟩)
        · exact hWnotU H hH v hvW (h ▸ hyU)
      rw [hempty]; simp

end BKLO
