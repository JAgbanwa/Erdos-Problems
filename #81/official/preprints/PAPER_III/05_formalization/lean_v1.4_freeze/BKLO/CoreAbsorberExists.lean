/-
# Reserving the bounded-core absorbers inside a dense host (BKLO §8.1 + §5).

This file proves `BKLO.CoreAbsorberExistence`: inside a large dense host `E ⊆ cliqueEdges S`, and
avoiding an already reserved edge set `R₁` of maximum degree at most `γ|S|/2`, one can reserve a
*bounded* edge set `R₂ ⊆ E \ R₁` which contains an absorber for **every** triangle-divisible edge
set inside a core `U ⊆ S` of bounded size, in such a way that removing that absorber leaves a
triangle-decomposable remainder.

The two ingredients are already available in the project:

* `BKLO.sparseAbsorberExistence_nine` — every loopless triangle-divisible edge set rooted below `C`
  has a `9`-degenerate absorber on fresh vertices (BKLO §8.1);
* `BKLO.exists_placement` — such a family of abstract absorbers embeds edge-disjointly into a host
  graph with large common neighbourhoods (BKLO §5).

The work here is the bookkeeping: passing from the edge-set model over an arbitrary vertex type to
the `SimpleGraph` on the subtype `↥S` (`BKLO.hostGraph`), enumerating the core, and transporting
the placed absorbers back (`BKLO.IsAbsorber.mapInj`).
-/
import BKLO.HostGraph
import BKLO.Placement
import BKLO.AbsorberExists
import BKLO.BoundedLeftover

open Finset

namespace BKLO

variable {V : Type*} [DecidableEq V]

/-! ### Enumerating the core -/

omit [DecidableEq V] in
/-- An injective enumeration `ℕ → ↥S` of a `C`-element subset `Uc ⊆ S`. -/
theorem exists_root_enum {S U : Finset V} {C : ℕ} (hUS : U ⊆ S) (hcard : U.card = C)
    (hne : S.Nonempty) :
    ∃ e₀ : ℕ → {x // x ∈ S}, (∀ u < C, ∀ v < C, e₀ u = e₀ v → u = v) ∧
      ∀ x : V, x ∈ U ↔ ∃ i < C, ((e₀ i : {x // x ∈ S}) : V) = x := by
  classical
  subst hcard
  refine ⟨fun i => if h : i < U.card then
      ⟨((U.equivFin.symm ⟨i, h⟩ : {x // x ∈ U}) : V), hUS (Finset.coe_mem _)⟩
    else ⟨hne.choose, hne.choose_spec⟩, ?_, ?_⟩
  · intro u hu v hv heq
    dsimp only at heq
    rw [dif_pos hu, dif_pos hv] at heq
    have : (U.equivFin.symm ⟨u, hu⟩ : {x // x ∈ U}) = U.equivFin.symm ⟨v, hv⟩ :=
      Subtype.ext (by simpa using congrArg Subtype.val heq)
    have := U.equivFin.symm.injective this
    exact congrArg Fin.val this
  · intro x
    constructor
    · intro hx
      refine ⟨(U.equivFin ⟨x, hx⟩ : Fin U.card).1, (U.equivFin ⟨x, hx⟩).2, ?_⟩
      dsimp only
      have : (⟨(U.equivFin ⟨x, hx⟩ : Fin U.card).1, (U.equivFin ⟨x, hx⟩).2⟩ : Fin U.card)
          = U.equivFin ⟨x, hx⟩ := rfl
      simp only [dif_pos (U.equivFin ⟨x, hx⟩).2, this, Equiv.symm_apply_apply]
    · rintro ⟨i, hi, rfl⟩
      dsimp only
      rw [dif_pos hi]
      exact Finset.coe_mem _

/-! ### The reserved structure -/

/-- **Interface B, proved.**  The bounded-core absorbers can be reserved inside a large dense
host, avoiding an already reserved edge set of maximum degree at most `γ|S|/2`. -/
theorem coreAbsorberExistence_holds : CoreAbsorberExistence := by
  classical
  intro C γ hγ
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
  -- an abstract `9`-degenerate absorber for each of them
  have hex : ∀ H ∈ Hs, ∃ A, SparseAbsorber 9 C H A := by
    intro H hH
    refine sparseAbsorberExistence_nine C H ?_ ?_ (hHsmem H hH).2
    · intro e he
      exact (mem_cliqueEdgesV.1 ((hHsmem H hH).1 he)).2
    · intro v hv
      exact hrootlt H hH v hv
  choose! Abs hAbs using hex
  -- the two constants: the room needed for the placement, and the size of the reserved structure
  obtain ⟨K, hKdef⟩ : ∃ K : ℕ, K = C + 2 * (∑ H ∈ Hs, (supp (Abs H)).card) := ⟨_, rfl⟩
  obtain ⟨M, hMdef⟩ : ∃ M : ℕ, M = ∑ H ∈ Hs, (Abs H).card := ⟨_, rfl⟩
  obtain ⟨m, hm⟩ := exists_nat_ge (2 * (M : ℝ) / γ)
  refine ⟨max (10 * K + 10) (max m C), ?_⟩
  intro V _ E R₁ S U hn hES hUS hUC hdeg hR₁E hR₁deg
  have hnK : 10 * K + 10 ≤ S.card := le_trans (le_max_left _ _) hn
  have hnm : m ≤ S.card := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hnC : C ≤ S.card := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  have hSne : S.Nonempty := Finset.card_pos.1 (by omega)
  set T : Finset (Sym2 V) := E \ R₁ with hTdef
  have hTE : T ⊆ E := Finset.sdiff_subset
  have hTS : T ⊆ cliqueEdges S := fun e he => hES (hTE he)
  -- the host graph has minimum degree at least `(9/10)|S|`
  have hTdeg : ∀ v ∈ S, 9 * S.card ≤ 10 * edeg T v := by
    intro v hv
    have hsplit : edeg E v ≤ edeg T v + edeg R₁ v := by
      have hsub : E.filter (fun e => v ∈ e)
          ⊆ T.filter (fun e => v ∈ e) ∪ R₁.filter (fun e => v ∈ e) := by
        intro e he
        obtain ⟨heE, hve⟩ := Finset.mem_filter.1 he
        by_cases hR : e ∈ R₁
        · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hR, hve⟩)
        · exact Finset.mem_union_left _
            (Finset.mem_filter.2 ⟨Finset.mem_sdiff.2 ⟨heE, hR⟩, hve⟩)
      calc edeg E v ≤ (T.filter (fun e => v ∈ e) ∪ R₁.filter (fun e => v ∈ e)).card :=
            Finset.card_le_card hsub
        _ ≤ edeg T v + edeg R₁ v := Finset.card_union_le _ _
    have h1 := hdeg v hv
    have h2 := hR₁deg v
    have h3 : (edeg E v : ℝ) ≤ (edeg T v : ℝ) + (edeg R₁ v : ℝ) := by exact_mod_cast hsplit
    have h4 : (9 : ℝ) * (S.card : ℝ) ≤ 10 * (edeg T v : ℝ) := by nlinarith
    exact_mod_cast h4
  -- enumerate a `C`-element core containing `U`
  obtain ⟨Uc, hUUc, hUcS, hUccard⟩ :=
    Finset.exists_subsuperset_card_eq hUS hUC hnC
  obtain ⟨e₀, he₀inj, he₀mem⟩ := exists_root_enum hUcS hUccard hSne
  set U' : Finset {x // x ∈ S} := (Finset.range C).image e₀ with hU'def
  -- place the whole family
  obtain ⟨B, W, hP⟩ :=
    exists_placement (hostGraph T S) C e₀ he₀inj U' hU'def Hs Abs hrootlt
      (fun H hH => hAbs H hH)
      (fun Q hQ => by
        have hroom := card_commonNbrs_host (T := T) (S := S) hTS hSne hTdeg Q hQ
        omega)
  -- the reserved structure
  set val : {x // x ∈ S} → V := fun a => (a : V) with hvaldef
  have hvalinj : Function.Injective val := Subtype.val_injective
  set R₂ : Finset (Sym2 V) := Hs.biUnion (fun H => (B H).image (Sym2.map val)) with hR₂def
  -- pairwise edge-disjointness of the placed absorbers
  have hBdisj : ∀ H₁ ∈ Hs, ∀ H₂ ∈ Hs, H₁ ≠ H₂ → Disjoint (B H₁) (B H₂) := by
    intro H₁ h₁ H₂ h₂ hne
    refine Finset.disjoint_left.2 fun f hf1 hf2 => ?_
    obtain ⟨v, hvf, hvW⟩ := hP.edge_meets H₁ h₁ f hf1
    rcases hP.edge_in H₂ h₂ f hf2 v hvf with hU | hW2
    · exact (Finset.disjoint_left.1 (hP.fresh_disj H₁ h₁) hvW) hU
    · exact (Finset.disjoint_left.1 (hP.pairwise H₁ h₁ H₂ h₂ hne) hvW) hW2
  have himgdisj : ∀ H₁ ∈ Hs, ∀ H₂ ∈ Hs, H₁ ≠ H₂ →
      Disjoint ((B H₁).image (Sym2.map val)) ((B H₂).image (Sym2.map val)) := by
    intro H₁ h₁ H₂ h₂ hne
    exact (Finset.disjoint_image (Sym2.map.injective hvalinj)).2 (hBdisj H₁ h₁ H₂ h₂ hne)
  have hBdec : ∀ H ∈ Hs, TriDecomp ((B H).image (Sym2.map val)) := by
    intro H hH
    exact ((hP.absorber H hH).2.1).mapInj hvalinj
  refine ⟨R₂, ?_, ?_, ?_⟩
  · -- `R₂ ⊆ E \ R₁`
    intro e he
    obtain ⟨H, hH, he⟩ := Finset.mem_biUnion.1 he
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 he
    exact hostGraph_edge_mem (hP.sub H hH hf)
  · -- the degree bound
    intro v
    have hcard : R₂.card ≤ M := by
      rw [hMdef, hR₂def]
      refine le_trans Finset.card_biUnion_le (Finset.sum_le_sum fun H hH => ?_)
      exact le_trans Finset.card_image_le (hP.card_le H hH)
    have h1 : edeg R₂ v ≤ R₂.card := Finset.card_filter_le _ _
    have h2 : (M : ℝ) ≤ γ * (S.card : ℝ) / 2 := by
      have hmn : (m : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast hnm
      have := le_trans hm hmn
      rw [div_le_iff₀ hγ] at this
      linarith
    have h3 : (edeg R₂ v : ℝ) ≤ (M : ℝ) := by exact_mod_cast le_trans h1 hcard
    linarith
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

end BKLO
