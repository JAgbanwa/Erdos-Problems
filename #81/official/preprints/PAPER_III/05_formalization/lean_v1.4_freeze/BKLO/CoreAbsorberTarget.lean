/-
# The bounded-core absorber, placed into prescribed targets

`BKLO.coreAbsorberExistence_bounded` (`BKLO/Section11CellsBuild.lean`) reserves, inside a dense
host, a bounded structure `R₂` that absorbs every triangle-divisible edge set inside a bounded core
`U`.  For the §11 cells route the *location* of `R₂` matters: its non-core vertices have to be
spread over the bottom cells of the vortex, one per cell, so that the reservation is spread at the
scale of a single cell.

This file proves the corresponding statement, `BKLO.coreAbsorberExistence_target`.  The caller
supplies a family of pairwise disjoint target sets `Tg j` (in the application: the usable vertices
of the `j`-th bottom cell) and only has to know that each target set contains a common neighbour of
any nine vertices of the host.  The reserved structure then satisfies

* `R₂ ⊆ cliqueEdges (U ∪ Fr)` with `Fr` meeting each target set at most once — so `R₂` sends at
  most one edge into a cell that is not the core, and
* `degTo R₂ x U ≤ 9` for every vertex `x` — the degeneracy of the abstract absorbers of §8.1, which
  is what bounds the reserved degree *into the core cell itself*.
-/
import BKLO.CoreAbsorberExists
import BKLO.PlacementTarget

open Finset

namespace BKLO

/-- **The bounded-core absorber, placed into prescribed targets.**

For every core size `C` there are constants `M` (the size of the reserved structure) and `Kt` (the
number of target sets it needs) such that: in any host `T ⊆ cliqueEdges S` with a `C`-element core
`U ⊆ S` and pairwise disjoint target sets `Tg 0, …, Tg (Kt-1) ⊆ S`, disjoint from `U` and each
containing a common neighbour of any nine vertices of `S`, one can reserve `R₂ ⊆ T` of size at most
`M` which is a core absorbing structure for `U`, uses at most one vertex of each target set, and
sends at most `9` edges from any vertex into the core. -/
theorem coreAbsorberExistence_target (C : ℕ) : ∃ M Kt : ℕ,
    ∀ {V : Type} [DecidableEq V] (T : Finset (Sym2 V)) (S U : Finset V) (Tg : ℕ → Finset V),
      T ⊆ cliqueEdges S → U ⊆ S → U.card = C → S.Nonempty →
      (∀ j, Tg j ⊆ S) → (∀ j, Disjoint (Tg j) U) →
      (∀ i j : ℕ, i ≠ j → Disjoint (Tg i) (Tg j)) →
      (∀ j < Kt, ∀ Q : Finset V, Q ⊆ S → Q.card ≤ 9 → ∃ y ∈ Tg j, ∀ q ∈ Q, s(q, y) ∈ T) →
      ∃ (R₂ : Finset (Sym2 V)) (Fr : Finset V),
        R₂ ⊆ T ∧ R₂.card ≤ M ∧ CoreAbsorbers U R₂ ∧
        R₂ ⊆ cliqueEdges (U ∪ Fr) ∧
        (∀ j, (Fr ∩ Tg j).card ≤ 1) ∧ (∀ v ∈ Fr, ∃ j < Kt, v ∈ Tg j) ∧
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
  -- the index of a target: the `u`-th fresh vertex of the absorber of the `rk H`-th member
  set Umax : ℕ := (Hs.sup (fun H => (supp (Abs H)).sup id)) + 1 with hUmaxdef
  have hUmax0 : 0 < Umax := Nat.succ_pos _
  have hUmax : ∀ H ∈ Hs, ∀ u ∈ supp (Abs H), u < Umax := by
    intro H hH u hu
    have h1 : u ≤ (supp (Abs H)).sup id := Finset.le_sup (f := id) hu
    have h2 : (supp (Abs H)).sup id ≤ Hs.sup (fun H => (supp (Abs H)).sup id) :=
      Finset.le_sup (f := fun H => (supp (Abs H)).sup id) hH
    omega
  set rk : Finset (Sym2 ℕ) → ℕ := fun H =>
    if h : H ∈ Hs then ((Hs.equivFin ⟨H, h⟩ : Fin Hs.card) : ℕ) else 0 with hrkdef
  have hrklt : ∀ H ∈ Hs, rk H < Hs.card := by
    intro H hH
    rw [hrkdef]
    simp only [dif_pos hH]
    exact (Hs.equivFin ⟨H, hH⟩).2
  have hrkinj : ∀ H₁ ∈ Hs, ∀ H₂ ∈ Hs, rk H₁ = rk H₂ → H₁ = H₂ := by
    intro H₁ h₁ H₂ h₂ heq
    rw [hrkdef] at heq
    simp only [dif_pos h₁, dif_pos h₂] at heq
    have : (Hs.equivFin ⟨H₁, h₁⟩ : Fin Hs.card) = Hs.equivFin ⟨H₂, h₂⟩ := Fin.ext heq
    have := Hs.equivFin.injective this
    exact congrArg Subtype.val this
  set idx : Finset (Sym2 ℕ) → ℕ → ℕ := fun H u => u + rk H * Umax with hidxdef
  set M : ℕ := ∑ H ∈ Hs, (Abs H).card with hMdef
  set Kt : ℕ := Hs.card * Umax with hKtdef
  have hidxlt : ∀ H ∈ Hs, ∀ u ∈ supp (Abs H), idx H u < Kt := by
    intro H hH u hu
    have h1 : u < Umax := hUmax H hH u hu
    have h2 : rk H + 1 ≤ Hs.card := hrklt H hH
    have h3 : (rk H + 1) * Umax ≤ Hs.card * Umax := Nat.mul_le_mul_right _ h2
    have h4 : u + rk H * Umax < (rk H + 1) * Umax := by
      have : (rk H + 1) * Umax = rk H * Umax + Umax := by ring
      omega
    have hi : idx H u = u + rk H * Umax := by rw [hidxdef]
    rw [hi, hKtdef]
    exact Nat.lt_of_lt_of_le h4 h3
  have hidxinj : ∀ H₁ ∈ Hs, ∀ u₁ ∈ supp (Abs H₁), ∀ H₂ ∈ Hs, ∀ u₂ ∈ supp (Abs H₂),
      idx H₁ u₁ = idx H₂ u₂ → H₁ = H₂ ∧ u₁ = u₂ := by
    intro H₁ h₁ u₁ hu₁ H₂ h₂ u₂ hu₂ heq
    have hb₁ : u₁ < Umax := hUmax H₁ h₁ u₁ hu₁
    have hb₂ : u₂ < Umax := hUmax H₂ h₂ u₂ hu₂
    rw [hidxdef] at heq
    simp only at heq
    have hmod : u₁ = u₂ := by
      have e₁ : (u₁ + rk H₁ * Umax) % Umax = u₁ := by
        rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb₁]
      have e₂ : (u₂ + rk H₂ * Umax) % Umax = u₂ := by
        rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb₂]
      rw [← e₁, ← e₂, heq]
    have hrk : rk H₁ = rk H₂ := by
      have := heq
      rw [hmod] at this
      have h5 : rk H₁ * Umax = rk H₂ * Umax := by omega
      exact Nat.eq_of_mul_eq_mul_right hUmax0 h5
    exact ⟨hrkinj H₁ h₁ H₂ h₂ hrk, hmod⟩
  refine ⟨M, Kt, ?_⟩
  intro V _ T S U Tg hTS hUS hUC hSne hTgS hTgU hTgdisj hroom
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
  -- the targets, as subsets of the host subtype
  set Tg' : Finset (Sym2 ℕ) → ℕ → Finset {x // x ∈ S} := fun H u => (Tg (idx H u)).subtype (· ∈ S)
    with hTg'def
  have hTg'mem : ∀ H u, ∀ a : {x // x ∈ S}, a ∈ Tg' H u ↔ val a ∈ Tg (idx H u) := by
    intro H u a
    rw [hTg'def, hvaldef]
    simp [Finset.mem_subtype]
  have hTg'U : ∀ H : Finset (Sym2 ℕ), ∀ u ∈ supp (Abs H), C ≤ u → Disjoint (Tg' H u) U' := by
    intro H u _ _
    refine Finset.disjoint_left.2 fun a ha haU => ?_
    have h1 : val a ∈ Tg (idx H u) := (hTg'mem H u a).1 ha
    have h2 : val a ∈ U := (hU'val a).1 haU
    exact (Finset.disjoint_left.1 (hTgU (idx H u))) h1 h2
  have hTg'disj : ∀ H₁ ∈ Hs, ∀ H₂ ∈ Hs, ∀ u ∈ supp (Abs H₁), ∀ v ∈ supp (Abs H₂),
      C ≤ u → C ≤ v → (H₁ ≠ H₂ ∨ u ≠ v) → Disjoint (Tg' H₁ u) (Tg' H₂ v) := by
    intro H₁ h₁ H₂ h₂ u hu v hv _ _ hne
    have hidxne : idx H₁ u ≠ idx H₂ v := by
      intro hcon
      obtain ⟨hH, hu'⟩ := hidxinj H₁ h₁ u hu H₂ h₂ v hv hcon
      rcases hne with h | h
      · exact h hH
      · exact h hu'
    refine Finset.disjoint_left.2 fun a ha ha' => ?_
    exact (Finset.disjoint_left.1 (hTgdisj _ _ hidxne)) ((hTg'mem H₁ u a).1 ha)
      ((hTg'mem H₂ v a).1 ha')
  have hroom' : ∀ H ∈ Hs, ∀ u ∈ supp (Abs H), C ≤ u → ∀ Q : Finset {x // x ∈ S}, Q.card ≤ 9 →
      (commonNbrs (hostGraph T S) Q ∩ Tg' H u).Nonempty := by
    intro H hH u hu _ Q hQ
    have hQcard : (Q.image val).card ≤ 9 := le_trans Finset.card_image_le hQ
    have hQS : Q.image val ⊆ S := by
      intro x hx
      obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hx
      exact a.2
    obtain ⟨y, hyT, hyadj⟩ := hroom (idx H u) (hidxlt H hH u hu) (Q.image val) hQS hQcard
    have hyS : y ∈ S := hTgS _ hyT
    refine ⟨⟨y, hyS⟩, Finset.mem_inter.2 ⟨?_, (hTg'mem H u ⟨y, hyS⟩).2 hyT⟩⟩
    simp only [commonNbrs, Finset.mem_filter, Finset.mem_univ, true_and]
    intro a ha
    have hedge : s((a : V), y) ∈ T := hyadj (a : V) (Finset.mem_image_of_mem val ha)
    refine ⟨?_, hedge⟩
    intro hcon
    refine hloopT _ hedge ?_
    have : (a : V) = y := congrArg val hcon
    simp [Sym2.isDiag_iff_proj_eq, this]
  -- place the whole family into the targets
  obtain ⟨B, W, hP⟩ :=
    exists_placement_target (hostGraph T S) C e₀ he₀inj U' hU'def Hs Abs Tg' hrootlt
      (fun H hH => hAbs H hH) (fun H _ => hTg'U H) hTg'disj hroom'
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
    · exact (Finset.disjoint_left.1 (hP.fresh_disj H₁ h₁) hvW) hU
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
    exact (Finset.disjoint_left.1 (hP.fresh_disj H hH)) ha ((hU'val a).2 hcon)
  have hFrmem : ∀ v ∈ Fr, ∃ H ∈ Hs, ∃ a ∈ W H, val a = v := by
    intro v hv
    obtain ⟨H, hH, hv'⟩ := Finset.mem_biUnion.1 hv
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hv'
    exact ⟨H, hH, a, ha, rfl⟩
  refine ⟨R₂, Fr, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
  · -- each target set receives at most one placed vertex
    intro j
    refine Finset.card_le_one.2 ?_
    intro a ha b hb
    obtain ⟨haFr, haT⟩ := Finset.mem_inter.1 ha
    obtain ⟨hbFr, hbT⟩ := Finset.mem_inter.1 hb
    obtain ⟨H₁, h₁, x₁, hx₁, rfl⟩ := hFrmem a haFr
    obtain ⟨H₂, h₂, x₂, hx₂, hx₂eq⟩ := hFrmem b hbFr
    obtain ⟨u₁, hu₁, hu₁C, hx₁T⟩ := hP.fresh_mem H₁ h₁ _ hx₁
    obtain ⟨u₂, hu₂, hu₂C, hx₂T⟩ := hP.fresh_mem H₂ h₂ _ hx₂
    have hj₁ : idx H₁ u₁ = j := by
      by_contra hcon
      exact (Finset.disjoint_left.1 (hTgdisj _ _ hcon)) ((hTg'mem H₁ u₁ x₁).1 hx₁T) haT
    have hj₂ : idx H₂ u₂ = j := by
      by_contra hcon
      refine (Finset.disjoint_left.1 (hTgdisj _ _ hcon)) ((hTg'mem H₂ u₂ x₂).1 hx₂T) ?_
      rw [hx₂eq]; exact hbT
    obtain ⟨hHH, huu⟩ := hidxinj H₁ h₁ u₁ hu₁ H₂ h₂ u₂ hu₂ (by rw [hj₁, hj₂])
    subst hHH
    subst huu
    have hone := hP.fresh_one H₁ h₁ u₁ hu₁ hu₁C
    have hmem₁ : x₁ ∈ W H₁ ∩ Tg' H₁ u₁ := Finset.mem_inter.2 ⟨hx₁, hx₁T⟩
    have hmem₂ : x₂ ∈ W H₁ ∩ Tg' H₁ u₁ := Finset.mem_inter.2 ⟨hx₂, hx₂T⟩
    have : x₁ = x₂ := Finset.card_le_one.1 hone x₁ hmem₁ x₂ hmem₂
    rw [this, hx₂eq]
  · -- every placed vertex lies in one of the target sets
    intro v hv
    obtain ⟨H, hH, a, ha, rfl⟩ := hFrmem v hv
    obtain ⟨u, hu, huC, haT⟩ := hP.fresh_mem H hH _ ha
    exact ⟨idx H u, hidxlt H hH u hu, (hTg'mem H u a).1 haT⟩
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
