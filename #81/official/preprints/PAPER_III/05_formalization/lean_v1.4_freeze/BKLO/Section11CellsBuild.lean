/-
# Building the cells absorber `A*` (BKLO §8 + §5, in the cells form of §11)

`BKLO/Section11Cells.lean` reduces the dense triangle-decomposition theorem to the single
interface `BKLO.CellsAbsorptionK3`: an absorber `A*`, reserved before the near-optimal
decomposition of §10 is run, which absorbs every even remainder confined to the **bottom cells**
of the partition sequence.

This file builds that absorber the way BKLO §8 does: as the edge-disjoint union, over the cells,
of *per-cell* bounded absorbers.  The two ingredients are the ones already proved in this project:

* `BKLO.sparseAbsorberExistence_nine` (§8.1) and `BKLO.exists_placement` (§5 Lemma 5.2), packaged
  as `BKLO.coreAbsorberExistence_holds`; here they are repackaged as
  `BKLO.coreAbsorberExistence_bounded`, which records that the reserved per-cell structure has
  **bounded size** `M = M(C)` — the quantitative form the union over cells needs;
* an induction over the cells (`BKLO.exists_cellsAbsorbers`), reserving one bounded absorber per
  cell edge-disjointly from all the earlier ones.

The outcome is `BKLO.triDecomp_cellsAbsorber_union`: if `A` is the edge-disjoint union of per-cell
core absorbers, then `A ∪ H` is triangle-decomposable for every `H` that is confined to the cells
and *triangle-divisible cell by cell*.

Everything here is `sorry`-free.  What it does **not** yet give, and what therefore separates it
from `BKLO.CellsAbsorptionK3`, is recorded precisely in `BKLO/SECTION11_CELLS_STATUS.md`.
-/
import BKLO.CoreAbsorberExists
import BKLO.Section11Cells

open Finset

namespace BKLO

/-! ### The per-cell absorber, with a bound on its size

`BKLO.coreAbsorberExistence_holds` reserves, inside a dense host and avoiding an already reserved
set, a structure `R₂` containing an absorber for every triangle-divisible edge set inside a
bounded core.  For the union over cells one needs the *size* of `R₂` to be bounded by a constant
depending on the core size alone; this is what the placement of §5 actually delivers, and it is
recorded here. -/

/-- **The bounded-core absorber with an explicit size bound.**  For every core size `C` and every
`γ > 0` there are constants `M` and `n₀` such that, inside a host `E ⊆ cliqueEdges S` on at least
`n₀` vertices of minimum degree `(9/10 + γ)|S|`, and avoiding any already reserved `R₁ ⊆ E` of
maximum degree at most `γ|S|/2`, one can reserve `R₂ ⊆ E \ R₁` of size at most `M` which contains
an absorber for every triangle-divisible edge set inside any core `U ⊆ S` with `|U| ≤ C`. -/
theorem coreAbsorberExistence_bounded (C : ℕ) (γ : ℝ) : ∃ M n₀ : ℕ,
    ∀ {V : Type} [DecidableEq V] (E R₁ : Finset (Sym2 V)) (S U : Finset V),
      n₀ ≤ S.card → E ⊆ cliqueEdges S → U ⊆ S → U.card ≤ C →
      (∀ v ∈ S, (9 / 10 + γ) * (S.card : ℝ) ≤ (edeg E v : ℝ)) → R₁ ⊆ E →
      (∀ v : V, (edeg R₁ v : ℝ) ≤ γ * (S.card : ℝ) / 2) →
      ∃ R₂ : Finset (Sym2 V), R₂ ⊆ E \ R₁ ∧ R₂.card ≤ M ∧ CoreAbsorbers U R₂ := by
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
  refine ⟨M, max (10 * K + 10) C, ?_⟩
  intro V _ E R₁ S U hn hES hUS hUC hdeg hR₁E hR₁deg
  have hnK : 10 * K + 10 ≤ S.card := le_trans (le_max_left _ _) hn
  have hnC : C ≤ S.card := le_trans (le_max_right _ _) hn
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
    have h4 : (9 : ℝ) * (S.card : ℝ) ≤ 10 * (edeg T v : ℝ) := by linarith only [h1, h2, h3]
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

/-! ### Reserving one bounded absorber per cell, edge-disjointly -/

variable {V : Type} [DecidableEq V]

/-- **The cells absorber, reserved cell by cell.**

Let `Q` be a family of cells of size at most `C` inside a large dense host `E ⊆ cliqueEdges S`,
and let `M` be the per-cell bound of `BKLO.coreAbsorberExistence_bounded`.  Provided the total
budget `|Q| · M` stays below `γ|S|/2` — the room the reservation of the next cell needs — there is
a family `R` of pairwise edge-disjoint structures, one per cell, each of size at most `M`, each a
core absorbing structure for its cell.

This is BKLO's §8 construction in the cells form: one bounded absorber per bottom cell of the
vortex, placed edge-disjointly by §5. -/
theorem exists_cellsAbsorbers {C : ℕ} {γ : ℝ} {M n₀ : ℕ}
    (hbase : ∀ {V : Type} [DecidableEq V] (E R₁ : Finset (Sym2 V)) (S U : Finset V),
      n₀ ≤ S.card → E ⊆ cliqueEdges S → U ⊆ S → U.card ≤ C →
      (∀ v ∈ S, (9 / 10 + γ) * (S.card : ℝ) ≤ (edeg E v : ℝ)) → R₁ ⊆ E →
      (∀ v : V, (edeg R₁ v : ℝ) ≤ γ * (S.card : ℝ) / 2) →
      ∃ R₂ : Finset (Sym2 V), R₂ ⊆ E \ R₁ ∧ R₂.card ≤ M ∧ CoreAbsorbers U R₂)
    (E : Finset (Sym2 V)) (S : Finset V) (Q : Finset (Finset V))
    (hn : n₀ ≤ S.card) (hES : E ⊆ cliqueEdges S)
    (hdeg : ∀ v ∈ S, (9 / 10 + γ) * (S.card : ℝ) ≤ (edeg E v : ℝ))
    (hQS : ∀ P ∈ Q, P ⊆ S) (hQC : ∀ P ∈ Q, P.card ≤ C)
    (hbudget : ((Q.card * M : ℕ) : ℝ) ≤ γ * (S.card : ℝ) / 2) :
    ∃ R : Finset V → Finset (Sym2 V),
      (∀ P ∈ Q, R P ⊆ E) ∧ (∀ P ∈ Q, (R P).card ≤ M) ∧
      (∀ P ∈ Q, CoreAbsorbers P (R P)) ∧
      (∀ P ∈ Q, ∀ P' ∈ Q, P ≠ P' → Disjoint (R P) (R P')) := by
  classical
  induction Q using Finset.induction_on with
  | empty => exact ⟨fun _ => ∅, by simp, by simp, by simp, by simp⟩
  | @insert P Q hPQ ih =>
    have hQS' : ∀ X ∈ Q, X ⊆ S := fun X hX => hQS X (Finset.mem_insert_of_mem hX)
    have hQC' : ∀ X ∈ Q, X.card ≤ C := fun X hX => hQC X (Finset.mem_insert_of_mem hX)
    have hcardlt : Q.card * M ≤ (insert P Q).card * M := by
      have : Q.card ≤ (insert P Q).card := Finset.card_le_card (Finset.subset_insert _ _)
      exact Nat.mul_le_mul_right _ this
    have hbudget' : ((Q.card * M : ℕ) : ℝ) ≤ γ * (S.card : ℝ) / 2 :=
      le_trans (by exact_mod_cast hcardlt) hbudget
    obtain ⟨R, hRE, hRcard, hRabs, hRdisj⟩ := ih hQS' hQC' hbudget'
    -- everything reserved so far
    set A : Finset (Sym2 V) := Q.biUnion R with hAdef
    have hAE : A ⊆ E := Finset.biUnion_subset.2 hRE
    have hAcard : A.card ≤ Q.card * M := by
      refine le_trans Finset.card_biUnion_le ?_
      calc ∑ X ∈ Q, (R X).card ≤ ∑ _X ∈ Q, M := Finset.sum_le_sum fun X hX => hRcard X hX
        _ = Q.card * M := by rw [Finset.sum_const, smul_eq_mul]
    have hAdeg : ∀ v : V, (edeg A v : ℝ) ≤ γ * (S.card : ℝ) / 2 := by
      intro v
      have h1 : edeg A v ≤ A.card := Finset.card_filter_le _ _
      have h2 : (edeg A v : ℝ) ≤ ((Q.card * M : ℕ) : ℝ) := by
        exact_mod_cast le_trans h1 hAcard
      linarith [hbudget']
    obtain ⟨RP, hRPsub, hRPcard, hRPabs⟩ :=
      hbase E A S P hn hES (hQS P (Finset.mem_insert_self _ _))
        (hQC P (Finset.mem_insert_self _ _)) hdeg hAE hAdeg
    have hRPE : RP ⊆ E := fun e he => (Finset.mem_sdiff.1 (hRPsub he)).1
    have hRPdisjA : Disjoint RP A :=
      Finset.disjoint_left.2 fun e he he' => (Finset.mem_sdiff.1 (hRPsub he)).2 he'
    refine ⟨Function.update R P RP, ?_, ?_, ?_, ?_⟩
    · intro X hX
      rcases Finset.mem_insert.1 hX with rfl | hX'
      · rw [Function.update_self]; exact hRPE
      · rw [Function.update_of_ne (by rintro rfl; exact hPQ hX')]; exact hRE X hX'
    · intro X hX
      rcases Finset.mem_insert.1 hX with rfl | hX'
      · rw [Function.update_self]; exact hRPcard
      · rw [Function.update_of_ne (by rintro rfl; exact hPQ hX')]; exact hRcard X hX'
    · intro X hX
      rcases Finset.mem_insert.1 hX with rfl | hX'
      · rw [Function.update_self]; exact hRPabs
      · rw [Function.update_of_ne (by rintro rfl; exact hPQ hX')]; exact hRabs X hX'
    · have key : ∀ X ∈ Q, Disjoint RP (R X) := by
        intro X hX
        exact Finset.disjoint_of_subset_right (Finset.subset_biUnion_of_mem R hX) hRPdisjA
      intro X hX Y hY hne
      rcases Finset.mem_insert.1 hX with rfl | hX' <;> rcases Finset.mem_insert.1 hY with rfl | hY'
      · exact absurd rfl hne
      · rw [Function.update_self, Function.update_of_ne (by rintro rfl; exact hPQ hY')]
        exact key Y hY'
      · rw [Function.update_self, Function.update_of_ne (by rintro rfl; exact hPQ hX')]
        exact (key X hX').symm
      · rw [Function.update_of_ne (by rintro rfl; exact hPQ hX'),
          Function.update_of_ne (by rintro rfl; exact hPQ hY')]
        exact hRdisj X hX' Y hY' hne

/-! ### The union over the cells absorbs a cell-wise divisible remainder -/

/-- The piece of `H` inside the cell `P`. -/
private def cellPiece (H : Finset (Sym2 V)) (P : Finset V) : Finset (Sym2 V) :=
  H ∩ cliqueEdges P

/-- A remainder confined to pairwise disjoint cells is the disjoint union of its cell pieces. -/
theorem biUnion_cellPiece {H : Finset (Sym2 V)} {Q : Finset (Finset V)}
    (hH : ∀ e ∈ H, ∃ P ∈ Q, e ∈ cliqueEdges P) :
    Q.biUnion (fun P => cellPiece H P) = H := by
  classical
  refine Finset.Subset.antisymm (fun e he => ?_) (fun e he => ?_)
  · obtain ⟨P, -, heP⟩ := Finset.mem_biUnion.1 he
    exact (Finset.mem_inter.1 heP).1
  · obtain ⟨P, hP, heP⟩ := hH e he
    exact Finset.mem_biUnion.2 ⟨P, hP, Finset.mem_inter.2 ⟨he, heP⟩⟩

/-- Cell pieces of disjoint cells are edge-disjoint. -/
theorem cellPiece_disjoint {H : Finset (Sym2 V)} {P P' : Finset V} (hPP' : Disjoint P P') :
    Disjoint (cellPiece H P) (cellPiece H P') := by
  classical
  refine Finset.disjoint_left.2 fun e he he' => ?_
  have h1 : e ∈ cliqueEdges P := (Finset.mem_inter.1 he).2
  have h2 : e ∈ cliqueEdges P' := (Finset.mem_inter.1 he').2
  induction e using Sym2.ind with
  | _ x y =>
    have hx : x ∈ P := (mem_cliqueEdgesV.1 h1).1 x (by simp)
    have hx' : x ∈ P' := (mem_cliqueEdgesV.1 h2).1 x (by simp)
    exact (Finset.disjoint_left.1 hPP' hx) hx'

/-- **The cells absorber absorbs.**  If `R` is a family of pairwise edge-disjoint core absorbing
structures, one for each cell of a pairwise disjoint family `Q`, and `H` is confined to the cells
of `Q`, edge-disjoint from the reserved union `A = ⋃ R`, and *triangle-divisible cell by cell*,
then `A ∪ H` is triangle-decomposable.

This is the absorption step of BKLO §11 in the cells form: each cell's leftover is swallowed by the
absorber reserved for that cell, and the unused parts of the reserved structures are decomposable
on their own. -/
theorem triDecomp_cellsAbsorber_union {Q : Finset (Finset V)} {R : Finset V → Finset (Sym2 V)}
    {H : Finset (Sym2 V)}
    (hQdisj : ∀ P ∈ Q, ∀ P' ∈ Q, P ≠ P' → Disjoint P P')
    (hRabs : ∀ P ∈ Q, CoreAbsorbers P (R P))
    (hRdisj : ∀ P ∈ Q, ∀ P' ∈ Q, P ≠ P' → Disjoint (R P) (R P'))
    (hH : ∀ e ∈ H, ∃ P ∈ Q, e ∈ cliqueEdges P)
    (hHA : Disjoint (Q.biUnion R) H)
    (hHdiv : ∀ P ∈ Q, TriDivisible (cellPiece H P)) :
    TriDecomp (Q.biUnion R ∪ H) := by
  classical
  -- the absorber used in each cell, and the part of the reservation left over there
  have hchoice : ∀ P ∈ Q, ∃ A : Finset (Sym2 V), A ⊆ R P ∧ IsAbsorber A (cellPiece H P) ∧
      TriDecomp (R P \ A) := by
    intro P hP
    exact (hRabs P hP).absorb (cellPiece H P) Finset.inter_subset_right (hHdiv P hP)
  choose! Aused hAsub hAabs hArest using hchoice
  -- the whole thing, cell by cell
  set F : Finset V → Finset (Sym2 V) :=
    fun P => (Aused P ∪ cellPiece H P) ∪ (R P \ Aused P) with hFdef
  have hFdec : ∀ P ∈ Q, TriDecomp (F P) := by
    intro P hP
    have hd : Disjoint (Aused P ∪ cellPiece H P) (R P \ Aused P) := by
      refine Finset.disjoint_union_left.2
        ⟨Finset.disjoint_left.2 fun e he he' => (Finset.mem_sdiff.1 he').2 he, ?_⟩
      refine Finset.disjoint_left.2 fun e he he' => ?_
      have h1 : e ∈ R P := (Finset.mem_sdiff.1 he').1
      have h2 : e ∈ Q.biUnion R := Finset.mem_biUnion.2 ⟨P, hP, h1⟩
      exact (Finset.disjoint_left.1 hHA h2) ((Finset.mem_inter.1 he).1)
    exact TriDecomp.union hd (hAabs P hP).2.2 (hArest P hP)
  have hFdisj : ∀ P ∈ Q, ∀ P' ∈ Q, P ≠ P' → Disjoint (F P) (F P') := by
    intro P hP P' hP' hne
    have hRR : Disjoint (R P) (R P') := hRdisj P hP P' hP' hne
    have hHH : Disjoint (cellPiece H P) (cellPiece H P') := cellPiece_disjoint (hQdisj P hP P' hP' hne)
    have hRH : ∀ X ∈ Q, ∀ Y ∈ Q, Disjoint (R X) (cellPiece H Y) := by
      intro X hX Y _
      refine Finset.disjoint_left.2 fun e he he' => ?_
      have h2 : e ∈ Q.biUnion R := Finset.mem_biUnion.2 ⟨X, hX, he⟩
      exact (Finset.disjoint_left.1 hHA h2) ((Finset.mem_inter.1 he').1)
    have hFsub : ∀ X ∈ Q, F X ⊆ R X ∪ cellPiece H X := by
      intro X hX e he
      rcases Finset.mem_union.1 he with h | h
      · rcases Finset.mem_union.1 h with h' | h'
        · exact Finset.mem_union_left _ (hAsub X hX h')
        · exact Finset.mem_union_right _ h'
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.1 h).1
    have hbig : Disjoint (R P ∪ cellPiece H P) (R P' ∪ cellPiece H P') := by
      refine Finset.disjoint_union_left.2 ⟨Finset.disjoint_union_right.2 ⟨hRR, ?_⟩,
        Finset.disjoint_union_right.2 ⟨?_, hHH⟩⟩
      · exact hRH P hP P' hP'
      · exact (hRH P' hP' P hP).symm
    exact Finset.disjoint_of_subset_left (hFsub P hP)
      (Finset.disjoint_of_subset_right (hFsub P' hP') hbig)
  have hsplit : Q.biUnion R ∪ H = Q.biUnion F := by
    have hHeq : Q.biUnion (fun P => cellPiece H P) = H := biUnion_cellPiece hH
    refine Finset.Subset.antisymm (fun e he => ?_) (fun e he => ?_)
    · rcases Finset.mem_union.1 he with h | h
      · obtain ⟨P, hP, heP⟩ := Finset.mem_biUnion.1 h
        refine Finset.mem_biUnion.2 ⟨P, hP, ?_⟩
        by_cases hA : e ∈ Aused P
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ hA)
        · exact Finset.mem_union_right _ (Finset.mem_sdiff.2 ⟨heP, hA⟩)
      · rw [← hHeq] at h
        obtain ⟨P, hP, heP⟩ := Finset.mem_biUnion.1 h
        exact Finset.mem_biUnion.2 ⟨P, hP, Finset.mem_union_left _
          (Finset.mem_union_right _ heP)⟩
    · obtain ⟨P, hP, heP⟩ := Finset.mem_biUnion.1 he
      rcases Finset.mem_union.1 heP with h | h
      · rcases Finset.mem_union.1 h with h' | h'
        · exact Finset.mem_union_left _ (Finset.mem_biUnion.2 ⟨P, hP, hAsub P hP h'⟩)
        · exact Finset.mem_union_right _ ((Finset.mem_inter.1 h').1)
      · exact Finset.mem_union_left _
          (Finset.mem_biUnion.2 ⟨P, hP, (Finset.mem_sdiff.1 h).1⟩)
  rw [hsplit]
  exact TriDecomp.biUnion hFdec hFdisj

/-! ### Why the per-cell absorber needs a cell-wise divisible remainder

`BKLO.triDecomp_cellsAbsorber_union` absorbs a remainder that is triangle-divisible *cell by
cell*.  The next two results show that this hypothesis is not an artefact of the proof: a reserved
structure that is a disjoint union of per-cell pieces pins the residue `|H ∩ cliqueEdges P| mod 3`
of each cell before the remainder is known, and both residue classes really occur among the
parity-legal (even-degree) remainders inside a cell with at least four vertices. -/

/-- **A reserved set pins the residue of what it absorbs.**  If `A ∪ Y` and `A ∪ Y'` are both
triangle-decomposable, with `Y` and `Y'` edge-disjoint from `A`, then `|Y| ≡ |Y'| (mod 3)`. -/
theorem card_mod_three_eq_of_absorbs {A Y Y' : Finset (Sym2 V)} (hY : Disjoint A Y)
    (hY' : Disjoint A Y') (h : TriDecomp (A ∪ Y)) (h' : TriDecomp (A ∪ Y')) :
    Y.card % 3 = Y'.card % 3 := by
  obtain ⟨s, hs⟩ := h.triDivisible.2
  obtain ⟨s', hs'⟩ := h'.triDivisible.2
  rw [Finset.card_union_of_disjoint hY] at hs
  rw [Finset.card_union_of_disjoint hY'] at hs'
  omega

/-- A four-cycle has even degrees: the parity condition on the §10 remainder does not force its
size to be divisible by three. -/
theorem evenDegrees_fourCycle (a b c d : V) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    EvenDegrees ({s(a, b), s(b, c), s(c, d), s(d, a)} : Finset (Sym2 V)) := by
  have e12 : (s(a, b) : Sym2 V) ≠ s(b, c) := by simp; tauto
  have e13 : (s(a, b) : Sym2 V) ≠ s(c, d) := by simp; tauto
  have e14 : (s(a, b) : Sym2 V) ≠ s(d, a) := by simp; tauto
  have e23 : (s(b, c) : Sym2 V) ≠ s(c, d) := by simp; tauto
  have e24 : (s(b, c) : Sym2 V) ≠ s(d, a) := by simp; tauto
  have e34 : (s(c, d) : Sym2 V) ≠ s(d, a) := by simp; tauto
  intro v
  simp only [edeg, Finset.filter_insert, Finset.filter_singleton]
  by_cases h1 : v ∈ s(a, b) <;> by_cases h2 : v ∈ s(b, c) <;> by_cases h3 : v ∈ s(c, d) <;>
    by_cases h4 : v ∈ s(d, a) <;>
    simp_all [Sym2.mem_iff, Finset.card_insert_of_notMem]; decide

/-- A four-cycle has four edges. -/
theorem card_fourCycle (a b c d : V) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hcd : c ≠ d) :
    ({s(a, b), s(b, c), s(c, d), s(d, a)} : Finset (Sym2 V)).card = 4 := by
  rw [Finset.card_insert_of_notMem (by simp; tauto),
    Finset.card_insert_of_notMem (by simp; tauto),
    Finset.card_insert_of_notMem (by simp; tauto), Finset.card_singleton]

/-- **The per-cell absorber cannot absorb every even remainder of its cell.**

A cell with at least four vertices carries even-degree remainders of two different sizes modulo
three — the empty one and a four-cycle — so no reserved structure `A` avoiding the cell can absorb
both.  Consequently the cells-form absorber of `BKLO.triDecomp_cellsAbsorber_union` really does
need the §10 remainder to be triangle-divisible **cell by cell**, and not merely globally. -/
theorem not_absorbs_all_even_of_cell {P : Finset V} (hP : 4 ≤ P.card) {A : Finset (Sym2 V)}
    (hA : Disjoint A (cliqueEdges P)) :
    ¬ ∀ Y : Finset (Sym2 V), Y ⊆ cliqueEdges P → EvenDegrees Y → TriDecomp (A ∪ Y) := by
  classical
  intro habs
  obtain ⟨T, hTP, hTcard⟩ := Finset.exists_subset_card_eq hP
  obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, hT⟩ := Finset.card_eq_four.1 hTcard
  have hmem : ∀ x ∈ ({a, b, c, d} : Finset V), x ∈ P := by
    intro x hx; exact hTP (by rw [hT]; exact hx)
  have ha : a ∈ P := hmem a (by simp)
  have hb : b ∈ P := hmem b (by simp)
  have hc : c ∈ P := hmem c (by simp)
  have hd : d ∈ P := hmem d (by simp)
  set Y : Finset (Sym2 V) := {s(a, b), s(b, c), s(c, d), s(d, a)} with hYdef
  have hYP : Y ⊆ cliqueEdges P := by
    intro e he
    simp only [hYdef, Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl <;>
      refine mem_cliqueEdgesV.2 ⟨?_, ?_⟩ <;>
      simp_all [Sym2.mem_iff, Sym2.isDiag_iff_proj_eq]; tauto
  have hdisjY : Disjoint A Y := Finset.disjoint_of_subset_right hYP hA
  have h0 : TriDecomp (A ∪ ∅) := habs ∅ (Finset.empty_subset _) (fun v => by simp)
  have h1 : TriDecomp (A ∪ Y) := habs Y hYP (evenDegrees_fourCycle a b c d hab hac had hbc hbd hcd)
  have := card_mod_three_eq_of_absorbs (Finset.disjoint_empty_right A) hdisjY h0 h1
  rw [card_fourCycle a b c d hab hac had hbc hbd hcd] at this
  simp at this

end BKLO
