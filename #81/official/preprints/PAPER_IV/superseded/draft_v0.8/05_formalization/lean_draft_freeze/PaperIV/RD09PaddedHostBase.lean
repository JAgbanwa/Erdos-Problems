import PaperIV.PaddedEquitableColouring
import PaperIV.RD09L1Adapter
import PaperIV.FiniteHeavySelection

/-!
# RD09 physical host bases on a padded equitable palette

This is the physical counterpart of `PaddedEquitableColouring`.  It uses the
canonical palette `max (#hosts) (Delta+1)`, so the host-to-colour injection is
unconditional.  All base families remain literal transported matching
classes; incompatible bases are filtered exactly as in `RD09L1Adapter`.
-/

namespace PaperIV.RD09PaddedHostBase

open Finset PaperIV.Model PaperIV.ColourClasses
open PaperIV.EquitableEdgeColouring PaperIV.PaddedEquitableColouring
open PaperIV.TransportedMatchings PaperIV.ExteriorTriangleLift
open PaperIV.MultiHostTriangleLift PaperIV.RD09L1Adapter

variable {V A I : Type*} [Fintype V] [DecidableEq V]
variable [Fintype A] [DecidableEq A] [Fintype I] [DecidableEq I]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable {H : SimpleGraph A} [DecidableRel H.Adj]

abbrev Palette (H : SimpleGraph A) [DecidableRel H.Adj] (I : Type*) [Fintype I] :=
  Fin (paddedPaletteSize H (Fintype.card I))

theorem hostCount_le_card_palette (H : SimpleGraph A) [DecidableRel H.Adj]
    (I : Type*) [Fintype I] : Fintype.card I ≤ Fintype.card (Palette H I) := by
  simpa [Palette] using hostCount_le_paddedPaletteSize H (Fintype.card I)

/-- The unconditional equitable colouring on the padded palette. -/
noncomputable def paddedLocalColour (H : SimpleGraph A) [DecidableRel H.Adj]
    (I : Type*) [Fintype I] : Sym2 A → Palette H I :=
  (equitableBoundedColouringOfCard H _
    (vizingSize_le_paddedPaletteSize H (Fintype.card I))).colour

theorem paddedLocalColour_proper (H : SimpleGraph A) [DecidableRel H.Adj]
    (I : Type*) [Fintype I] :
    ProperOn (graphEdges H) (paddedLocalColour H I) :=
  (equitableBoundedColouringOfCard H _
    (vizingSize_le_paddedPaletteSize H (Fintype.card I))).proper

theorem paddedLocalColour_class_card_le (H : SimpleGraph A) [DecidableRel H.Adj]
    (I : Type*) [Fintype I] (c : Palette H I) :
    (colourClass (graphEdges H) (paddedLocalColour H I) c).card ≤
      classCeiling (graphEdges H).card (paddedPaletteSize H (Fintype.card I)) :=
  (equitableBoundedColouringOfCard H _
    (vizingSize_le_paddedPaletteSize H (Fintype.card I))).class_card_le c

/-- A maximum-average selection of exactly one padded colour per physical
host.  This is the missing numerical part of the padded construction: merely
injecting the hosts into the palette need not select enough exterior edges. -/
noncomputable def heavyPaletteSelection (H : SimpleGraph A) [DecidableRel H.Adj]
    (I : Type*) [Fintype I] : Fin (Fintype.card I) → Palette H I :=
  Classical.choose
    (PaperIV.FiniteHeavySelection.exists_injective_card_mul_sum_le_card_mul_sum
      (fun c : Palette H I =>
        (colourClass (graphEdges H) (paddedLocalColour H I) c).card)
      (Fintype.card I) (hostCount_le_card_palette H I))

theorem heavyPaletteSelection_injective (H : SimpleGraph A) [DecidableRel H.Adj]
    (I : Type*) [Fintype I] : Function.Injective (heavyPaletteSelection H I) :=
  (Classical.choose_spec
    (PaperIV.FiniteHeavySelection.exists_injective_card_mul_sum_le_card_mul_sum
      (fun c : Palette H I =>
        (colourClass (graphEdges H) (paddedLocalColour H I) c).card)
      (Fintype.card I) (hostCount_le_card_palette H I))).1

/-- The selected `p` classes contain at least the `p/c` fraction of all
exterior edges, in cross-multiplied integral form. -/
theorem heavyPaletteSelection_mass (H : SimpleGraph A) [DecidableRel H.Adj]
    (I : Type*) [Fintype I] :
    Fintype.card I * (graphEdges H).card ≤
      paddedPaletteSize H (Fintype.card I) *
        ∑ i : Fin (Fintype.card I),
          (colourClass (graphEdges H) (paddedLocalColour H I)
            (heavyPaletteSelection H I i)).card := by
  have hs :=
    (Classical.choose_spec
      (PaperIV.FiniteHeavySelection.exists_injective_card_mul_sum_le_card_mul_sum
        (fun c : Palette H I =>
          (colourClass (graphEdges H) (paddedLocalColour H I) c).card)
        (Fintype.card I) (hostCount_le_card_palette H I))).2
  have hsum :
      (∑ c : Palette H I,
        (colourClass (graphEdges H) (paddedLocalColour H I) c).card) =
        (graphEdges H).card :=
    sum_card_colourClass_univ _ _
  calc
    Fintype.card I * (graphEdges H).card =
        Fintype.card I * ∑ c : Palette H I,
          (colourClass (graphEdges H) (paddedLocalColour H I) c).card := by rw [hsum]
    _ ≤ Fintype.card (Palette H I) *
        ∑ i : Fin (Fintype.card I),
          (colourClass (graphEdges H) (paddedLocalColour H I)
            (heavyPaletteSelection H I i)).card := hs
    _ = paddedPaletteSize H (Fintype.card I) *
        ∑ i : Fin (Fintype.card I),
          (colourClass (graphEdges H) (paddedLocalColour H I)
            (heavyPaletteSelection H I i)).card := by simp [Palette]

/-- The heavy selected colour carried by a host. -/
noncomputable def heavyHostColour (H : SimpleGraph A) [DecidableRel H.Adj]
    (I : Type*) [Fintype I] (i : I) : Palette H I :=
  heavyPaletteSelection H I (Fintype.equivFin I i)

theorem heavyHostColour_injective (H : SimpleGraph A) [DecidableRel H.Adj]
    (I : Type*) [Fintype I] : Function.Injective (heavyHostColour H I) := by
  exact (heavyPaletteSelection_injective H I).comp (Fintype.equivFin I).injective

theorem heavyHostColour_mass (H : SimpleGraph A) [DecidableRel H.Adj]
    (I : Type*) [Fintype I] :
    Fintype.card I * (graphEdges H).card ≤
      paddedPaletteSize H (Fintype.card I) *
        ∑ i : I,
          (colourClass (graphEdges H) (paddedLocalColour H I)
            (heavyHostColour H I i)).card := by
  have hs := heavyPaletteSelection_mass H I
  have heq :
      (∑ i : I,
          (colourClass (graphEdges H) (paddedLocalColour H I)
            (heavyHostColour H I i)).card) =
        ∑ j : Fin (Fintype.card I),
          (colourClass (graphEdges H) (paddedLocalColour H I)
            (heavyPaletteSelection H I j)).card := by
    simpa [heavyHostColour] using
      ((Fintype.equivFin I).sum_comp
        (fun j : Fin (Fintype.card I) =>
          (colourClass (graphEdges H) (paddedLocalColour H I)
            (heavyPaletteSelection H I j)).card))
  rwa [heq]

/-- The literal matching class assigned canonically to host `i`. -/
noncomputable def paddedHostBase (H : SimpleGraph A) [DecidableRel H.Adj]
    (I : Type*) [Fintype I] (f : A ↪ V) (i : I) : Finset (Sym2 V) :=
  mapColourClass f (graphEdges H) (paddedLocalColour H I) (heavyHostColour H I i)

theorem mem_paddedHostBase {f : A ↪ V} {i : I} {e : Sym2 V} :
    e ∈ paddedHostBase H I f i ↔
      ∃ d ∈ graphEdges H, paddedLocalColour H I d = heavyHostColour H I i ∧
        Sym2.map f d = e :=
  mem_mapColourClass

theorem card_paddedHostBase (f : A ↪ V) (i : I) :
    (paddedHostBase H I f i).card =
      (colourClass (graphEdges H) (paddedLocalColour H I) (heavyHostColour H I i)).card :=
  card_mapColourClass _ _ _

theorem card_paddedHostBase_le (f : A ↪ V) (i : I) :
    (paddedHostBase H I f i).card ≤
      classCeiling (graphEdges H).card (paddedPaletteSize H (Fintype.card I)) := by
  rw [card_paddedHostBase]
  exact paddedLocalColour_class_card_le H I _

/-- The selected transported bases retain at least the `p/c` share of every
exterior edge.  This is the literal top-class bound used in RD09-L1. -/
theorem card_mul_graphEdges_le_palette_mul_sum_card_paddedHostBase
    (f : A ↪ V) :
    Fintype.card I * (graphEdges H).card ≤
      paddedPaletteSize H (Fintype.card I) *
        ∑ i : I, (paddedHostBase H I f i).card := by
  have h := heavyHostColour_mass H I
  simpa only [card_paddedHostBase] using h

noncomputable def compatiblePaddedHostBase (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : SimpleGraph A) [DecidableRel H.Adj] (I : Type*) [Fintype I]
    (f : A ↪ V) (r : V) (i : I) : Finset (Sym2 V) :=
  (paddedHostBase H I f i).filter (IsCompatibleBase G r)

noncomputable def paddedIncompatCount (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : SimpleGraph A) [DecidableRel H.Adj] (I : Type*) [Fintype I]
    (f : A ↪ V) (r : V) (i : I) : ℕ :=
  ((paddedHostBase H I f i).filter fun e => ¬ IsCompatibleBase G r e).card

theorem compatiblePaddedHostBase_subset (f : A ↪ V) (r : V) (i : I) :
    compatiblePaddedHostBase G H I f r i ⊆ paddedHostBase H I f i :=
  Finset.filter_subset _ _

theorem card_compatiblePaddedHostBase_add_incompat (f : A ↪ V) (r : V) (i : I) :
    (compatiblePaddedHostBase G H I f r i).card + paddedIncompatCount G H I f r i =
      (paddedHostBase H I f i).card :=
  Finset.card_filter_add_card_filter_not _

theorem paddedHostBase_subset_graphEdges (f : A ↪ V)
    (hcore : ∀ a b : A, H.Adj a b → G.Adj (f a) (f b)) (i : I) :
    paddedHostBase H I f i ⊆ graphEdges G := by
  intro e he
  obtain ⟨d, hd, -, rfl⟩ := mem_paddedHostBase.mp he
  exact PaperIV.RD09LocalPhaseI.mem_graphEdges_map hcore hd

theorem exists_core_of_mem_paddedHostBase {f : A ↪ V} {i : I} {e : Sym2 V}
    (he : e ∈ paddedHostBase H I f i) {x : V} (hx : x ∈ e) :
    ∃ a : A, f a = x := by
  obtain ⟨d, -, -, rfl⟩ := mem_paddedHostBase.mp he
  obtain ⟨a, -, hax⟩ := Sym2.mem_map.mp hx
  exact ⟨a, hax⟩

theorem isLiteralMatching_paddedHostBase (f : A ↪ V) (i : I) :
    IsLiteralMatching (paddedHostBase H I f i) := by
  have hp := mapColourClass_pairwiseDisjoint_toFinset (f := f)
    (paddedLocalColour_proper H I) (heavyHostColour H I i)
  intro e he d hd hne
  exact hp (by simpa [paddedHostBase] using he)
    (by simpa [paddedHostBase] using hd) hne

theorem disjoint_paddedHostBase (f : A ↪ V) {i j : I} (hij : i ≠ j) :
    Disjoint (paddedHostBase H I f i) (paddedHostBase H I f j) :=
  disjoint_mapColourClass fun hc => hij (heavyHostColour_injective H I hc)

theorem isExteriorHub_compatiblePaddedHostBase (f : A ↪ V) (z : I → V)
    (hcore : ∀ a b : A, H.Adj a b → G.Adj (f a) (f b)) (i : I) :
    IsExteriorHub G (z i) (compatiblePaddedHostBase G H I f (z i) i) where
  edges := fun _ he => paddedHostBase_subset_graphEdges f hcore i
    (compatiblePaddedHostBase_subset f (z i) i he)
  matching := fun e he d hd hne =>
    isLiteralMatching_paddedHostBase f i e
      (compatiblePaddedHostBase_subset f (z i) i he) d
      (compatiblePaddedHostBase_subset f (z i) i hd) hne
  hubAdj := by
    intro e he x hx
    exact (Finset.mem_filter.mp he).2 x (Sym2.mem_toFinset.mpr hx)

theorem isMultiExteriorHub_compatiblePaddedHostBase (f : A ↪ V) (z : I → V)
    (hcore : ∀ a b : A, H.Adj a b → G.Adj (f a) (f b))
    (hzInj : Function.Injective z)
    (hzcore : ∀ (i : I) (a : A), z i ≠ f a) :
    IsMultiExteriorHub G z (fun i => compatiblePaddedHostBase G H I f (z i) i) where
  hub := isExteriorHub_compatiblePaddedHostBase f z hcore
  hostInj := hzInj
  exterior := by
    intro i j e he x hx
    obtain ⟨a, rfl⟩ := exists_core_of_mem_paddedHostBase
      (compatiblePaddedHostBase_subset f (z i) i he) hx
    exact fun h => hzcore j a h.symm
  baseDisjoint := by
    intro i j hij
    exact (disjoint_paddedHostBase f hij).mono
      (compatiblePaddedHostBase_subset f (z i) i)
      (compatiblePaddedHostBase_subset f (z j) j)

theorem isPacking_compatiblePaddedHostBase (f : A ↪ V) (z : I → V)
    (hcore : ∀ a b : A, H.Adj a b → G.Adj (f a) (f b))
    (hzInj : Function.Injective z)
    (hzcore : ∀ (i : I) (a : A), z i ≠ f a) :
    IsPacking G (multiLiftedPacking z
      (fun i => compatiblePaddedHostBase G H I f (z i) i)) :=
  isPacking_multiLiftedPacking
    (isMultiExteriorHub_compatiblePaddedHostBase f z hcore hzInj hzcore)

theorem card_paddedPacking_add_incompat (f : A ↪ V) (z : I → V)
    (hcore : ∀ a b : A, H.Adj a b → G.Adj (f a) (f b))
    (hzInj : Function.Injective z)
    (hzcore : ∀ (i : I) (a : A), z i ≠ f a) :
    (multiLiftedPacking z
      (fun i => compatiblePaddedHostBase G H I f (z i) i)).card
        + ∑ i : I, paddedIncompatCount G H I f (z i) i =
      ∑ i : I, (paddedHostBase H I f i).card := by
  rw [card_multiLiftedPacking
    (isMultiExteriorHub_compatiblePaddedHostBase f z hcore hzInj hzcore),
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ =>
    card_compatiblePaddedHostBase_add_incompat f (z i) i

end PaperIV.RD09PaddedHostBase
