import PaperIV.RD09PaddedHostBase
import PaperIV.RD09RootedOrderAdapter

/-!
# The RD09-L1 ledger with an unconditional padded palette

This module repeats the literal geometric charge for the canonical palette
`max (#hosts) (Delta+1)`.  Unlike the historical adapter, no injection of the
host type into `Fin (Delta+1)` is assumed.
-/

namespace PaperIV.RD09PaddedL1Adapter

open Finset PaperIV.Model PaperIV.RD09L1Adapter
open PaperIV.RD09PaddedHostBase PaperIV.MultiHostTriangleLift
open PaperIV.RD09FiniteAveraging PaperIV.RD09RootedOrderAdapter

variable {V A I : Type*} [Fintype V] [DecidableEq V]
variable [Fintype A] [DecidableEq A] [Fintype I] [DecidableEq I]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable {H : SimpleGraph A} [DecidableRel H.Adj]

noncomputable def badCoreEdges (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : SimpleGraph A) [DecidableRel H.Adj] (I : Type*) [Fintype I]
    (f : A ↪ V) (root : I → V) (i r : I) : Finset (Sym2 A) :=
  (graphEdges H).filter fun d =>
    paddedLocalColour H I d = heavyHostColour H I i ∧
      ¬ IsCompatibleBase G (root r) (Sym2.map f d)

theorem paddedIncompatCount_eq_card_badCoreEdges (f : A ↪ V)
    (root : I → V) (i r : I) :
    paddedIncompatCount G H I f (root r) i =
      (badCoreEdges G H I f root i r).card := by
  classical
  unfold paddedIncompatCount paddedHostBase badCoreEdges
  rw [PaperIV.TransportedMatchings.mapColourClass, Finset.filter_image,
    Finset.card_image_of_injective _ (Sym2.map.injective f.injective),
    PaperIV.ColourClasses.colourClass, Finset.filter_filter]

noncomputable def badIncidences (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : SimpleGraph A) [DecidableRel H.Adj] (I : Type*) [Fintype I]
    (f : A ↪ V) (root : I → V) : Finset ((_ : I × I) × Sym2 A) :=
  (Finset.univ : Finset (I × I)).sigma fun p =>
    badCoreEdges G H I f root p.1 p.2

theorem card_badIncidences (f : A ↪ V) (root : I → V) :
    (badIncidences G H I f root).card =
      ∑ i : I, ∑ r : I, paddedIncompatCount G H I f (root r) i := by
  rw [badIncidences, Finset.card_sigma, Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun r _ =>
    (paddedIncompatCount_eq_card_badCoreEdges f root i r).symm

/-- The same `(w-1)A` geometric charge as RD09-L1, now for the padded
colouring.  Injectivity of selected colours is provided canonically by
`heavyHostColour_injective`. -/
theorem total_paddedIncompat_le_mul_card_missingIncidences (f : A ↪ V)
    (root : I → V) (w : ℕ)
    (earlier later : Sym2 A → A) (laterNbr : A → Finset A)
    (hends : ∀ d ∈ graphEdges H, d = s(earlier d, later d))
    (hlater : ∀ d ∈ graphEdges H, later d ∈ laterNbr (earlier d))
    (hwidth : ∀ a : A, (laterNbr a).card ≤ w - 1)
    (hnest : ∀ (r : I), ∀ d ∈ graphEdges H,
      ¬ IsCompatibleBase G (root r) (Sym2.map f d) →
        ¬ G.Adj (root r) (f (earlier d))) :
    (∑ i : I, ∑ r : I, paddedIncompatCount G H I f (root r) i) ≤
      (w - 1) * (missingIncidences G root f).card := by
  classical
  rw [← card_badIncidences f root]
  set T : Finset ((_ : I × A) × A) :=
    (missingIncidences G root f).sigma fun p => laterNbr p.2 with hT
  have hcharge : (badIncidences G H I f root).card ≤ T.card := by
    refine Finset.card_le_card_of_injOn
      (fun x => ⟨(x.1.2, earlier x.2), later x.2⟩) ?_ ?_
    · rintro ⟨⟨i, r⟩, d⟩ hx
      simp only [Finset.mem_coe, badIncidences, Finset.mem_sigma, Finset.mem_univ,
        true_and, badCoreEdges, Finset.mem_filter] at hx
      obtain ⟨hd, -, hbad⟩ := hx
      simp only [hT, Finset.mem_coe, Finset.mem_sigma, mem_missingIncidences]
      exact ⟨hnest r d hd hbad, hlater d hd⟩
    · rintro ⟨⟨i, r⟩, d⟩ hx ⟨⟨i', r'⟩, d'⟩ hy hxy
      simp only [Finset.mem_coe, badIncidences, Finset.mem_sigma, Finset.mem_univ,
        true_and, badCoreEdges, Finset.mem_filter] at hx hy
      obtain ⟨hd, hci, -⟩ := hx
      obtain ⟨hd', hci', -⟩ := hy
      simp only [Sigma.mk.injEq, Prod.mk.injEq, heq_eq_eq] at hxy
      obtain ⟨⟨hr, hearl⟩, hlat⟩ := hxy
      subst hr
      have hdd : d = d' := by
        rw [hends d hd, hends d' hd', hearl, hlat]
      subst hdd
      have hii : i = i' :=
        heavyHostColour_injective H I
          (hci.symm.trans hci')
      subst hii
      rfl
  refine hcharge.trans ?_
  rw [hT, Finset.card_sigma]
  calc
    ∑ p ∈ missingIncidences G root f, (laterNbr p.2).card ≤
        ∑ _p ∈ missingIncidences G root f, (w - 1) :=
      Finset.sum_le_sum fun p _ => hwidth p.2
    _ = (w - 1) * (missingIncidences G root f).card := by
      rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]

section Group

variable [Nonempty I] [Group I]

theorem exists_shift_paddedIncompat_le (f : A ↪ V) (root : I → V)
    (w : ℕ) (earlier later : Sym2 A → A) (laterNbr : A → Finset A)
    (hends : ∀ d ∈ graphEdges H, d = s(earlier d, later d))
    (hlater : ∀ d ∈ graphEdges H, later d ∈ laterNbr (earlier d))
    (hwidth : ∀ a : A, (laterNbr a).card ≤ w - 1)
    (hnest : ∀ (r : I), ∀ d ∈ graphEdges H,
      ¬ IsCompatibleBase G (root r) (Sym2.map f d) →
        ¬ G.Adj (root r) (f (earlier d))) :
    ∃ shift : I,
      Fintype.card I *
          (∑ i : I, paddedIncompatCount G H I f (root (i * shift)) i) ≤
        (w - 1) * (missingIncidences G root f).card := by
  obtain ⟨shift, hs⟩ := exists_shift_card_mul_cost_le_of_total_le
    (fun i r => paddedIncompatCount G H I f (root r) i)
    ((w - 1) * (missingIncidences G root f).card)
    (total_paddedIncompat_le_mul_card_missingIncidences f root w earlier later laterNbr
      hends hlater hwidth hnest)
  exact ⟨shift, by simpa [shiftCost] using hs⟩

/-- Unconditional-palette RD09-L1, with the PEO/orientation obligations
discharged by `RootedEliminationOrder`. -/
theorem rd09PaddedL1_ledger_of_rooted_order
    {P : Finset V} (O : PaperIV.RootedEliminationOrder.Order G P)
    (f : A ↪ V) (root : I → V)
    (hcore : ∀ a b : A, H.Adj a b → G.Adj (f a) (f b))
    (hrootInj : Function.Injective root)
    (hroot : ∀ r, root r ∈ P)
    (hout : ∀ a : A, f a ∉ P) :
    ∃ shift : I, ∃ z : I → V, ∃ E : I → Finset (Sym2 V),
      (∀ i, z i = root (i * shift)) ∧
      (∀ i, E i = compatiblePaddedHostBase G H I f (z i) i) ∧
      IsMultiExteriorHub G z E ∧
      IsPacking G (multiLiftedPacking z E) ∧
      (multiLiftedPacking z E).card +
          ∑ i : I, paddedIncompatCount G H I f (z i) i =
        ∑ i : I, (paddedHostBase H I f i).card ∧
      Fintype.card I * ∑ i : I, (paddedHostBase H I f i).card ≤
        Fintype.card I * (multiLiftedPacking z E).card +
          H.maxDegree * (missingIncidences G root f).card := by
  obtain ⟨hends, hlater, hwidth, hnest⟩ :=
    rooted_order_geometry (H := H) O f root hroot hout hcore
  obtain ⟨shift, hs⟩ := exists_shift_paddedIncompat_le f root
    (H.maxDegree + 1) (edgeEarlier O f) (edgeLater O f)
    (laterCoreNeighbors O f H) hends hlater hwidth hnest
  let z : I → V := fun i => root (i * shift)
  let E : I → Finset (Sym2 V) := fun i => compatiblePaddedHostBase G H I f (z i) i
  have hzInj : Function.Injective z := by
    intro a b hab
    exact mul_right_cancel (hrootInj hab)
  have hzcore : ∀ (i : I) (a : A), z i ≠ f a := by
    intro i a h
    have hi := hroot (i * shift)
    change root (i * shift) = f a at h
    rw [h] at hi
    exact hout a hi
  have hhub := isMultiExteriorHub_compatiblePaddedHostBase f z hcore hzInj hzcore
  have hpack := isPacking_compatiblePaddedHostBase f z hcore hzInj hzcore
  have hadd := card_paddedPacking_add_incompat f z hcore hzInj hzcore
  refine ⟨shift, z, E, fun _ => rfl, fun _ => rfl, hhub, hpack, hadd, ?_⟩
  calc
    Fintype.card I * ∑ i : I, (paddedHostBase H I f i).card =
        Fintype.card I * (multiLiftedPacking z E).card +
          Fintype.card I * ∑ i : I, paddedIncompatCount G H I f (z i) i := by
      rw [← Nat.mul_add, hadd]
    _ ≤ _ := Nat.add_le_add_left hs _

/-- Sharp padded L1 ledger for an induced exterior graph.  The discarded
incidences are charged with the PEO clique width `cliqueNum H - 1`; this is
the coefficient used by the numerical RD09 proof. -/
theorem rd09PaddedL1_ledger_cliqueNum_of_rooted_order
    {P : Finset V} (O : PaperIV.RootedEliminationOrder.Order G P)
    (f : A ↪ V) (root : I → V)
    (hcore : ∀ a b : A, H.Adj a b → G.Adj (f a) (f b))
    (hreflect : ∀ a b : A, G.Adj (f a) (f b) → H.Adj a b)
    (hrootInj : Function.Injective root)
    (hroot : ∀ r, root r ∈ P)
    (hout : ∀ a : A, f a ∉ P) :
    ∃ shift : I, ∃ z : I → V, ∃ E : I → Finset (Sym2 V),
      (∀ i, z i = root (i * shift)) ∧
      (∀ i, E i = compatiblePaddedHostBase G H I f (z i) i) ∧
      IsMultiExteriorHub G z E ∧
      IsPacking G (multiLiftedPacking z E) ∧
      (multiLiftedPacking z E).card +
          ∑ i : I, paddedIncompatCount G H I f (z i) i =
        ∑ i : I, (paddedHostBase H I f i).card ∧
      Fintype.card I * ∑ i : I, (paddedHostBase H I f i).card ≤
        Fintype.card I * (multiLiftedPacking z E).card +
          (H.cliqueNum - 1) * (missingIncidences G root f).card := by
  obtain ⟨hends, hlater, hwidth, hnest⟩ :=
    rooted_order_geometry_cliqueNum (H := H) O f root hroot hout hcore hreflect
  obtain ⟨shift, hs⟩ := exists_shift_paddedIncompat_le f root
    H.cliqueNum (edgeEarlier O f) (edgeLater O f)
    (laterCoreNeighbors O f H) hends hlater hwidth hnest
  let z : I → V := fun i => root (i * shift)
  let E : I → Finset (Sym2 V) := fun i => compatiblePaddedHostBase G H I f (z i) i
  have hzInj : Function.Injective z := by
    intro a b hab
    exact mul_right_cancel (hrootInj hab)
  have hzcore : ∀ (i : I) (a : A), z i ≠ f a := by
    intro i a h
    have hi := hroot (i * shift)
    change root (i * shift) = f a at h
    rw [h] at hi
    exact hout a hi
  have hhub := isMultiExteriorHub_compatiblePaddedHostBase f z hcore hzInj hzcore
  have hpack := isPacking_compatiblePaddedHostBase f z hcore hzInj hzcore
  have hadd := card_paddedPacking_add_incompat f z hcore hzInj hzcore
  refine ⟨shift, z, E, fun _ => rfl, fun _ => rfl, hhub, hpack, hadd, ?_⟩
  calc
    Fintype.card I * ∑ i : I, (paddedHostBase H I f i).card =
        Fintype.card I * (multiLiftedPacking z E).card +
          Fintype.card I * ∑ i : I, paddedIncompatCount G H I f (z i) i := by
      rw [← Nat.mul_add, hadd]
    _ ≤ _ := Nat.add_le_add_left hs _

end Group

end PaperIV.RD09PaddedL1Adapter
