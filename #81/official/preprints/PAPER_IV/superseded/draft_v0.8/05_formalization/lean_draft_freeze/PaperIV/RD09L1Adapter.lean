import PaperIV.RD09LocalPhaseI
import PaperIV.RD09FiniteAveraging

/-!
# RD09-L1: the complete geometric adapter

This module closes the geometric adapter behind the RD09-L1 inequality, *on the literal
types and definitions of `PaperIV.RD09LocalPhaseI`*: the real transported colour classes
`hostBase H f colourOf i`, the real exterior-hub structures `IsExteriorHub` /
`IsMultiExteriorHub`, and the real lift `multiLiftedPacking`.

## The missing datum of phase I

`PaperIV.RD09LocalPhaseI.IsLocalHostConfig` assumes `hostAdj`: *every* host is adjacent to
*every* embedded core vertex.  That hypothesis is exactly what RD09-L1 has to pay for, so
it is **not** used anywhere in this file.  Instead:

* a base edge `e` is *compatible* with a root `r` when both of its endpoints are adjacent
  to `r` (`IsCompatibleBase`);
* `compatibleHostBase` keeps only the compatible part of a transported colour class;
* `incompatCount` counts the discarded bases.

## What is proved

1. **The geometric charging bound** `total_incompat_le_mul_card_missingIncidences`: with a
   minimal PEO/orientation witness on the *actual* core edge type `Sym2 A` (an earlier and
   a later endpoint of each core edge, later endpoints confined to later-neighbour sets of
   size at most `w - 1`, and the PEO nesting condition sending every incompatible
   base/root pair to a missing incidence at the earlier endpoint), the **total** number of
   incompatible selected-class/root incidences is at most `(w - 1) * A`, where `A` is the
   literal number of missing root/core incidences.  This is a theorem, proved by an
   explicit double count; it is not a hypothesis and not a structure field.

2. **Explicit cyclic-shift averaging** `exists_shift_card_mul_incompat_le`: the roots and
   the selected colour classes are indexed by one finite group `Index`, class `i` being
   assigned to root `i * s` for a shift `s`.  Combining 1. with the explicit-shift family
   of `PaperIV.RD09FiniteAveraging` (`shiftCost`, `sum_shiftCost_eq`,
   `exists_shift_card_mul_cost_le_of_total_le`) produces one shift with
   `p * bad ≤ (w - 1) * A`, `p = Fintype.card Index`.  No averaging over permutations.

3. **The filtered phase-I data is literal hub data**
   `isMultiExteriorHub_compatibleHostBase`, hence
   `isPacking_multiLiftedPacking_compatibleHostBase` is a literal
   `PaperIV.Model.IsPacking` of `multiLiftedPacking`.

4. **Exact cardinality** `card_multiLiftedPacking_compatibleHostBase` and the integral
   RD09-L1 ledger `rd09L1_ledger`
   (`p * selectedTotal ≤ p * keptTotal + (w - 1) * A`), with the divided rational form
   `rd09L1_ledger_div` as a corollary.
-/

namespace PaperIV.RD09L1Adapter

open Finset PaperIV.Model PaperIV.ColourClasses PaperIV.ExteriorTriangleLift
open PaperIV.MultiHostTriangleLift PaperIV.TransportedMatchings
open PaperIV.RD09LocalPhaseI PaperIV.RD09FiniteAveraging

variable {V A : Type*} [Fintype V] [DecidableEq V] [Fintype A] [DecidableEq A]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {H : SimpleGraph A} [DecidableRel H.Adj]
variable {I : Type*} [Fintype I] [DecidableEq I]

/-! ## Compatibility of a transported base with an assigned root -/

/-- A transported base edge `e` is *compatible* with the root `r` when `r` is adjacent to
both endpoints of `e`.  This is precisely the `hubAdj` requirement of
`PaperIV.ExteriorTriangleLift.IsExteriorHub`, localized to a single base edge; it is the
datum that `IsLocalHostConfig.hostAdj` would grant for free. -/
def IsCompatibleBase (G : SimpleGraph V) [DecidableRel G.Adj] (r : V) (e : Sym2 V) : Prop :=
  ∀ x ∈ e.toFinset, G.Adj r x

instance instDecidableIsCompatibleBase (G : SimpleGraph V) [DecidableRel G.Adj] (r : V) :
    DecidablePred (IsCompatibleBase G r) := fun e =>
  inferInstanceAs (Decidable (∀ x ∈ e.toFinset, G.Adj r x))

omit [Fintype V] in
theorem isCompatibleBase_iff {r : V} {e : Sym2 V} :
    IsCompatibleBase G r e ↔ ∀ x ∈ e, G.Adj r x := by
  simp [IsCompatibleBase, Sym2.mem_toFinset]

/-- The compatible part of the real transported colour class carried by index `i`, for the
root `r` assigned to it. -/
noncomputable def compatibleHostBase (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : SimpleGraph A) [DecidableRel H.Adj] (f : A ↪ V)
    (colourOf : I → Fin (H.maxDegree + 1)) (r : V) (i : I) : Finset (Sym2 V) :=
  (hostBase H f colourOf i).filter (IsCompatibleBase G r)

omit [Fintype I] [DecidableEq I] in
theorem compatibleHostBase_subset (f : A ↪ V) (colourOf : I → Fin (H.maxDegree + 1))
    (r : V) (i : I) :
    compatibleHostBase G H f colourOf r i ⊆ hostBase H f colourOf i :=
  Finset.filter_subset _ _

omit [Fintype I] [DecidableEq I] in
theorem mem_compatibleHostBase {f : A ↪ V} {colourOf : I → Fin (H.maxDegree + 1)}
    {r : V} {i : I} {e : Sym2 V} :
    e ∈ compatibleHostBase G H f colourOf r i ↔
      e ∈ hostBase H f colourOf i ∧ ∀ x ∈ e, G.Adj r x := by
  simp [compatibleHostBase, isCompatibleBase_iff]

/-- The number of bases of the transported class `i` that are *incompatible* with the root
`r`, i.e. that have to be discarded. -/
noncomputable def incompatCount (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : SimpleGraph A) [DecidableRel H.Adj] (f : A ↪ V)
    (colourOf : I → Fin (H.maxDegree + 1)) (r : V) (i : I) : ℕ :=
  ((hostBase H f colourOf i).filter fun e => ¬ IsCompatibleBase G r e).card

omit [Fintype I] [DecidableEq I] in
/-- Exact local ledger: kept bases plus discarded bases is the full transported class. -/
theorem card_compatibleHostBase_add_incompatCount (f : A ↪ V)
    (colourOf : I → Fin (H.maxDegree + 1)) (r : V) (i : I) :
    (compatibleHostBase G H f colourOf r i).card + incompatCount G H f colourOf r i
      = (hostBase H f colourOf i).card :=
  Finset.card_filter_add_card_filter_not _

/-! ## The geometric charging bound -/

/-- The literal set of **missing root/core incidences**: pairs `(r, a)` such that the root
`root r` is *not* adjacent to the embedded core vertex `f a`.  Its cardinality is the
quantity `A` of RD09-L1. -/
def missingIncidences (G : SimpleGraph V) [DecidableRel G.Adj] (root : I → V) (f : A ↪ V) :
    Finset (I × A) :=
  Finset.univ.filter fun p => ¬ G.Adj (root p.1) (f p.2)

omit [Fintype V] [DecidableEq V] [DecidableEq A] [DecidableEq I] in
@[simp] theorem mem_missingIncidences {root : I → V} {f : A ↪ V} {p : I × A} :
    p ∈ missingIncidences G root f ↔ ¬ G.Adj (root p.1) (f p.2) := by
  simp [missingIncidences]

/-- The core-side description of the discarded bases of class `i` at root `root r`. -/
noncomputable def badCoreEdges (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : SimpleGraph A) [DecidableRel H.Adj] (f : A ↪ V)
    (colourOf : I → Fin (H.maxDegree + 1)) (root : I → V) (i r : I) : Finset (Sym2 A) :=
  (graphEdges H).filter fun d =>
    localColour H d = colourOf i ∧ ¬ IsCompatibleBase G (root r) (Sym2.map f d)

omit [Fintype I] [DecidableEq I] in
/-- The discarded bases are exactly the images of the discarded *core* edges. -/
theorem incompatCount_eq_card_badCoreEdges (f : A ↪ V)
    (colourOf : I → Fin (H.maxDegree + 1)) (root : I → V) (i r : I) :
    incompatCount G H f colourOf (root r) i
      = (badCoreEdges G H f colourOf root i r).card := by
  classical
  unfold incompatCount hostBase badCoreEdges
  rw [mapColourClass, Finset.filter_image,
    Finset.card_image_of_injective _ (Sym2.map.injective f.injective), colourClass,
    Finset.filter_filter]

/-- The total collection of incompatible class/root incidences, as one literal finite set
of triples `⟨(class, root), core edge⟩`. -/
noncomputable def badIncidences (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : SimpleGraph A) [DecidableRel H.Adj] (f : A ↪ V)
    (colourOf : I → Fin (H.maxDegree + 1)) (root : I → V) : Finset ((_ : I × I) × Sym2 A) :=
  (Finset.univ : Finset (I × I)).sigma fun p => badCoreEdges G H f colourOf root p.1 p.2

omit [DecidableEq I] in
theorem card_badIncidences (f : A ↪ V) (colourOf : I → Fin (H.maxDegree + 1))
    (root : I → V) :
    (badIncidences G H f colourOf root).card
      = ∑ i : I, ∑ r : I, incompatCount G H f colourOf (root r) i := by
  rw [badIncidences, Finset.card_sigma, Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun r _ =>
    (incompatCount_eq_card_badCoreEdges f colourOf root i r).symm

omit [DecidableEq I] in
/-- **The geometric charging lemma behind RD09-L1.**

Hypotheses are a minimal PEO/orientation witness on the *actual* core edge type `Sym2 A`:

* `hends` : every core edge is spanned by its earlier and its later endpoint;
* `hlater` : the later endpoint lies in a finite later-neighbour set of the earlier one;
* `hwidth` : every later-neighbour set has at most `w - 1` elements;
* `hnest` : the PEO nesting condition — whenever a transported core edge is incompatible
  with a root, the incidence `(root, earlier endpoint)` is already missing.

Conclusion: the **total** number of incompatible selected-class/root incidences is at most
`(w - 1) * A`, with `A` the literal number of missing root/core incidences.  Each
incompatible incidence is charged to the missing incidence at the earlier endpoint of its
core edge; a missing incidence `(r, u)` receives at most one charge per later neighbour of
`u`, because the core edge is `s(u, v)` and the class index is then determined by
injectivity of `colourOf`. -/
theorem total_incompat_le_mul_card_missingIncidences (f : A ↪ V)
    (colourOf : I → Fin (H.maxDegree + 1)) (root : I → V)
    (hcolourInj : Function.Injective colourOf)
    (w : ℕ) (earlier later : Sym2 A → A) (laterNbr : A → Finset A)
    (hends : ∀ d ∈ graphEdges H, d = s(earlier d, later d))
    (hlater : ∀ d ∈ graphEdges H, later d ∈ laterNbr (earlier d))
    (hwidth : ∀ a : A, (laterNbr a).card ≤ w - 1)
    (hnest : ∀ (r : I), ∀ d ∈ graphEdges H,
      ¬ IsCompatibleBase G (root r) (Sym2.map f d) → ¬ G.Adj (root r) (f (earlier d))) :
    (∑ i : I, ∑ r : I, incompatCount G H f colourOf (root r) i)
      ≤ (w - 1) * (missingIncidences G root f).card := by
  classical
  rw [← card_badIncidences f colourOf root]
  set T : Finset ((_ : I × A) × A) :=
    (missingIncidences G root f).sigma fun p => laterNbr p.2 with hT
  have hcharge : (badIncidences G H f colourOf root).card ≤ T.card := by
    refine Finset.card_le_card_of_injOn
      (fun x => ⟨(x.1.2, earlier x.2), later x.2⟩) ?_ ?_
    · rintro ⟨⟨i, r⟩, d⟩ hx
      simp only [Finset.mem_coe, badIncidences, Finset.mem_sigma, Finset.mem_univ, true_and,
        badCoreEdges, Finset.mem_filter] at hx
      obtain ⟨hd, -, hbad⟩ := hx
      simp only [hT, Finset.mem_coe, Finset.mem_sigma, mem_missingIncidences]
      exact ⟨hnest r d hd hbad, hlater d hd⟩
    · rintro ⟨⟨i, r⟩, d⟩ hx ⟨⟨i', r'⟩, d'⟩ hy hxy
      simp only [Finset.mem_coe, badIncidences, Finset.mem_sigma, Finset.mem_univ, true_and,
        badCoreEdges, Finset.mem_filter] at hx hy
      obtain ⟨hd, hci, -⟩ := hx
      obtain ⟨hd', hci', -⟩ := hy
      simp only [Sigma.mk.injEq, Prod.mk.injEq, heq_eq_eq] at hxy
      obtain ⟨⟨hr, hearl⟩, hlat⟩ := hxy
      subst hr
      have hdd : d = d' := by
        rw [hends d hd, hends d' hd', hearl, hlat]
      subst hdd
      have : i = i' := hcolourInj (hci.symm.trans hci')
      subst this
      rfl
  refine hcharge.trans ?_
  rw [hT, Finset.card_sigma]
  calc ∑ p ∈ missingIncidences G root f, (laterNbr p.2).card
      ≤ ∑ _p ∈ missingIncidences G root f, (w - 1) :=
        Finset.sum_le_sum fun p _ => hwidth p.2
    _ = (w - 1) * (missingIncidences G root f).card := by
        rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]

/-! ## The explicit cyclic-shift averaging step

Roots and selected colour classes are indexed by one finite group `Index`; the shift `s`
assigns class `i` to root `i * s`.  Only the `Fintype.card Index` explicit translations are
used — never the factorial family of all bijections. -/

section Shift

variable {Index : Type*} [Fintype Index] [DecidableEq Index] [Nonempty Index] [Group Index]

omit [DecidableEq Index] in
/-- **Explicit-shift existence.**  Combining the geometric charging bound with the
group-translation averaging certificate of `PaperIV.RD09FiniteAveraging` yields one shift
`s` whose total incompatibility cost satisfies the cross-multiplied RD09-L1 bound
`p * bad ≤ (w - 1) * A` with `p = Fintype.card Index`. -/
theorem exists_shift_card_mul_incompat_le (f : A ↪ V)
    (colourOf : Index → Fin (H.maxDegree + 1)) (root : Index → V)
    (hcolourInj : Function.Injective colourOf)
    (w : ℕ) (earlier later : Sym2 A → A) (laterNbr : A → Finset A)
    (hends : ∀ d ∈ graphEdges H, d = s(earlier d, later d))
    (hlater : ∀ d ∈ graphEdges H, later d ∈ laterNbr (earlier d))
    (hwidth : ∀ a : A, (laterNbr a).card ≤ w - 1)
    (hnest : ∀ (r : Index), ∀ d ∈ graphEdges H,
      ¬ IsCompatibleBase G (root r) (Sym2.map f d) → ¬ G.Adj (root r) (f (earlier d))) :
    ∃ s : Index,
      Fintype.card Index * (∑ i : Index, incompatCount G H f colourOf (root (i * s)) i)
        ≤ (w - 1) * (missingIncidences G root f).card := by
  classical
  obtain ⟨s, hs⟩ :=
    exists_shift_card_mul_cost_le_of_total_le
      (fun i r => incompatCount G H f colourOf (root r) i)
      ((w - 1) * (missingIncidences G root f).card)
      (total_incompat_le_mul_card_missingIncidences f colourOf root hcolourInj w
        earlier later laterNbr hends hlater hwidth hnest)
  exact ⟨s, by simpa [shiftCost] using hs⟩

end Shift

/-! ## The filtered transported classes are literal exterior-hub data

Note that `IsLocalHostConfig.hostAdj` is *not* available here: adjacency of a host to the
endpoints of its bases is supplied edge by edge, by the compatibility filter. -/

omit [Fintype I] [DecidableEq I] in
/-- Each filtered class consists of literal edges of `G`; this uses only the
adjacency-preserving core embedding (a hypothesis-generalized form of
`RD09LocalPhaseI.hostBase_subset_graphEdges`). -/
theorem hostBase_subset_graphEdges_of_coreHom {f : A ↪ V}
    {colourOf : I → Fin (H.maxDegree + 1)}
    (hcore : ∀ a b : A, H.Adj a b → G.Adj (f a) (f b)) (i : I) :
    hostBase H f colourOf i ⊆ graphEdges G := by
  intro e he
  obtain ⟨d, hd, -, rfl⟩ := mem_hostBase.mp he
  exact mem_graphEdges_map hcore hd

omit [Fintype V] [Fintype I] [DecidableEq I] in
/-- Distinct indices carry distinct local colours, hence disjoint transported classes: a
hypothesis-generalized form of `RD09LocalPhaseI.disjoint_hostBase`. -/
theorem disjoint_hostBase_of_colourInj {f : A ↪ V} {colourOf : I → Fin (H.maxDegree + 1)}
    (hcolourInj : Function.Injective colourOf) {i j : I} (hij : i ≠ j) :
    Disjoint (hostBase H f colourOf i) (hostBase H f colourOf j) :=
  disjoint_mapColourClass fun hc => hij (hcolourInj hc)

omit [Fintype I] [DecidableEq I] in
/-- Each host is a literal exterior hub for its *filtered* transported class. -/
theorem isExteriorHub_compatibleHostBase {f : A ↪ V}
    {colourOf : I → Fin (H.maxDegree + 1)} {z : I → V}
    (hcore : ∀ a b : A, H.Adj a b → G.Adj (f a) (f b)) (i : I) :
    IsExteriorHub G (z i) (compatibleHostBase G H f colourOf (z i) i) where
  edges := fun _ he =>
    hostBase_subset_graphEdges_of_coreHom hcore i (compatibleHostBase_subset f colourOf _ i he)
  matching := fun e he g hg hne =>
    isLiteralMatching_hostBase (H := H) i e (compatibleHostBase_subset f colourOf _ i he)
      g (compatibleHostBase_subset f colourOf _ i hg) hne
  hubAdj := fun _ he x hx => (mem_compatibleHostBase.mp he).2 x hx

omit [Fintype I] [DecidableEq I] in
/-- **The filtered phase-I data is multi-exterior-hub data.**  No global host/core
adjacency is assumed: only the adjacency-preserving core embedding, injectivity of the
host assignment and of the colour assignment, and the exteriority of the hosts. -/
theorem isMultiExteriorHub_compatibleHostBase {f : A ↪ V}
    {colourOf : I → Fin (H.maxDegree + 1)} {z : I → V}
    (hcore : ∀ a b : A, H.Adj a b → G.Adj (f a) (f b))
    (hzInj : Function.Injective z)
    (hcolourInj : Function.Injective colourOf)
    (hzcore : ∀ (i : I) (a : A), z i ≠ f a) :
    IsMultiExteriorHub G z (fun i => compatibleHostBase G H f colourOf (z i) i) where
  hub := isExteriorHub_compatibleHostBase hcore
  hostInj := hzInj
  exterior := by
    intro i j e he x hx
    obtain ⟨a, rfl⟩ :=
      exists_core_of_mem_hostBase (compatibleHostBase_subset f colourOf _ i he) hx
    exact fun hz => hzcore j a hz.symm
  baseDisjoint := fun i j hij =>
    (disjoint_hostBase_of_colourInj hcolourInj hij).mono
      (compatibleHostBase_subset f colourOf _ i) (compatibleHostBase_subset f colourOf _ j)

/-- **The filtered phase-I lift is a literal packing.** -/
theorem isPacking_multiLiftedPacking_compatibleHostBase {f : A ↪ V}
    {colourOf : I → Fin (H.maxDegree + 1)} {z : I → V}
    (hcore : ∀ a b : A, H.Adj a b → G.Adj (f a) (f b))
    (hzInj : Function.Injective z)
    (hcolourInj : Function.Injective colourOf)
    (hzcore : ∀ (i : I) (a : A), z i ≠ f a) :
    IsPacking G (multiLiftedPacking z fun i => compatibleHostBase G H f colourOf (z i) i) :=
  isPacking_multiLiftedPacking
    (isMultiExteriorHub_compatibleHostBase hcore hzInj hcolourInj hzcore)

omit [DecidableEq I] in
/-- **Exact cardinality of the filtered phase-I packing**: the total number of selected
bases minus the discarded incompatibilities, in exact additive form. -/
theorem card_multiLiftedPacking_compatibleHostBase {f : A ↪ V}
    {colourOf : I → Fin (H.maxDegree + 1)} {z : I → V}
    (hcore : ∀ a b : A, H.Adj a b → G.Adj (f a) (f b))
    (hzInj : Function.Injective z)
    (hcolourInj : Function.Injective colourOf)
    (hzcore : ∀ (i : I) (a : A), z i ≠ f a) :
    (multiLiftedPacking z fun i => compatibleHostBase G H f colourOf (z i) i).card
        + ∑ i : I, incompatCount G H f colourOf (z i) i
      = ∑ i : I, (hostBase H f colourOf i).card
    ∧ (multiLiftedPacking z fun i => compatibleHostBase G H f colourOf (z i) i).card
      = (∑ i : I, (hostBase H f colourOf i).card)
          - ∑ i : I, incompatCount G H f colourOf (z i) i := by
  have hcard :
      (multiLiftedPacking z fun i => compatibleHostBase G H f colourOf (z i) i).card
        = ∑ i : I, (compatibleHostBase G H f colourOf (z i) i).card :=
    card_multiLiftedPacking
      (isMultiExteriorHub_compatibleHostBase hcore hzInj hcolourInj hzcore)
  have hsum :
      (∑ i : I, (compatibleHostBase G H f colourOf (z i) i).card)
          + ∑ i : I, incompatCount G H f colourOf (z i) i
        = ∑ i : I, (hostBase H f colourOf i).card := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ =>
      card_compatibleHostBase_add_incompatCount f colourOf (z i) i
  refine ⟨by rw [hcard]; exact hsum, ?_⟩
  omega

/-! ## The RD09-L1 ledger -/

section Ledger

variable {Index : Type*} [Fintype Index] [DecidableEq Index] [Nonempty Index] [Group Index]

/-- **RD09-L1, complete geometric adapter.**

Data: an adjacency-preserving core embedding `f`, an injective family of roots
`root : Index → V` exterior to the embedded core, an injective assignment `colourOf` of
local Vizing colours of the core to the index group, and a minimal PEO/orientation witness
on the core edge type `Sym2 A` with width `w`.

Conclusion: there is an explicit group shift `s` — the class `i` being assigned to the
root `i * s` — such that, after discarding exactly the bases incompatible with their
assigned root,

* the shifted hosts and the filtered transported classes are literal
  `IsMultiExteriorHub` data, so their lift is a literal `IsPacking`;
* the packing has exactly `selectedTotal - discarded` pieces (also in additive form);
* the integral cross-multiplied RD09-L1 ledger holds:
  `p * selectedTotal ≤ p * keptTotal + (w - 1) * A`, where `p = Fintype.card Index`,
  `A = (missingIncidences G root f).card`, and `keptTotal` is the cardinality of the
  packing.

Nothing here uses `IsLocalHostConfig.hostAdj`; the incompatibility count is genuine. -/
theorem rd09L1_ledger (f : A ↪ V) (colourOf : Index → Fin (H.maxDegree + 1))
    (root : Index → V)
    (hcore : ∀ a b : A, H.Adj a b → G.Adj (f a) (f b))
    (hrootInj : Function.Injective root)
    (hcolourInj : Function.Injective colourOf)
    (hrootcore : ∀ (r : Index) (a : A), root r ≠ f a)
    (w : ℕ) (earlier later : Sym2 A → A) (laterNbr : A → Finset A)
    (hends : ∀ d ∈ graphEdges H, d = s(earlier d, later d))
    (hlater : ∀ d ∈ graphEdges H, later d ∈ laterNbr (earlier d))
    (hwidth : ∀ a : A, (laterNbr a).card ≤ w - 1)
    (hnest : ∀ (r : Index), ∀ d ∈ graphEdges H,
      ¬ IsCompatibleBase G (root r) (Sym2.map f d) → ¬ G.Adj (root r) (f (earlier d))) :
    ∃ s : Index,
      ∃ z : Index → V, ∃ E : Index → Finset (Sym2 V),
        (∀ i, z i = root (i * s)) ∧
        (∀ i, E i = compatibleHostBase G H f colourOf (z i) i) ∧
        (∀ i, E i ⊆ hostBase H f colourOf i) ∧
        IsMultiExteriorHub G z E ∧
        IsPacking G (multiLiftedPacking z E) ∧
        (multiLiftedPacking z E).card
            + ∑ i : Index, incompatCount G H f colourOf (z i) i
          = ∑ i : Index, (hostBase H f colourOf i).card ∧
        (multiLiftedPacking z E).card
          = (∑ i : Index, (hostBase H f colourOf i).card)
              - ∑ i : Index, incompatCount G H f colourOf (z i) i ∧
        Fintype.card Index * ∑ i : Index, (hostBase H f colourOf i).card
          ≤ Fintype.card Index * (multiLiftedPacking z E).card
              + (w - 1) * (missingIncidences G root f).card := by
  classical
  obtain ⟨s, hs⟩ :=
    exists_shift_card_mul_incompat_le f colourOf root hcolourInj w earlier later laterNbr
      hends hlater hwidth hnest
  refine ⟨s, fun i => root (i * s),
    fun i => compatibleHostBase G H f colourOf (root (i * s)) i,
    fun _ => rfl, fun _ => rfl, fun i => compatibleHostBase_subset f colourOf _ i, ?_, ?_,
    ?_, ?_, ?_⟩
  · exact isMultiExteriorHub_compatibleHostBase hcore
      (fun a b hab => mul_right_cancel (hrootInj hab)) hcolourInj
      (fun i a => hrootcore (i * s) a)
  · exact isPacking_multiLiftedPacking_compatibleHostBase hcore
      (fun a b hab => mul_right_cancel (hrootInj hab)) hcolourInj
      (fun i a => hrootcore (i * s) a)
  · exact (card_multiLiftedPacking_compatibleHostBase hcore
      (fun a b hab => mul_right_cancel (hrootInj hab)) hcolourInj
      (fun i a => hrootcore (i * s) a)).1
  · exact (card_multiLiftedPacking_compatibleHostBase hcore
      (fun a b hab => mul_right_cancel (hrootInj hab)) hcolourInj
      (fun i a => hrootcore (i * s) a)).2
  · have hadd := (card_multiLiftedPacking_compatibleHostBase (z := fun i => root (i * s))
      hcore (fun a b hab => mul_right_cancel (hrootInj hab)) hcolourInj
      (fun i a => hrootcore (i * s) a)).1
    calc Fintype.card Index * ∑ i : Index, (hostBase H f colourOf i).card
        = Fintype.card Index *
            (multiLiftedPacking (fun i => root (i * s))
              (fun i => compatibleHostBase G H f colourOf (root (i * s)) i)).card
          + Fintype.card Index *
            ∑ i : Index, incompatCount G H f colourOf (root (i * s)) i := by
          rw [← Nat.mul_add, hadd]
      _ ≤ _ := Nat.add_le_add_left hs _

/-- Divided rational form of the RD09-L1 ledger: the number of selected bases exceeds the
size of the constructed packing by at most `(w - 1) * A / p`. -/
theorem rd09L1_ledger_div (f : A ↪ V) (colourOf : Index → Fin (H.maxDegree + 1))
    (root : Index → V)
    (hcore : ∀ a b : A, H.Adj a b → G.Adj (f a) (f b))
    (hrootInj : Function.Injective root)
    (hcolourInj : Function.Injective colourOf)
    (hrootcore : ∀ (r : Index) (a : A), root r ≠ f a)
    (w : ℕ) (earlier later : Sym2 A → A) (laterNbr : A → Finset A)
    (hends : ∀ d ∈ graphEdges H, d = s(earlier d, later d))
    (hlater : ∀ d ∈ graphEdges H, later d ∈ laterNbr (earlier d))
    (hwidth : ∀ a : A, (laterNbr a).card ≤ w - 1)
    (hnest : ∀ (r : Index), ∀ d ∈ graphEdges H,
      ¬ IsCompatibleBase G (root r) (Sym2.map f d) → ¬ G.Adj (root r) (f (earlier d))) :
    ∃ z : Index → V, ∃ E : Index → Finset (Sym2 V),
      IsMultiExteriorHub G z E ∧ IsPacking G (multiLiftedPacking z E) ∧
      ((∑ i : Index, (hostBase H f colourOf i).card : ℚ)
        ≤ (multiLiftedPacking z E).card
            + ((w - 1) * (missingIncidences G root f).card : ℕ) / Fintype.card Index) := by
  obtain ⟨_, z, E, -, -, -, hhub, hpack, -, -, hledger⟩ :=
    rd09L1_ledger f colourOf root hcore hrootInj hcolourInj hrootcore w earlier later
      laterNbr hends hlater hwidth hnest
  refine ⟨z, E, hhub, hpack, ?_⟩
  have hp : (0 : ℚ) < Fintype.card Index := by
    exact_mod_cast Fintype.card_pos
  rw [← sub_le_iff_le_add', le_div_iff₀ hp]
  have := (Nat.cast_le (α := ℚ)).2 hledger
  push_cast at this ⊢
  nlinarith [this]

end Ledger


/-! ## Non-vacuity

A concrete instance with a *genuine* missing incidence: the graph on seven vertices which
is complete except that the root `1` is **not** adjacent to the core vertex `4`.  The core
is the single-edge core of `RD09LocalPhaseI.Example`, embedded onto `{4, 5}`; the index
group is the cyclic group `Multiplicative (ZMod 2)`, whose two elements label the two
roots `0`, `1` and the two local colours.  Every hypothesis of the adapter holds, the
PEO/orientation witness is the obvious one, and the class assigned to root `1` really does
have an incompatible base, so the incompatibility count is not identically zero. -/

namespace Example

open PaperIV.RD09LocalPhaseI.Example

/-- The ambient graph: `K₇` minus the single edge `s(1, 4)`. -/
def graph7 : SimpleGraph (Fin 7) where
  Adj a b := a ≠ b ∧ ¬ (a = 1 ∧ b = 4) ∧ ¬ (a = 4 ∧ b = 1)
  symm := by
    intro a b h
    exact ⟨h.1.symm, fun hh => h.2.2 ⟨hh.2, hh.1⟩, fun hh => h.2.1 ⟨hh.2, hh.1⟩⟩
  loopless := ⟨fun a h => h.1 rfl⟩

instance : DecidableRel graph7.Adj := fun a b =>
  inferInstanceAs (Decidable (a ≠ b ∧ ¬ (a = 1 ∧ b = 4) ∧ ¬ (a = 4 ∧ b = 1)))

/-- The index group: the cyclic group with two elements. -/
abbrev Idx := Multiplicative (ZMod 2)

/-- The two roots. -/
def roots : Idx → Fin 7 := fun i => if Multiplicative.toAdd i = 0 then 0 else 1

/-- The two selected local colours of the core. -/
def colours : Idx → Fin (core.maxDegree + 1) :=
  fun i => if Multiplicative.toAdd i = 0 then ⟨0, Nat.succ_pos _⟩
    else ⟨1, by rw [core_maxDegree]; omega⟩

/-- The orientation: the unique core edge `s(0, 1)` is oriented from `0` to `1`. -/
def earlierPt : Sym2 (Fin 2) → Fin 2 := fun _ => 0
/-- The later endpoint of the unique core edge. -/
def laterPt : Sym2 (Fin 2) → Fin 2 := fun _ => 1
/-- The later-neighbour sets: at most `w - 1 = 1` later neighbour. -/
def laterNbrs : Fin 2 → Finset (Fin 2) := fun _ => {1}

theorem roots_injective : Function.Injective roots := by decide
theorem colours_injective : Function.Injective colours := by decide

/-- The root `1` is genuinely non-adjacent to the core vertex `coreEmb 0 = 4`: the missing
incidence set is nonempty, so this instance is not one in which every base is
automatically compatible. -/
theorem missingIncidences_nonempty :
    (missingIncidences graph7 roots coreEmb).Nonempty := by decide

/-- Every hypothesis of the adapter holds here, so the RD09-L1 ledger applies. -/
theorem rd09L1_ledger_example :
    ∃ z : Idx → Fin 7, ∃ E : Idx → Finset (Sym2 (Fin 7)),
      IsMultiExteriorHub graph7 z E ∧ IsPacking graph7 (multiLiftedPacking z E) ∧
      Fintype.card Idx * ∑ i : Idx, (hostBase core coreEmb colours i).card
        ≤ Fintype.card Idx * (multiLiftedPacking z E).card
            + (2 - 1) * (missingIncidences graph7 roots coreEmb).card := by
  obtain ⟨_, z, E, -, -, -, hhub, hpack, -, -, hledger⟩ :=
    rd09L1_ledger (G := graph7) (H := core) coreEmb colours roots
      (by decide) roots_injective colours_injective (by decide)
      2 earlierPt laterPt laterNbrs (by decide) (by decide) (by decide) (by decide)
  exact ⟨z, E, hhub, hpack, hledger⟩

end Example

end PaperIV.RD09L1Adapter

