import PaperIV.EquitableKempe
import PaperIV.RD09RootFactorPhase

/-!
# RD09 local phase I: equitable Vizing colouring as literal exterior-hub data

This module closes the first genuinely combinatorial step of the RD09 local constructor.
It turns the *unconditional* equitable Vizing colouring produced by
`PaperIV.EquitableKempe.equitableVizingBoundedColouring` into literal phase-I host data
`(z, E)` satisfying `PaperIV.MultiHostTriangleLift.IsMultiExteriorHub`, for the concrete
local split/root configuration of `PaperIV.RD09RootFactorPhase`.

## The local configuration

The data is exactly the geometric configuration used by RD09 near the critical root branch:

* a **core** graph `H` on an abstract label type `A`, embedded into the physical vertex
  type by `f : A ↪ V` in an adjacency-preserving way (`coreHom`);
* a family of **exterior hosts** `z : I → V`, pairwise distinct (`hostInj`), each adjacent
  to every embedded core vertex (`hostAdj`);
* an injective assignment `colourOf : I → Fin (H.maxDegree + 1)` of one Vizing colour of
  the core to each host (`colourInj`).

No other datum is assumed.  In particular **the colouring itself is not a hypothesis**: it
is the unconditional output of `equitableVizingBoundedColouring H`, and the phase-I base
families are the literal transported colour classes

`hostBase H f colourOf i = TransportedMatchings.mapColourClass f (graphEdges H) (localColour H) (colourOf i)`.

## What is proved

`isMultiExteriorHub_hostBase` : the transported classes *are* multi-exterior-hub data.
`exists_multiExteriorHub_of_critical_root` : the packaged phase-I statement for the RD09
root-factor configuration, with explicit `z` and `E`, host injectivity, edge-disjoint base
classes, cross-host resource disjointness, literal triangle membership, the class-size
bound inherited from equitability, and the exact phase-I cardinality and gain ledgers —
together with the compatibility (`IsRootHostSeparated`) and the ledgers of the union with
the RD09 phase-II root-factor packing.

The separation structure `IsLocalRootSeparated` records the two literal disjointness facts
of the local split configuration (hosts and core lie outside the root/hub pool); every
cross-phase compatibility statement is *derived* from them, never assumed.

See `docs/RD09_LOCAL_PHASE_I.md` for the remaining (global) missing datum.
-/

namespace PaperIV.RD09LocalPhaseI

open Finset PaperIV.Model PaperIV.ColourClasses PaperIV.EquitableEdgeColouring
open PaperIV.ExteriorTriangleLift PaperIV.MultiHostTriangleLift
open PaperIV.TransportedMatchings PaperIV.RD09PhaseII PaperIV.RD09RootFactorPhase

section LocalColouring

variable {V A I : Type*} [DecidableEq V] [Fintype A] [DecidableEq A]
variable {H : SimpleGraph A} [DecidableRel H.Adj]

/-! ## The unconditional local colouring -/

/-- The equitable proper Vizing colouring of the core graph, from
`PaperIV.EquitableKempe.equitableVizingBoundedColouring`.  It is unconditional: no
colouring is ever assumed by this module. -/
noncomputable def localColour (H : SimpleGraph A) [DecidableRel H.Adj] :
    Sym2 A → Fin (H.maxDegree + 1) :=
  (PaperIV.EquitableKempe.equitableVizingBoundedColouring H).colour

theorem localColour_proper (H : SimpleGraph A) [DecidableRel H.Adj] :
    ProperOn (graphEdges H) (localColour H) :=
  (PaperIV.EquitableKempe.equitableVizingBoundedColouring H).proper

/-- Equitability of the local colouring, in the form actually consumed downstream: every
class is at most the ceiling of the average class size. -/
theorem card_colourClass_localColour_le (H : SimpleGraph A) [DecidableRel H.Adj]
    (c : Fin (H.maxDegree + 1)) :
    (colourClass (graphEdges H) (localColour H) c).card
      ≤ classCeiling (graphEdges H).card (H.maxDegree + 1) :=
  (PaperIV.EquitableKempe.equitableVizingBoundedColouring H).class_card_le c

/-- The literal phase-I base family carried by the host with index `i`: the physical image
of the local colour class `colourOf i`. -/
noncomputable def hostBase (H : SimpleGraph A) [DecidableRel H.Adj] (f : A ↪ V)
    (colourOf : I → Fin (H.maxDegree + 1)) (i : I) : Finset (Sym2 V) :=
  mapColourClass f (graphEdges H) (localColour H) (colourOf i)

theorem mem_hostBase {f : A ↪ V} {colourOf : I → Fin (H.maxDegree + 1)} {i : I}
    {e : Sym2 V} :
    e ∈ hostBase H f colourOf i ↔
      ∃ d ∈ graphEdges H, localColour H d = colourOf i ∧ Sym2.map f d = e :=
  mem_mapColourClass

/-- Exact size of a phase-I base family: it is the size of its local colour class. -/
theorem card_hostBase (f : A ↪ V) (colourOf : I → Fin (H.maxDegree + 1)) (i : I) :
    (hostBase H f colourOf i).card
      = (colourClass (graphEdges H) (localColour H) (colourOf i)).card :=
  card_mapColourClass _ _ _

/-- **Class-size bound inherited from equitability.** -/
theorem card_hostBase_le (f : A ↪ V) (colourOf : I → Fin (H.maxDegree + 1)) (i : I) :
    (hostBase H f colourOf i).card ≤ classCeiling (graphEdges H).card (H.maxDegree + 1) := by
  rw [card_hostBase]
  exact card_colourClass_localColour_le H _

end LocalColouring

/-! ## The local split/host configuration -/

variable {V A : Type*} [Fintype V] [DecidableEq V] [Fintype A] [DecidableEq A]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {H : SimpleGraph A} [DecidableRel H.Adj]
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The literal local configuration of RD09 phase I: an adjacency-preserving embedding of
the core graph, pairwise distinct exterior hosts complete to the embedded core, and an
injective assignment of local colours to hosts. -/
structure IsLocalHostConfig (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : SimpleGraph A) [DecidableRel H.Adj] (f : A ↪ V) (z : I → V)
    (colourOf : I → Fin (H.maxDegree + 1)) : Prop where
  /-- the embedding of the core into the physical graph preserves adjacency -/
  coreHom : ∀ a b : A, H.Adj a b → G.Adj (f a) (f b)
  /-- the hosts are pairwise distinct -/
  hostInj : Function.Injective z
  /-- every host is adjacent to every embedded core vertex -/
  hostAdj : ∀ (i : I) (a : A), G.Adj (z i) (f a)
  /-- distinct hosts carry distinct local colours -/
  colourInj : Function.Injective colourOf

variable {f : A ↪ V} {z : I → V} {colourOf : I → Fin (H.maxDegree + 1)}

omit [DecidableEq V] [DecidableEq A] [Fintype I] [DecidableEq I] in
/-- The physical image of a core edge is a physical edge. -/
theorem mem_graphEdges_map (hhom : ∀ a b : A, H.Adj a b → G.Adj (f a) (f b))
    {d : Sym2 A} (hd : d ∈ graphEdges H) : Sym2.map f d ∈ graphEdges G := by
  induction d with
  | _ a b =>
    rw [mem_graphEdges, SimpleGraph.mem_edgeSet] at hd
    simpa using hhom a b hd

omit [Fintype V] [Fintype I] [DecidableEq I] in
/-- Every vertex of a phase-I base edge is an embedded core vertex. -/
theorem exists_core_of_mem_hostBase {i : I} {e : Sym2 V} (he : e ∈ hostBase H f colourOf i)
    {x : V} (hx : x ∈ e) : ∃ a : A, f a = x := by
  obtain ⟨d, -, -, rfl⟩ := mem_hostBase.mp he
  obtain ⟨a, -, hax⟩ := Sym2.mem_map.mp hx
  exact ⟨a, hax⟩

omit [Fintype I] [DecidableEq I] in
/-- Each phase-I base family consists of physical edges of `G`. -/
theorem hostBase_subset_graphEdges (hcfg : IsLocalHostConfig G H f z colourOf) (i : I) :
    hostBase H f colourOf i ⊆ graphEdges G := by
  intro e he
  obtain ⟨d, hd, -, rfl⟩ := mem_hostBase.mp he
  exact mem_graphEdges_map hcfg.coreHom hd

omit [Fintype V] [Fintype I] [DecidableEq I] in
/-- Each phase-I base family is a literal matching: this is exactly properness of the
local Vizing colouring, transported along `f`. -/
theorem isLiteralMatching_hostBase (i : I) :
    IsLiteralMatching (hostBase H f colourOf i) := by
  have hpd := mapColourClass_pairwiseDisjoint_toFinset (f := f)
    (localColour_proper H) (colourOf i)
  intro e he g hg hne
  exact hpd (by simpa [hostBase] using he) (by simpa [hostBase] using hg) hne

omit [Fintype I] [DecidableEq I] in
/-- Each host is an exterior hub for its own transported colour class. -/
theorem isExteriorHub_hostBase (hcfg : IsLocalHostConfig G H f z colourOf) (i : I) :
    IsExteriorHub G (z i) (hostBase H f colourOf i) where
  edges := fun _ he => hostBase_subset_graphEdges hcfg i he
  matching := isLiteralMatching_hostBase i
  hubAdj := by
    intro e he x hx
    obtain ⟨a, rfl⟩ := exists_core_of_mem_hostBase he hx
    exact hcfg.hostAdj i a

omit [Fintype V] [Fintype I] [DecidableEq I] in
/-- **Edge-disjoint base classes.**  Distinct hosts carry distinct local colours, hence
literally disjoint transported classes. -/
theorem disjoint_hostBase (hcfg : IsLocalHostConfig G H f z colourOf) {i j : I} (hij : i ≠ j) :
    Disjoint (hostBase H f colourOf i) (hostBase H f colourOf j) :=
  disjoint_mapColourClass fun hc => hij (hcfg.colourInj hc)

omit [Fintype I] [DecidableEq I] in
/-- **The phase-I host data of RD09 is multi-exterior-hub data.** -/
theorem isMultiExteriorHub_hostBase (hcfg : IsLocalHostConfig G H f z colourOf) :
    IsMultiExteriorHub G z (hostBase H f colourOf) where
  hub := isExteriorHub_hostBase hcfg
  hostInj := hcfg.hostInj
  exterior := by
    intro i j e he x hx
    obtain ⟨a, rfl⟩ := exists_core_of_mem_hostBase he hx
    exact fun hzj => (hcfg.hostAdj j a).ne hzj.symm
  baseDisjoint := fun _ _ hij => disjoint_hostBase hcfg hij

/-! ## Local ledgers of the phase-I packing -/

omit [DecidableEq I] in
/-- **Exact cardinality of the phase-I packing.** -/
theorem card_multiLiftedPacking_hostBase (hcfg : IsLocalHostConfig G H f z colourOf) :
    (multiLiftedPacking z (hostBase H f colourOf)).card
      = ∑ i, (hostBase H f colourOf i).card :=
  card_multiLiftedPacking (isMultiExteriorHub_hostBase hcfg)

omit [DecidableEq I] in
/-- If the hosts are indexed by *all* local colours, the phase-I packing has exactly one
triangle per core edge. -/
theorem card_multiLiftedPacking_eq_card_coreEdges
    (hcfg : IsLocalHostConfig G H f z colourOf) (hsurj : Function.Surjective colourOf) :
    (multiLiftedPacking z (hostBase H f colourOf)).card = (graphEdges H).card := by
  have hbij : Function.Bijective colourOf := ⟨hcfg.colourInj, hsurj⟩
  rw [card_multiLiftedPacking_hostBase hcfg]
  rw [Finset.sum_congr rfl fun i _ => card_hostBase (H := H) f colourOf i]
  rw [Fintype.sum_bijective colourOf hbij _
    (fun c => (colourClass (graphEdges H) (localColour H) c).card) fun _ => rfl]
  exact sum_card_colourClass_univ (graphEdges H) (localColour H)

/-! ## Separation from the root-factor pool -/

variable {J : Type*} [Fintype J] [DecidableEq J]
variable {root : Finset V} {hub : J → Finset V} {base : J → Sym2 V}

/-- The two literal separation facts of the local split configuration: the exterior hosts
and the embedded core both avoid the root/hub pool of the phase-II root factor. -/
structure IsLocalRootSeparated (f : A ↪ V) (z : I → V) (root : Finset V)
    (hub : J → Finset V) : Prop where
  /-- no host lies in the root/hub pool -/
  hostExterior : ∀ i, z i ∉ phaseTwoPool root hub
  /-- no embedded core vertex lies in the root/hub pool -/
  coreExterior : ∀ a : A, f a ∉ phaseTwoPool root hub

omit [Fintype V] [Fintype I] [DecidableEq I] [DecidableEq J] in
/-- The phase-I/phase-II separation of `RD09RootFactorPhase` is *derived* from the local
configuration, not assumed. -/
theorem isRootHostSeparated_hostBase (hsep : IsLocalRootSeparated f z root hub) :
    IsRootHostSeparated z (hostBase H f colourOf) root hub where
  hostExterior := hsep.hostExterior
  baseMeetPool := by
    intro i e he
    have hempty : e.toFinset ∩ phaseTwoPool root hub = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun x hx => ?_
      obtain ⟨hxe, hxp⟩ := Finset.mem_inter.mp hx
      obtain ⟨a, rfl⟩ := exists_core_of_mem_hostBase he (Sym2.mem_toFinset.mp hxe)
      exact hsep.coreExterior a hxp
    simp [hempty]

/-! ## The packaged phase-I statement for the critical root configuration -/

omit [DecidableEq J] in
/-- **RD09 local phase I.**

For the concrete local split/root configuration of RD09 — an adjacency-preserving core
embedding, pairwise distinct exterior hosts complete to the core, an injective assignment
of local colours to hosts, a root-factor family, and the literal separation of hosts and
core from the root/hub pool — the unconditional equitable Vizing colouring of the core
yields *literal* phase-I host data `E` with:

* the explicit description of `E` as transported local colour classes;
* `IsMultiExteriorHub G z E` (so in particular the phase-I lift is a literal packing);
* host injectivity and pairwise edge-disjointness of the base classes;
* cross-host physical resource disjointness of the lifted triangles;
* literal triangle membership: for every base edge `e ∈ E i` the set `triangle (z i) e`
  contains the host and both endpoints of `e`, has exactly three vertices, and belongs to
  the phase-I packing;
* the class-size bound inherited from equitability;
* the exact phase-I ledgers `card = ∑ i, (E i).card` and `totalGain = 2 * ∑ i, (E i).card`;
* compatibility with the RD09 phase-II root factor, together with the exact cardinality of
  the union of the two phases. -/
theorem exists_multiExteriorHub_of_critical_root
    (hcfg : IsLocalHostConfig G H f z colourOf)
    (hroot : IsRootFactorFamily G root hub base)
    (hsep : IsLocalRootSeparated f z root hub) :
    ∃ E : I → Finset (Sym2 V),
      (∀ i, E i = mapColourClass f (graphEdges H) (localColour H) (colourOf i)) ∧
      IsMultiExteriorHub G z E ∧
      Function.Injective z ∧
      (∀ i j, i ≠ j → Disjoint (E i) (E j)) ∧
      (∀ i j, i ≠ j → ∀ e ∈ E i, ∀ g ∈ E j,
        Disjoint (pieceEdges (triangle (z i) e)) (pieceEdges (triangle (z j) g))) ∧
      (∀ i, ∀ e ∈ E i, z i ∈ triangle (z i) e ∧ (∀ a ∈ e, a ∈ triangle (z i) e) ∧
        (triangle (z i) e).card = 3 ∧ triangle (z i) e ∈ multiLiftedPacking z E) ∧
      (∀ i, (E i).card ≤ classCeiling (graphEdges H).card (H.maxDegree + 1)) ∧
      IsPacking G (multiLiftedPacking z E) ∧
      (multiLiftedPacking z E).card = ∑ i, (E i).card ∧
      totalGain (multiLiftedPacking z E) = 2 * ∑ i, (E i).card ∧
      IsRootHostSeparated z E root hub ∧
      IsPacking G (multiLiftedPacking z E ∪ phaseTwoPacking hub base) ∧
      (multiLiftedPacking z E ∪ phaseTwoPacking hub base).card
        = (∑ i, (E i).card) + Fintype.card J := by
  classical
  refine ⟨hostBase H f colourOf, fun _ => rfl, isMultiExteriorHub_hostBase hcfg,
    hcfg.hostInj, fun _ _ hij => disjoint_hostBase hcfg hij,
    fun i j hij e he g hg =>
      pieceEdges_disjoint_cross (isMultiExteriorHub_hostBase hcfg) hij he hg,
    ?_, card_hostBase_le f colourOf, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i e he
    refine ⟨by simp, fun a ha => by simp [ha], ?_,
      mem_multiLiftedPacking.mpr ⟨i, e, he, rfl⟩⟩
    exact card_triangle
      (not_isDiag_of_mem_graphEdges G (hostBase_subset_graphEdges hcfg i he))
      (notMem_of_hub (isExteriorHub_hostBase hcfg i) he)
  · exact isPacking_multiLiftedPacking (isMultiExteriorHub_hostBase hcfg)
  · exact card_multiLiftedPacking_hostBase hcfg
  · exact totalGain_multiLiftedPacking (isMultiExteriorHub_hostBase hcfg)
  · exact isRootHostSeparated_hostBase hsep
  · exact isPacking_union_rootFactorPhases (isMultiExteriorHub_hostBase hcfg) hroot
      (isRootHostSeparated_hostBase hsep)
  · exact card_union_rootFactorPhases (isMultiExteriorHub_hostBase hcfg) hroot
      (isRootHostSeparated_hostBase hsep)

/-! ## Non-vacuity

A concrete instance of the whole configuration: the complete graph on seven vertices, a
two-vertex core `{4,5}` carrying one core edge, two exterior hosts `3` and `6` indexed by
*all* local colours, and the root-factor family with root `{0,1}`, hub `{2}` and root
factor edge `s(0,1)`.  Every hypothesis holds, and the resulting phase-I packing contains
exactly one literal triangle, one per core edge. -/

namespace Example

/-- The ambient complete graph. -/
def graph : SimpleGraph (Fin 7) := ⊤

instance : DecidableRel graph.Adj := fun a b => by unfold graph; infer_instance

/-- The core graph: a single edge. -/
def core : SimpleGraph (Fin 2) := ⊤

instance : DecidableRel core.Adj := fun a b => by unfold core; infer_instance

theorem core_maxDegree : core.maxDegree = 1 := by decide

theorem card_graphEdges_core : (graphEdges core).card = 1 := by decide

/-- The core embedding onto the two physical vertices `4` and `5`. -/
def coreEmb : Fin 2 ↪ Fin 7 := ⟨![4, 5], by decide⟩

/-- Two exterior hosts. -/
def hosts : Fin 2 → Fin 7 := ![3, 6]

/-- The two hosts carry the two local colours of the core. -/
def hostColour : Fin 2 → Fin (core.maxDegree + 1) :=
  Fin.cast (by rw [core_maxDegree])

theorem hostColour_bijective : Function.Bijective hostColour := by
  constructor
  · exact fun a b hab => by simpa [hostColour, Fin.ext_iff] using hab
  · intro y
    exact ⟨Fin.cast (by rw [core_maxDegree]) y, by simp [hostColour, Fin.ext_iff]⟩

/-- The root clique. -/
def rootSet : Finset (Fin 7) := {0, 1}

/-- The single phase-II hub. -/
def hubSet : Fin 1 → Finset (Fin 7) := ![{2}]

/-- The single root factor edge. -/
def baseEdge : Fin 1 → Sym2 (Fin 7) := ![s(0, 1)]

theorem isLocalHostConfig_example :
    IsLocalHostConfig graph core coreEmb hosts hostColour where
  coreHom := by decide
  hostInj := by decide
  hostAdj := by decide
  colourInj := hostColour_bijective.1

theorem isRootFactorFamily_example :
    IsRootFactorFamily graph rootSet hubSet baseEdge where
  rootClique := fun _ _ _ _ hab => hab
  baseSubRoot := by decide
  baseNotDiag := by decide
  baseMatching := by decide
  hubCard := by decide
  hubClique := fun _ _ _ _ _ hab => hab
  hubAdj := by decide
  hubExterior := by decide
  hubMeet := by decide

theorem isLocalRootSeparated_example :
    IsLocalRootSeparated coreEmb hosts rootSet hubSet where
  hostExterior := by decide
  coreExterior := by decide

/-- The phase-I packing of the example has exactly one triangle: one per core edge. -/
theorem card_multiLiftedPacking_example :
    (multiLiftedPacking hosts (hostBase core coreEmb hostColour)).card = 1 := by
  rw [card_multiLiftedPacking_eq_card_coreEdges isLocalHostConfig_example
    hostColour_bijective.2]
  exact card_graphEdges_core

/-- The configuration is non-vacuous: the packaged phase-I theorem applies to it. -/
theorem exists_phaseI_example :
    ∃ E : Fin 2 → Finset (Sym2 (Fin 7)),
      IsMultiExteriorHub graph hosts E ∧ IsPacking graph (multiLiftedPacking hosts E) ∧
      IsPacking graph (multiLiftedPacking hosts E ∪ phaseTwoPacking hubSet baseEdge) := by
  obtain ⟨E, -, hhub, -, -, -, -, -, hpack, -, -, -, hunion, -⟩ :=
    exists_multiExteriorHub_of_critical_root isLocalHostConfig_example
      isRootFactorFamily_example isLocalRootSeparated_example
  exact ⟨E, hhub, hpack, hunion⟩

end Example

end PaperIV.RD09LocalPhaseI

