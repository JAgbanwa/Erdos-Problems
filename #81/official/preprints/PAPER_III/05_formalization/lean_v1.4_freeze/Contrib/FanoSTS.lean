/-
# Steiner triple systems, the Fano plane, and triangle decompositions of `K₇`

A self-contained development of the purely finite combinatorics of Steiner triple systems on a
`7`-set, extracted so that it depends on `Mathlib` alone.

We work in an **edge-set model**: a "graph" is a `Finset (Sym2 V)` of edges, a "triangle" is a
`3`-element `Finset V`, and `TriDecomp E` says that `E` splits exactly into edge-disjoint
triangles.

Contents:

* the mini-API `cliqueEdges`, `famEdges`, `TriDecomp`, `TriFamilyIn` and the few facts about them
  that are needed here (transport along an injective map, removal of a subfamily, counting);
* `IsSTS C L` — `L` is a Steiner triple system on the vertex set `C`;
* `fanoLines`, `isSTS_fanoLines` — a concrete `STS(7)` on `Fin 7`, the seven lines
  `{0,1,2} {0,3,4} {0,5,6} {1,3,5} {1,4,6} {2,3,6} {2,4,5}`, proved by `decide` to be edge-disjoint
  triangles whose edges are exactly the `21` edges of `K₇` (they edge-partition `K₇`);
* `exists_isSTS_of_card_seven` — every `7`-set of any vertex type carries an `STS`, and
  `exists_isSTS_through` — one may be placed with any prescribed triple as a line;
* `triDecomp_cliqueEdges_of_card_seven` — `K₇` is triangle-decomposable;
* `IsSTS.triDecomp_sdiff_famEdges` — the residue of a cluster after a union of lines has been
  consumed is triangle-decomposable;
* `triDecomp_cliqueEdges_sdiff_triangle`, `triDecomp_cliqueEdges_sdiff_sixCycle` — `K₇` minus a
  triangle, resp. minus a six-cycle, is triangle-decomposable;
* `not_triDecomp_sdiff_twoTriangles7` — `K₇` minus two vertex-disjoint triangles is **not**
  triangle-decomposable.

Everything here is `sorry`-free.
-/
import Mathlib

set_option maxRecDepth 100000

open Finset

namespace Contrib.FanoSTS

variable {V : Type*} [DecidableEq V]

/-! ### The edge-set mini-API -/

/-- The edge set (as `Sym2`) of a `Finset` of vertices, viewed as a complete graph on that set:
all unordered pairs of distinct vertices of `t`.  For a 3-set this is the triangle's three edges. -/
def cliqueEdges (t : Finset V) : Finset (Sym2 V) :=
  (t.sym2).filter (fun e => ¬ e.IsDiag)

theorem mem_cliqueEdgesV {t : Finset V} {e : Sym2 V} :
    e ∈ cliqueEdges t ↔ (∀ x ∈ e, x ∈ t) ∧ ¬ e.IsDiag := by
  simp [cliqueEdges, Finset.mem_sym2_iff]

/-- The three edges of a `3`-set. -/
theorem cliqueEdges_card_three {t : Finset V} (h : t.card = 3) : (cliqueEdges t).card = 3 := by
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.1 h
  have h3 : cliqueEdges ({a, b, c} : Finset V) = ({s(a,b), s(b,c), s(a,c)} : Finset (Sym2 V)) := by
    ext e
    induction e using Sym2.ind with
    | _ x y =>
      simp only [mem_cliqueEdgesV, Sym2.mem_iff, Sym2.isDiag_iff_proj_eq, Finset.mem_insert,
        Finset.mem_singleton, Sym2.eq_iff]
      constructor
      · rintro ⟨h, hne⟩
        rcases h x (Or.inl rfl) with rfl | rfl | rfl <;>
          rcases h y (Or.inr rfl) with rfl | rfl | rfl <;> simp_all
      · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
          refine ⟨?_, ?_⟩ <;> simp_all <;> tauto
  rw [h3]
  rw [Finset.card_insert_of_notMem (by simp; tauto),
    Finset.card_insert_of_notMem (by simp; tauto)]
  simp

/-- The edges of a triangle family. -/
def famEdges (P : Finset (Finset V)) : Finset (Sym2 V) := P.biUnion cliqueEdges

/-- `E` is **exactly triangle-decomposable**: an edge-disjoint family of 3-cliques whose edges are
exactly `E`.  (Cliques here are abstract 3-sets; triangle = its three `cliqueEdges`.) -/
def TriDecomp (E : Finset (Sym2 V)) : Prop :=
  ∃ P : Finset (Finset V), (∀ t ∈ P, t.card = 3) ∧
    (∀ t ∈ P, ∀ t' ∈ P, t ≠ t' → Disjoint (cliqueEdges t) (cliqueEdges t')) ∧
    famEdges P = E

/-- `P` is an edge-disjoint family of triangles all of whose edges lie in `E`. -/
def TriFamilyIn (E : Finset (Sym2 V)) (P : Finset (Finset V)) : Prop :=
  (∀ t ∈ P, t.card = 3) ∧ (∀ t ∈ P, cliqueEdges t ⊆ E) ∧
    (∀ t ∈ P, ∀ t' ∈ P, t ≠ t' → Disjoint (cliqueEdges t) (cliqueEdges t'))

/-- The edges of a triangle family form a triangle-decomposable edge set. -/
theorem TriFamilyIn.triDecomp {E : Finset (Sym2 V)} {P : Finset (Finset V)}
    (h : TriFamilyIn E P) : TriDecomp (famEdges P) :=
  ⟨P, h.1, h.2.2, rfl⟩

/-- A subfamily of an edge-disjoint triangle family inside `E` is again one. -/
theorem TriFamilyIn.subfamily {E : Finset (Sym2 V)} {P Q : Finset (Finset V)}
    (h : TriFamilyIn E P) (hQP : Q ⊆ P) : TriFamilyIn E Q :=
  ⟨fun t ht => h.1 t (hQP ht), fun t ht => h.2.1 t (hQP ht),
    fun t ht t' ht' hne => h.2.2 t (hQP ht) t' (hQP ht') hne⟩

/-- **Removing a subfamily of a packing removes exactly its edges.**  For an edge-disjoint triangle
family `P` and a subfamily `Q ⊆ P`, the edges of `P` not used by `Q` are exactly the edges of the
untouched triangles `P \ Q`. -/
theorem famEdges_sdiff_subfamily {E : Finset (Sym2 V)} {P Q : Finset (Finset V)}
    (hP : TriFamilyIn E P) (hQP : Q ⊆ P) :
    famEdges P \ famEdges Q = famEdges (P \ Q) := by
  classical
  ext e
  simp only [Finset.mem_sdiff, famEdges, Finset.mem_biUnion]
  constructor
  · rintro ⟨⟨t, htP, het⟩, hnot⟩
    exact ⟨t, ⟨htP, fun htQ => hnot ⟨t, htQ, het⟩⟩, het⟩
  · rintro ⟨t, ⟨htP, htQ⟩, het⟩
    refine ⟨⟨t, htP, het⟩, ?_⟩
    rintro ⟨t', ht'Q, het'⟩
    have hne : t ≠ t' := by rintro rfl; exact htQ ht'Q
    exact (Finset.disjoint_left.1 (hP.2.2 t htP t' (hQP ht'Q) hne)) het het'

/-- What remains of a packing reservoir after a subfamily has been consumed is
triangle-decomposable. -/
theorem triDecomp_famEdges_sdiff_subfamily {E : Finset (Sym2 V)} {P Q : Finset (Finset V)}
    (hP : TriFamilyIn E P) (hQP : Q ⊆ P) : TriDecomp (famEdges P \ famEdges Q) := by
  rw [famEdges_sdiff_subfamily hP hQP]
  exact (hP.subfamily Finset.sdiff_subset).triDecomp

/-- The edge set of an edge-disjoint triangle family has `3 |P|` edges. -/
theorem card_famEdges_of_triFamily {E : Finset (Sym2 V)} {P : Finset (Finset V)}
    (hP : TriFamilyIn E P) : (famEdges P).card = 3 * P.card := by
  classical
  rw [famEdges, Finset.card_biUnion hP.2.2]
  rw [Finset.sum_congr rfl (fun t ht => cliqueEdges_card_three (hP.1 t ht))]
  simp [Nat.mul_comm]

/-! ### Transport of the edge-set calculus along an injective map -/

omit [DecidableEq V] in
theorem sym2_isDiag_map {W : Type*} {f : W → V} (hf : Function.Injective f) {e : Sym2 W} :
    (Sym2.map f e).IsDiag ↔ e.IsDiag := by
  induction e using Sym2.ind with
  | _ x y => simp [Sym2.isDiag_iff_proj_eq, hf.eq_iff]

theorem cliqueEdges_image_of_injective {W : Type*} [DecidableEq W] {f : W → V}
    (hf : Function.Injective f) (t : Finset W) :
    cliqueEdges (t.image f) = (cliqueEdges t).image (Sym2.map f) := by
  ext e
  induction e using Sym2.ind with
  | _ x y =>
    constructor
    · intro he
      rw [mem_cliqueEdgesV] at he
      obtain ⟨hmem, hne⟩ := he
      obtain ⟨a, ha, hax⟩ := Finset.mem_image.1 (hmem x (by simp))
      obtain ⟨b, hb, hby⟩ := Finset.mem_image.1 (hmem y (by simp))
      subst hax
      subst hby
      refine Finset.mem_image.2 ⟨s(a, b), mem_cliqueEdgesV.2 ⟨?_, ?_⟩, by simp⟩
      · rintro z hz
        simp only [Sym2.mem_iff] at hz
        rcases hz with rfl | rfl <;> assumption
      · rw [← sym2_isDiag_map hf (e := s(a, b))]
        simpa using hne
    · intro he
      obtain ⟨e', he', heq⟩ := Finset.mem_image.1 he
      rw [mem_cliqueEdgesV] at he'
      rw [mem_cliqueEdgesV]
      refine ⟨?_, ?_⟩
      · intro z hz
        rw [← heq] at hz
        obtain ⟨w, hw, rfl⟩ := Sym2.mem_map.1 hz
        exact Finset.mem_image_of_mem f (he'.1 w hw)
      · rw [← heq, sym2_isDiag_map hf]
        exact he'.2

/-- Triangle-decomposability transports along an injective map of vertex types. -/
theorem TriDecomp.mapInj {W : Type*} [DecidableEq W] {f : W → V} (hf : Function.Injective f)
    {E : Finset (Sym2 W)} (h : TriDecomp E) : TriDecomp (E.image (Sym2.map f)) := by
  classical
  obtain ⟨P, hc, hd, he⟩ := h
  refine ⟨P.image (fun t => t.image f), ?_, ?_, ?_⟩
  · rintro t ht
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 ht
    rw [Finset.card_image_of_injective _ hf, hc s hs]
  · rintro t ht t' ht' hne
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 ht
    obtain ⟨s', hs', rfl⟩ := Finset.mem_image.1 ht'
    have hss' : s ≠ s' := by rintro rfl; exact hne rfl
    rw [cliqueEdges_image_of_injective hf, cliqueEdges_image_of_injective hf]
    exact (Finset.disjoint_image (Sym2.map.injective hf)).2 (hd s hs s' hs' hss')
  · rw [← he]
    simp only [famEdges]
    ext e
    simp only [Finset.mem_biUnion, Finset.mem_image]
    constructor
    · rintro ⟨t, ⟨s, hs, rfl⟩, hmem⟩
      rw [cliqueEdges_image_of_injective hf] at hmem
      obtain ⟨e', he', rfl⟩ := Finset.mem_image.1 hmem
      exact ⟨e', ⟨s, hs, he'⟩, rfl⟩
    · rintro ⟨e', ⟨s, hs, he'⟩, rfl⟩
      exact ⟨s.image f, ⟨s, hs, rfl⟩, by
        rw [cliqueEdges_image_of_injective hf]; exact Finset.mem_image_of_mem _ he'⟩

/-! ### Steiner triple systems on a vertex set -/

/-- `L` is a **Steiner triple system** on `C`: a family of triangles which are pairwise
edge-disjoint and whose edges are exactly the edges of the complete graph on `C`.  Equivalently,
`L` edge-partitions `K_C`, so every pair of vertices of `C` lies on exactly one line. -/
def IsSTS (C : Finset V) (L : Finset (Finset V)) : Prop :=
  (∀ t ∈ L, t.card = 3) ∧
    (∀ t ∈ L, ∀ t' ∈ L, t ≠ t' → Disjoint (cliqueEdges t) (cliqueEdges t')) ∧
      famEdges L = cliqueEdges C

/-- A Steiner triple system on `C` is an edge-disjoint triangle family inside `K_C`. -/
theorem IsSTS.triFamilyIn {C : Finset V} {L : Finset (Finset V)} (h : IsSTS C L) :
    TriFamilyIn (cliqueEdges C) L :=
  ⟨h.1, fun _ ht => h.2.2 ▸ Finset.subset_biUnion_of_mem cliqueEdges ht, h.2.1⟩

/-- Every line of a Steiner triple system on `C` is contained in `C`. -/
theorem IsSTS.subset_of_mem {C : Finset V} {L : Finset (Finset V)} (h : IsSTS C L) {t : Finset V}
    (ht : t ∈ L) : t ⊆ C := by
  intro v hv
  -- `t` has three elements, so `v` lies on one of its edges
  have hcard : t.card = 3 := h.1 t ht
  obtain ⟨w, hw, hvw⟩ : ∃ w ∈ t, v ≠ w := by
    by_contra hcon
    push_neg at hcon
    have : t ⊆ {v} := fun u hu => Finset.mem_singleton.2 (hcon u hu).symm
    have := Finset.card_le_card this
    simp [hcard] at this
  have hmem : s(v, w) ∈ cliqueEdges t := by
    refine mem_cliqueEdgesV.2 ⟨?_, by simp [Sym2.isDiag_iff_proj_eq, hvw]⟩
    rintro u hu
    simp only [Sym2.mem_iff] at hu
    rcases hu with rfl | rfl
    exacts [hv, hw]
  have hC' : s(v, w) ∈ cliqueEdges C := h.2.2 ▸ Finset.mem_biUnion.2 ⟨t, ht, hmem⟩
  exact (mem_cliqueEdgesV.1 hC').1 v (by simp)

/-- **Closure under complementation of line-unions.**  If the set of edges consumed inside a
cluster `C` is the union of a subfamily `L' ⊆ L` of its lines, then the unused edges of the cluster
are exactly the edges of the remaining lines, and are therefore triangle-decomposable. -/
theorem IsSTS.sdiff_famEdges {C : Finset V} {L L' : Finset (Finset V)} (h : IsSTS C L)
    (hL' : L' ⊆ L) : cliqueEdges C \ famEdges L' = famEdges (L \ L') := by
  rw [← h.2.2]
  exact famEdges_sdiff_subfamily h.triFamilyIn hL'

/-- The residue of a cluster after a union of lines has been consumed is
triangle-decomposable. -/
theorem IsSTS.triDecomp_sdiff_famEdges {C : Finset V} {L L' : Finset (Finset V)} (h : IsSTS C L)
    (hL' : L' ⊆ L) : TriDecomp (cliqueEdges C \ famEdges L') := by
  rw [← h.2.2]
  exact triDecomp_famEdges_sdiff_subfamily h.triFamilyIn hL'

theorem famEdges_image_of_injective {W : Type*} [DecidableEq W] {g : W → V}
    (hg : Function.Injective g) (P : Finset (Finset W)) :
    famEdges (P.image (Finset.image g)) = (famEdges P).image (Sym2.map g) := by
  classical
  ext e
  simp only [famEdges, Finset.mem_biUnion, Finset.mem_image]
  constructor
  · rintro ⟨t, ⟨s, hs, rfl⟩, hmem⟩
    rw [cliqueEdges_image_of_injective hg] at hmem
    obtain ⟨e', he', rfl⟩ := Finset.mem_image.1 hmem
    exact ⟨e', ⟨s, hs, he'⟩, rfl⟩
  · rintro ⟨e', ⟨s, hs, he'⟩, rfl⟩
    exact ⟨s.image g, ⟨s, hs, rfl⟩, by
      rw [cliqueEdges_image_of_injective hg]; exact Finset.mem_image_of_mem _ he'⟩

/-- Steiner triple systems transport along an injective map of vertex types. -/
theorem IsSTS.image {W : Type*} [DecidableEq W] {g : W → V} (hg : Function.Injective g)
    {C : Finset W} {L : Finset (Finset W)} (h : IsSTS C L) :
    IsSTS (C.image g) (L.image (Finset.image g)) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · rintro t ht
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 ht
    rw [Finset.card_image_of_injective _ hg, h.1 s hs]
  · rintro t ht t' ht' hne
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 ht
    obtain ⟨s', hs', rfl⟩ := Finset.mem_image.1 ht'
    have hss' : s ≠ s' := by rintro rfl; exact hne rfl
    rw [cliqueEdges_image_of_injective hg, cliqueEdges_image_of_injective hg]
    exact (Finset.disjoint_image (Sym2.map.injective hg)).2 (h.2.1 s hs s' hs' hss')
  · rw [famEdges_image_of_injective hg, h.2.2, cliqueEdges_image_of_injective hg]

/-! ### The Fano plane -/

/-- A concrete Steiner triple system on `Fin 7`: the seven lines of a Fano plane. -/
def fanoLines : Finset (Finset (Fin 7)) :=
  {{0, 1, 2}, {0, 3, 4}, {0, 5, 6}, {1, 3, 5}, {1, 4, 6}, {2, 3, 6}, {2, 4, 5}}

theorem card_fanoLines : fanoLines.card = 7 := by decide

/-- **Fact (a).**  The seven lines of the Fano plane are edge-disjoint triangles whose edges are
exactly the `21` edges of `K₇`: they edge-partition `K₇`. -/
theorem isSTS_fanoLines : IsSTS (Finset.univ : Finset (Fin 7)) fanoLines := by
  refine ⟨by decide, by decide, by decide⟩

/-- Every `7`-set of any vertex type carries a Steiner triple system with seven lines. -/
theorem exists_isSTS_of_card_seven {C : Finset V} (hC : C.card = 7) :
    ∃ L : Finset (Finset V), IsSTS C L ∧ L.card = 7 := by
  classical
  -- a bijection `Fin 7 ≃ C`
  set g : Fin 7 → V := fun i => ((C.equivFin.symm (Fin.cast hC.symm i) : C) : V) with hgdef
  have hginj : Function.Injective g := by
    intro i j hij
    have : C.equivFin.symm (Fin.cast hC.symm i) = C.equivFin.symm (Fin.cast hC.symm j) :=
      Subtype.ext hij
    have := C.equivFin.symm.injective this
    exact Fin.cast_injective _ this
  have himg : (Finset.univ : Finset (Fin 7)).image g = C := by
    apply Finset.eq_of_subset_of_card_le
    · intro v hv
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hv
      exact (C.equivFin.symm (Fin.cast hC.symm i)).2
    · rw [Finset.card_image_of_injective _ hginj]
      simp [hC]
  refine ⟨fanoLines.image (Finset.image g), ?_, ?_⟩
  · have := isSTS_fanoLines.image hginj
    rwa [himg] at this
  · rw [Finset.card_image_of_injOn, card_fanoLines]
    intro s _ s' _ hss'
    exact Finset.image_injective hginj hss'

/-- The complete graph on a `7`-set is triangle-decomposable: its Steiner triple system
decomposes it. -/
theorem triDecomp_cliqueEdges_of_card_seven {C : Finset V} (hC : C.card = 7) :
    TriDecomp (cliqueEdges C) := by
  obtain ⟨L, hL, _⟩ := exists_isSTS_of_card_seven hC
  exact hL.2.2 ▸ hL.triFamilyIn.triDecomp

/-- **Every triangle of a `7`-set is a line of some Steiner triple system on it.**  All `STS(7)`s
are isomorphic to the Fano plane, and the symmetric group is transitive on triples, so the Fano
plane can be placed with any prescribed triple as one of its lines. -/
theorem exists_isSTS_through {C t : Finset V} (hC : C.card = 7) (htC : t ⊆ C) (ht : t.card = 3) :
    ∃ L : Finset (Finset V), IsSTS C L ∧ t ∈ L := by
  classical
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.1 ht
  have hrest : (C \ ({a, b, c} : Finset V)).card = 4 := by
    rw [Finset.card_sdiff_of_subset htC, hC, ht]
  obtain ⟨d, hd⟩ : (C \ ({a, b, c} : Finset V)).Nonempty := by
    rw [← Finset.card_pos, hrest]; norm_num
  have herase : ((C \ ({a, b, c} : Finset V)).erase d).card = 3 := by
    rw [Finset.card_erase_of_mem hd, hrest]
  obtain ⟨e, f, gg, hef, heg, hfg, hset⟩ := Finset.card_eq_three.1 herase
  have hrest' : C \ ({a, b, c} : Finset V) = ({d, e, f, gg} : Finset V) := by
    rw [← Finset.insert_erase hd, hset]
  have hCeq : C = ({a, b, c} : Finset V) ∪ ({d, e, f, gg} : Finset V) := by
    rw [← hrest', Finset.union_sdiff_of_subset htC]
  -- the placement of the Fano plane
  set g : Fin 7 → V := ![a, b, c, d, e, f, gg] with hgdef
  have himg : (Finset.univ : Finset (Fin 7)).image g = C := by
    rw [hCeq, hgdef]
    ext v
    simp [Fin.exists_fin_succ]
    tauto
  have hinj : Function.Injective g := by
    have hcard : ((Finset.univ : Finset (Fin 7)).image g).card
        = (Finset.univ : Finset (Fin 7)).card := by
      rw [himg, hC]; simp
    have := Finset.card_image_iff.1 hcard
    intro i j hij
    exact this (Finset.mem_univ i) (Finset.mem_univ j) hij
  have hline : ({0, 1, 2} : Finset (Fin 7)) ∈ fanoLines := by decide
  refine ⟨fanoLines.image (Finset.image g), ?_, ?_⟩
  · have := isSTS_fanoLines.image hinj
    rwa [himg] at this
  · refine Finset.mem_image.2 ⟨{0, 1, 2}, hline, ?_⟩
    rw [hgdef]
    ext v
    simp

/-- **A `K₇` minus any triangle is triangle-decomposable.**  Place a Steiner triple system with the
removed triangle as one of its lines; the remaining six lines decompose the rest. -/
theorem triDecomp_cliqueEdges_sdiff_triangle {C t : Finset V} (hC : C.card = 7) (htC : t ⊆ C)
    (ht : t.card = 3) : TriDecomp (cliqueEdges C \ cliqueEdges t) := by
  classical
  obtain ⟨L, hL, htL⟩ := exists_isSTS_through hC htC ht
  have hsub : ({t} : Finset (Finset V)) ⊆ L := by simpa using htL
  have hfam : famEdges ({t} : Finset (Finset V)) = cliqueEdges t := by simp [famEdges]
  have := hL.triDecomp_sdiff_famEdges hsub
  rwa [hfam] at this

/-! ### The residue of a six-cycle

A `K₇` can also give back everything outside a **six-cycle**.  A six-cycle is (with a triangle) one
of the only two connected patterns of the right size: the consumed set must have even degrees and
its size must be divisible by `3`, and a two-regular graph on seven vertices with a number of edges
divisible by three has three or six edges. -/

/-- The six-cycle `0-1-2-3-4-5-0` inside `K₇`. -/
def sixCycle7 : Finset (Sym2 (Fin 7)) :=
  {s(0, 1), s(1, 2), s(2, 3), s(3, 4), s(4, 5), s(5, 0)}

/-- Five triangles decomposing `K₇` minus the six-cycle `0-1-2-3-4-5-0`: the three "long
diagonals" through the seventh vertex, and the two alternating triangles of the cycle. -/
def sixCycleResidue7 : Finset (Finset (Fin 7)) :=
  {{6, 0, 3}, {6, 1, 4}, {6, 2, 5}, {0, 2, 4}, {1, 3, 5}}

/-- `K₇` minus a six-cycle is triangle-decomposable — the concrete case. -/
theorem triDecomp_sdiff_sixCycle7 :
    TriDecomp (cliqueEdges (Finset.univ : Finset (Fin 7)) \ sixCycle7) :=
  ⟨sixCycleResidue7, by decide, by decide, by decide⟩

/-- **A `K₇` minus any six-cycle is triangle-decomposable.**  Together with
`triDecomp_cliqueEdges_sdiff_triangle` this is the flexibility a `K₇` offers: it can give back its
unused part whenever what is consumed inside it is a triangle or a six-cycle. -/
theorem triDecomp_cliqueEdges_sdiff_sixCycle {C : Finset V} (hC : C.card = 7)
    {a b c d e f : V} (hsub : ({a, b, c, d, e, f} : Finset V) ⊆ C)
    (hcard : ({a, b, c, d, e, f} : Finset V).card = 6) :
    TriDecomp (cliqueEdges C \ {s(a, b), s(b, c), s(c, d), s(d, e), s(e, f), s(f, a)}) := by
  classical
  have hrest : (C \ ({a, b, c, d, e, f} : Finset V)).card = 1 := by
    rw [Finset.card_sdiff_of_subset hsub, hC, hcard]
  obtain ⟨gg, hgg⟩ := Finset.card_eq_one.1 hrest
  have hCeq : C = ({a, b, c, d, e, f} : Finset V) ∪ ({gg} : Finset V) := by
    rw [← hgg, Finset.union_sdiff_of_subset hsub]
  set g : Fin 7 → V := ![a, b, c, d, e, f, gg] with hgdef
  have himg : (Finset.univ : Finset (Fin 7)).image g = C := by
    rw [hCeq, hgdef]
    ext v
    simp [Fin.exists_fin_succ]
    tauto
  have hinj : Function.Injective g := by
    have hcard' : ((Finset.univ : Finset (Fin 7)).image g).card
        = (Finset.univ : Finset (Fin 7)).card := by
      rw [himg, hC]; simp
    have h := Finset.card_image_iff.1 hcard'
    intro i j hij
    exact h (Finset.mem_univ i) (Finset.mem_univ j) hij
  have h1 : cliqueEdges C = (cliqueEdges (Finset.univ : Finset (Fin 7))).image (Sym2.map g) := by
    rw [← himg, cliqueEdges_image_of_injective hinj]
  have h2 : ({s(a, b), s(b, c), s(c, d), s(d, e), s(e, f), s(f, a)} : Finset (Sym2 V))
      = sixCycle7.image (Sym2.map g) := by
    simp [sixCycle7, hgdef]
  rw [h1, h2, ← Finset.image_sdiff _ _ (Sym2.map.injective hinj)]
  exact triDecomp_sdiff_sixCycle7.mapInj hinj

/-! ### The obstruction: two disjoint triangles

Not every consumed pattern of the right shape can be given back.  The consumed set must have even
degrees and its size must be divisible by three, but these two conditions are *not* sufficient: if
what is consumed is a pair of **vertex-disjoint triangles**, the residue is not
triangle-decomposable.  The reason is that the residue then contains no triangle avoiding the
seventh vertex, so it has at most three triangles' worth of edges, while it has fifteen. -/

/-- Two vertex-disjoint triangles inside `K₇`. -/
def twoTriangles7 : Finset (Sym2 (Fin 7)) :=
  cliqueEdges ({0, 1, 2} : Finset (Fin 7)) ∪ cliqueEdges ({3, 4, 5} : Finset (Fin 7))

/-- The six edges at the seventh vertex of `K₇`. -/
def star6 : Finset (Sym2 (Fin 7)) := {s(6, 0), s(6, 1), s(6, 2), s(6, 3), s(6, 4), s(6, 5)}

theorem card_star6 : star6.card = 6 := by decide

theorem star6_subset : star6 ⊆ cliqueEdges (Finset.univ : Finset (Fin 7)) \ twoTriangles7 := by
  decide

theorem card_sdiff_twoTriangles7 :
    (cliqueEdges (Finset.univ : Finset (Fin 7)) \ twoTriangles7).card = 15 := by decide

/-- Every triangle of the residue passes through the seventh vertex, and therefore uses exactly two
of the six edges at it. -/
theorem card_inter_star6_of_triangle {t : Finset (Fin 7)} (ht : t.card = 3)
    (hsub : cliqueEdges t ⊆ cliqueEdges (Finset.univ : Finset (Fin 7)) \ twoTriangles7) :
    (cliqueEdges t ∩ star6).card = 2 := by
  revert ht hsub
  revert t
  decide

/-- **`K₇` minus two vertex-disjoint triangles is not triangle-decomposable.**  The residue has
fifteen edges but every triangle inside it uses two of the six edges at the seventh vertex, so a
decomposition would have three triangles and only nine edges. -/
theorem not_triDecomp_sdiff_twoTriangles7 :
    ¬ TriDecomp (cliqueEdges (Finset.univ : Finset (Fin 7)) \ twoTriangles7) := by
  classical
  rintro ⟨P, hcard, hdisj, hfam⟩
  have hsub : ∀ t ∈ P, cliqueEdges t ⊆ cliqueEdges (Finset.univ : Finset (Fin 7)) \ twoTriangles7 :=
    fun t ht => hfam ▸ Finset.subset_biUnion_of_mem cliqueEdges ht
  have hfamily : TriFamilyIn (cliqueEdges (Finset.univ : Finset (Fin 7)) \ twoTriangles7) P :=
    ⟨hcard, hsub, hdisj⟩
  -- counting the edges at the seventh vertex
  have hsplit : famEdges P ∩ star6 = P.biUnion (fun t => cliqueEdges t ∩ star6) := by
    ext e
    simp only [famEdges, Finset.mem_inter, Finset.mem_biUnion]
    tauto
  have hdisj' : ∀ t ∈ P, ∀ t' ∈ P, t ≠ t' →
      Disjoint (cliqueEdges t ∩ star6) (cliqueEdges t' ∩ star6) := fun t ht t' ht' hne =>
    Finset.disjoint_of_subset_left Finset.inter_subset_left
      (Finset.disjoint_of_subset_right Finset.inter_subset_left (hdisj t ht t' ht' hne))
  have hcount : (famEdges P ∩ star6).card = 2 * P.card := by
    rw [hsplit, Finset.card_biUnion hdisj']
    rw [Finset.sum_congr rfl fun t ht => card_inter_star6_of_triangle (hcard t ht) (hsub t ht)]
    simp [Nat.mul_comm]
  have hstar : famEdges P ∩ star6 = star6 := by
    rw [hfam]
    exact Finset.inter_eq_right.2 star6_subset
  rw [hstar, card_star6] at hcount
  have hP3 : P.card = 3 := by omega
  have h15 := card_famEdges_of_triFamily hfamily
  rw [hfam, card_sdiff_twoTriangles7, hP3] at h15
  omega

end Contrib.FanoSTS
