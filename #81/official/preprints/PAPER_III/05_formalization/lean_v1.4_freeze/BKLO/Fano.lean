/-
# The Fano plane `STS(7)`, and Steiner triple systems on a `7`-set.

The reservoir used to absorb a bounded-degree leftover is built from edge-disjoint copies of `K₇`
("clusters"), each carrying a fixed Steiner triple system — a Fano plane.  This file supplies the
purely finite algebra of that object:

* `BKLO.fanoLines` — a concrete `STS(7)` on `Fin 7`, the seven lines
  `{0,1,2} {0,3,4} {0,5,6} {1,3,5} {1,4,6} {2,3,6} {2,4,5}`;
* `BKLO.isSTS_fanoLines` — its defining property, proved by `decide`: the seven lines are triangles
  which are pairwise edge-disjoint and whose edges are *exactly* the `21` edges of `K₇`, i.e. the
  lines **edge-partition** `K₇` (fact (a));
* `BKLO.IsSTS` — the same notion for an arbitrary `7`-set `C` of an arbitrary vertex type, and
  `BKLO.exists_isSTS_of_card_seven` — every `7`-set carries one (transport of the Fano plane along
  a bijection);
* `BKLO.IsSTS.triDecomp_sdiff_famEdges` — **closure under complementation of line-unions** (fact
  (b)): if the edges consumed inside the cluster are a union of lines, what is left is the union of
  the remaining lines and is therefore triangle-decomposable.  This is the property that makes a
  cluster reservoir re-decomposable, and it is immediate from (a) once the lines are known to
  partition the cluster.

Everything here is `sorry`-free.
-/
import BKLO.MapTransport
import BKLO.PackingAbsorb
import Mathlib.Tactic.Group

set_option maxRecDepth 100000

open Finset

namespace BKLO

variable {V : Type*} [DecidableEq V]

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

/-- Fact (b): the residue of a cluster after a union of lines has been consumed is
triangle-decomposable. -/
theorem IsSTS.triDecomp_sdiff_famEdges {C : Finset V} {L L' : Finset (Finset V)} (h : IsSTS C L)
    (hL' : L' ⊆ L) : TriDecomp (cliqueEdges C \ famEdges L') := by
  rw [← h.2.2]
  exact triDecomp_famEdges_sdiff_subfamily h.triFamilyIn hL'

/-! ### Transport along an injective map -/

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

theorem card_fanoLines : fanoLines.card = 7 := by decide +kernel

/-- **Fact (a).**  The seven lines of the Fano plane are edge-disjoint triangles whose edges are
exactly the `21` edges of `K₇`: they edge-partition `K₇`. -/
theorem isSTS_fanoLines : IsSTS (Finset.univ : Finset (Fin 7)) fanoLines := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

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
    simp [Fin.exists_fin_succ, eq_comm, or_left_comm]
  have hinj : Function.Injective g := by
    have hcard : ((Finset.univ : Finset (Fin 7)).image g).card = (Finset.univ : Finset (Fin 7)).card := by
      rw [himg, hC]; simp
    have := Finset.card_image_iff.1 hcard
    intro i j hij
    exact this (Finset.mem_univ i) (Finset.mem_univ j) hij
  have hline : ({0, 1, 2} : Finset (Fin 7)) ∈ fanoLines := by decide +kernel
  refine ⟨fanoLines.image (Finset.image g), ?_, ?_⟩
  · have := isSTS_fanoLines.image hinj
    rwa [himg] at this
  · refine Finset.mem_image.2 ⟨{0, 1, 2}, hline, ?_⟩
    rw [hgdef]
    ext v
    simp

/-- **A `K₇` minus any triangle is triangle-decomposable.**  Place a Steiner triple system with the
removed triangle as one of its lines; the remaining six lines decompose the rest.  This is what
lets a cluster give back everything it is not asked for, whatever triangle of legs is consumed
inside it. -/
theorem triDecomp_cliqueEdges_sdiff_triangle {C t : Finset V} (hC : C.card = 7) (htC : t ⊆ C)
    (ht : t.card = 3) : TriDecomp (cliqueEdges C \ cliqueEdges t) := by
  classical
  obtain ⟨L, hL, htL⟩ := exists_isSTS_through hC htC ht
  have hsub : ({t} : Finset (Finset V)) ⊆ L := by simpa using htL
  have hfam : famEdges ({t} : Finset (Finset V)) = cliqueEdges t := by simp [famEdges]
  have := hL.triDecomp_sdiff_famEdges hsub
  rwa [hfam] at this

/-! ### The residue of a six-cycle

A `K₇` cluster can also give back everything outside a **six-cycle**.  This is the pattern that a
routing of the leftover actually produces inside a cluster: three "owner" vertices, each of which
contributes two legs, alternating with three apex vertices, each of which is used twice.  A
six-cycle is (with a triangle) one of the only two connected patterns of the right size: the
consumed set must have even degrees and its size must be divisible by `3`, and a two-regular graph
on seven vertices with a number of edges divisible by three has three or six edges. -/

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
  ⟨sixCycleResidue7, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- **A `K₇` minus any six-cycle is triangle-decomposable.**  Together with
`BKLO.triDecomp_cliqueEdges_sdiff_triangle` this is the flexibility a cluster offers: it can give
back its unused part whenever what is consumed inside it is a triangle or a six-cycle. -/
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
    simp [Fin.exists_fin_succ, eq_comm]
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

Not every consumed pattern of the right shape can be given back.  The consumed set inside a cluster
must have even degrees (this is forced: the whole reservoir is consumed evenly) and its size must
be divisible by three, but these two conditions are *not* sufficient: if what is consumed inside a
cluster is a pair of **vertex-disjoint triangles**, the residue is not triangle-decomposable.  The
reason is that the residue then contains no triangle avoiding the seventh vertex, so it has at most
three triangles' worth of edges, while it has fifteen.

This is why the routing has to produce *connected* patterns — a triangle or a six-cycle — inside
each cluster, and not merely even ones. -/

/-- Two vertex-disjoint triangles inside `K₇`. -/
def twoTriangles7 : Finset (Sym2 (Fin 7)) :=
  cliqueEdges ({0, 1, 2} : Finset (Fin 7)) ∪ cliqueEdges ({3, 4, 5} : Finset (Fin 7))

/-- The six edges at the seventh vertex of `K₇`. -/
def star6 : Finset (Sym2 (Fin 7)) := {s(6, 0), s(6, 1), s(6, 2), s(6, 3), s(6, 4), s(6, 5)}

theorem card_star6 : star6.card = 6 := by decide +kernel

theorem star6_subset : star6 ⊆ cliqueEdges (Finset.univ : Finset (Fin 7)) \ twoTriangles7 := by
  decide +kernel

theorem card_sdiff_twoTriangles7 :
    (cliqueEdges (Finset.univ : Finset (Fin 7)) \ twoTriangles7).card = 15 := by decide +kernel

/-- Every triangle of the residue passes through the seventh vertex, and therefore uses exactly two
of the six edges at it. -/
theorem card_inter_star6_of_triangle {t : Finset (Fin 7)} (ht : t.card = 3)
    (hsub : cliqueEdges t ⊆ cliqueEdges (Finset.univ : Finset (Fin 7)) \ twoTriangles7) :
    (cliqueEdges t ∩ star6).card = 2 := by
  revert ht hsub
  revert t
  decide +kernel

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

end BKLO
