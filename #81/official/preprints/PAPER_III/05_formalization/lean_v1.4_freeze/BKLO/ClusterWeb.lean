/-
# The web of trades: what replaces the corner mechanism

`BKLO/CornerLimit.lean` and `BKLO/CornerHexagon.lean` refute the *corner* mechanism: a routing in
which the two legs at a leftover vertex are paired **inside one cluster** forces the reservoir to
corner-link three leftover vertices, and a counting argument produces a hexagon which no sparse
reservoir corner-links.  The escape left open there is the one this file makes precise.  At a
leftover vertex `x` the parity defect of the cluster `C` holding a leg at `x` can also be repaired
by a **patch edge at `x` inside `C`**: an edge of a cross triangle through `x`.  The cluster then
consumes a longer pattern (a triangle, or a six-cycle, through `x`), and the cross triangle moves
the defect to two other clusters — a *trade*, which propagates instead of terminating locally.

Two things are proved here.

* **The local demand of the web is free.**  `BKLO.exists_cross_triangle_of_pairCovering`: pair
  covering alone forces every reserved edge `ab` of a cluster `C` to lie in a *cross* triangle
  `abq`, whose three edges lie in three pairwise distinct clusters.  In particular every cluster
  through a vertex `x` carries cross triangles through `x`.  This is the exact contrast with the
  corner condition, which pair covering does *not* supply: the corner demand is about triples of
  **leftover** vertices, which the adversary chooses, whereas the web demand is about the reserved
  edges at a single vertex, which the reservoir already has.
* **The local demand of the web is also what a routing forces.**
  `BKLO.corner_or_cross_at_vertex`: in *any* cross patch, at every leftover vertex `x` and every
  cluster `C` holding a leg at `x`, either a second leg at `x` lies in `C` (the corner, now known
  to be unavailable) or some cross triangle of the patch has an edge at `x` inside `C`.  So the
  web is not merely an option; once corners are excluded it is forced.

Finally the assembly is packaged: `BKLO.IsTriangleWeb` is the concrete form of a routing in which
every cluster consumes a triangle, `BKLO.isCrossPatch_of_triangleWeb` turns it into a cross patch,
and `BKLO.crossPatchExistence_of_triangleWebExistence` reduces `BKLO.CrossPatchExistence` — hence
the whole cluster route — to the single statement `BKLO.TriangleWebExistence`: the *global*
existence of the closed web.

The global step must **not** be attempted in the form "an even, `3`-divisible auxiliary graph on
the clusters is triangle-decomposable": that statement is false, and
`BKLO.exists_even_three_dvd_not_triDecomp` records a witness (a six-cycle has even degrees and six
edges, and contains no triangle at all).  What `3 ∣ |H|` does supply is the *numerical*
consistency of the web, `BKLO.three_dvd_card_of_triangleWeb`: in a web all of whose
patterns are triangles, the `2|H|` legs and the `3|X|` patch edges fill up patterns of size three,
so `3 ∣ 2|H|`.

Everything in this file is `sorry`-free.
-/
import BKLO.CornerHexagon

open Finset

namespace BKLO

variable {V : Type*} [DecidableEq V]

/-! ### Cross triangles are supplied by pair covering -/

/-- **Cross triangles are free.**  If every pair of vertices of `S` has at least eight reserved
common neighbours, then every reserved edge `ab` of a cluster `C` lies in a triangle `abq` with
`q ∉ C` whose three edges lie in three pairwise distinct clusters.

This is the local ingredient of the six-cycle web, and, unlike the corner condition, it follows
from pair covering alone: the cluster `C` has only seven vertices, so among the eight available
apexes of the pair `ab` one lies outside it. -/
theorem exists_cross_triangle_of_pairCovering {E : Finset (Sym2 V)} {S : Finset V}
    {𝒞 : Finset (Finset V)} {K : ℕ} (hK : 8 ≤ K) (h𝒞 : ClusterFamilyIn E 𝒞)
    (hcov : ∀ e ∈ cliqueEdges S, K ≤ (apexSet (famEdges 𝒞) S e).card)
    {C : Finset V} (hC : C ∈ 𝒞) {a b : V} (hab : s(a, b) ∈ cliqueEdges C)
    (habS : s(a, b) ∈ cliqueEdges S) :
    ∃ q ∈ S, q ∉ C ∧ ∃ Ca ∈ 𝒞, ∃ Cb ∈ 𝒞,
      s(a, q) ∈ cliqueEdges Ca ∧ s(b, q) ∈ cliqueEdges Cb ∧ Ca ≠ C ∧ Cb ≠ C ∧ Ca ≠ Cb := by
  classical
  have hC7 : C.card = 7 := h𝒞.1 C hC
  have hcard : K ≤ (apexSet (famEdges 𝒞) S s(a, b)).card := hcov _ habS
  have hne : (apexSet (famEdges 𝒞) S s(a, b) \ C).Nonempty := by
    refine Finset.card_pos.1 ?_
    have h1 : (apexSet (famEdges 𝒞) S s(a, b)).card
        ≤ (apexSet (famEdges 𝒞) S s(a, b) \ C).card + C.card :=
      Finset.card_le_card_sdiff_add_card
    omega
  obtain ⟨q, hq⟩ := hne
  rw [Finset.mem_sdiff, apexSet, Finset.mem_filter] at hq
  obtain ⟨⟨hqS, hqapex⟩, hqC⟩ := hq
  have haq : s(a, q) ∈ famEdges 𝒞 := hqapex a (by simp)
  have hbq : s(b, q) ∈ famEdges 𝒞 := hqapex b (by simp)
  obtain ⟨Ca, hCa, hCaq⟩ := Finset.mem_biUnion.1 haq
  obtain ⟨Cb, hCb, hCbq⟩ := Finset.mem_biUnion.1 hbq
  have hqCa : q ∈ Ca := (mem_cliqueEdgesV.1 hCaq).1 q (by simp)
  have hqCb : q ∈ Cb := (mem_cliqueEdgesV.1 hCbq).1 q (by simp)
  have hCane : Ca ≠ C := by rintro rfl; exact hqC hqCa
  have hCbne : Cb ≠ C := by rintro rfl; exact hqC hqCb
  refine ⟨q, hqS, hqC, Ca, hCa, Cb, hCb, hCaq, hCbq, hCane, hCbne, ?_⟩
  rintro rfl
  -- `a`, `b` and `q` would all lie in `Ca`, putting the edge `ab` into two distinct clusters
  have haCa : a ∈ Ca := (mem_cliqueEdgesV.1 hCaq).1 a (by simp)
  have hbCa : b ∈ Ca := (mem_cliqueEdgesV.1 hCbq).1 b (by simp)
  have habCa : s(a, b) ∈ cliqueEdges Ca := by
    refine mem_cliqueEdgesV.2 ⟨?_, (mem_cliqueEdgesV.1 hab).2⟩
    intro z hz
    rcases Sym2.mem_iff.1 hz with rfl | rfl
    · exact haCa
    · exact hbCa
  exact (Finset.disjoint_left.1 (h𝒞.2.2 Ca hCa C hC hCane)) habCa hab

/-- **A cross triangle through every vertex of every cluster.**  Specialisation of
`BKLO.exists_cross_triangle_of_pairCovering` to the situation of the web: at a vertex `x` of a
cluster `C` there is, for every other vertex `w` of `C`, a cross triangle `xwq` one of whose edges
at `x`, namely `xw`, lies in `C` — exactly the patch edge that repairs the parity defect of `C`
at `x`. -/
theorem exists_patch_edge_at_vertex {E : Finset (Sym2 V)} {S : Finset V}
    {𝒞 : Finset (Finset V)} {K : ℕ} (hK : 8 ≤ K) (h𝒞 : ClusterFamilyIn E 𝒞)
    (hES : E ⊆ cliqueEdges S)
    (hcov : ∀ e ∈ cliqueEdges S, K ≤ (apexSet (famEdges 𝒞) S e).card)
    {C : Finset V} (hC : C ∈ 𝒞) {x w : V} (hx : x ∈ C) (hw : w ∈ C) (hxw : x ≠ w) :
    ∃ q ∈ S, q ∉ C ∧ s(x, w) ∈ cliqueEdges C ∧ s(x, q) ∈ famEdges 𝒞 ∧ s(w, q) ∈ famEdges 𝒞 := by
  classical
  have hxwC : s(x, w) ∈ cliqueEdges C := by
    refine mem_cliqueEdgesV.2 ⟨?_, by simpa [Sym2.isDiag_iff_proj_eq] using hxw⟩
    intro z hz
    rcases Sym2.mem_iff.1 hz with rfl | rfl
    · exact hx
    · exact hw
  have hxwS : s(x, w) ∈ cliqueEdges S := hES (h𝒞.2.1 C hC hxwC)
  obtain ⟨q, hqS, hqC, Ca, hCa, Cb, hCb, hxq, hwq, -, -, -⟩ :=
    exists_cross_triangle_of_pairCovering hK h𝒞 hcov hC hxwC hxwS
  exact ⟨q, hqS, hqC, hxwC, Finset.mem_biUnion.2 ⟨Ca, hCa, hxq⟩,
    Finset.mem_biUnion.2 ⟨Cb, hCb, hwq⟩⟩

/-! ### What a routing forces at a leftover vertex -/

/-- **A second consumed edge at every leftover vertex.**  In any routing the set of reserved edges
a cluster loses has even degrees (`BKLO.even_consumed_in_cluster`), so a cluster holding a leg at a
vertex `x` loses a second edge at `x`. -/
theorem exists_second_consumed_edge {E : Finset (Sym2 V)} {𝒞 : Finset (Finset V)}
    {U : Finset (Sym2 V)} (h𝒞 : ClusterFamilyIn E 𝒞)
    (hres : ∀ C ∈ 𝒞, TriDecomp (cliqueEdges C \ U))
    {C : Finset V} (hC : C ∈ 𝒞) {g : Sym2 V} (hgU : g ∈ U) (hgC : g ∈ cliqueEdges C) {x : V}
    (hxg : x ∈ g) : ∃ g' ∈ U, g' ∈ cliqueEdges C ∧ x ∈ g' ∧ g' ≠ g := by
  classical
  set F : Finset (Sym2 V) := (cliqueEdges C ∩ U).filter (fun h => x ∈ h) with hF
  have hmemF : g ∈ F := Finset.mem_filter.2 ⟨Finset.mem_inter.2 ⟨hgC, hgU⟩, hxg⟩
  have heven : Even F.card := by
    have := even_consumed_in_cluster (h𝒞.1 C hC) (hres C hC) x
    simpa [edeg, hF] using this
  have hcard : 1 < F.card := by
    have hpos : 0 < F.card := Finset.card_pos.2 ⟨_, hmemF⟩
    obtain ⟨k, hk⟩ := heven
    omega
  obtain ⟨g', hg'F, hg'ne⟩ := Finset.exists_mem_ne hcard g
  obtain ⟨hg'inter, hg'x⟩ := Finset.mem_filter.1 hg'F
  obtain ⟨hg'C, hg'U⟩ := Finset.mem_inter.1 hg'inter
  exact ⟨g', hg'U, hg'C, hg'x, hg'ne⟩

/-- **The escape, made precise.**  Let a cross patch cover all of the leftover with fresh apexes,
and let `C` be a cluster holding the leg at `x` of a leftover edge `e`.  Then

* either a *second leg* at `x` lies in `C` — the corner, which
  `BKLO.exists_cornerLinked_of_cornerRouting` and `BKLO.exists_unlinked_hexagon` show is not
  available in a sparse reservoir —
* or some patching cross triangle of the routing has an edge at `x` inside `C`.

So, corners being dead, every leftover vertex must be served by cross triangles through it, which
is precisely the six-cycle web.  Its local ingredient is supplied by pair covering
(`BKLO.exists_patch_edge_at_vertex`), which is what makes the escape possible at all. -/
theorem corner_or_cross_at_vertex {E H : Finset (Sym2 V)} {𝒞 : Finset (Finset V)}
    {f : Sym2 V → V} {X : Finset (Finset V)} (h𝒞 : ClusterFamilyIn E 𝒞)
    (hass : IsApexAssignment H f) (hfresh : ∀ e ∈ H, ∀ e' ∈ H, f e ∉ e')
    (hres : ∀ C ∈ 𝒞, TriDecomp (cliqueEdges C \ routedEdges H f X))
    {e : Sym2 V} (he : e ∈ H) {x : V} (hx : x ∈ e) {C : Finset V} (hC : C ∈ 𝒞)
    (hleg : s(x, f e) ∈ cliqueEdges C) :
    (∃ e' ∈ H, e' ≠ e ∧ x ∈ e' ∧ s(x, f e') ∈ cliqueEdges C) ∨
      (∃ t ∈ X, ∃ g ∈ cliqueEdges t, x ∈ g ∧ g ∈ cliqueEdges C) := by
  classical
  have hlegmem : s(x, f e) ∈ apexEdges H f := by
    refine Finset.mem_sdiff.2 ⟨?_, ?_⟩
    · refine Finset.mem_biUnion.2 ⟨apexTri e (f e), Finset.mem_image.2 ⟨e, he, rfl⟩, ?_⟩
      exact (mem_cliqueEdges_apexTri_iff (hass.nondiag e he) (hass.apex_notMem e he)).2
        (Or.inr ⟨x, hx, rfl⟩)
    · intro hmem
      exact hfresh e he _ hmem (by simp)
  obtain ⟨g, hgU, hgC, hgx, hgne⟩ :=
    exists_second_consumed_edge h𝒞 hres hC (Finset.mem_union_left _ hlegmem) hleg
      (Sym2.mem_iff.2 (Or.inl rfl))
  rcases Finset.mem_union.1 hgU with hg | hg
  · -- a second leg at `x`
    left
    obtain ⟨e', he', u, hu, rfl⟩ := mem_apexEdges_iff_leg hass hg
    have hxu : x = u := by
      rcases Sym2.mem_iff.1 hgx with h | h
      · exact h
      · exact absurd hx (by rw [h]; exact hfresh e' he' e he)
    subst hxu
    exact ⟨e', he', by rintro rfl; exact hgne rfl, hu, hgC⟩
  · -- an edge of a patching cross triangle
    right
    obtain ⟨t, ht, hgt⟩ := Finset.mem_biUnion.1 hg
    exact ⟨t, ht, _, hgt, hgx, hgC⟩

/-! ### The demand of the web at a leftover vertex -/

/-- **The web demand at a vertex.**  A reserved triangle through `x` one of whose edges at `x` lies
inside the cluster `C`.  This is what the six-cycle web needs at a leftover vertex `x` in place of
the (dead) corner: the patch edge `xw` inside `C` repairs the parity of `C` at `x`, and the cross
triangle `xwm` carries the defect away to the clusters of `xm` and `wm`.

Unlike the corner condition it involves no second leftover vertex at all, which is why the counting
of `BKLO.exists_unlinked_hexagon` does not obstruct it — and indeed pair covering supplies it
outright (`BKLO.crossAtVertex_of_pairCovering`). -/
def CrossAtVertex (𝒞 : Finset (Finset V)) (x : V) (C : Finset V) : Prop :=
  ∃ w m : V, w ∈ C ∧ w ≠ x ∧ m ≠ x ∧ m ≠ w ∧ s(x, w) ∈ cliqueEdges C ∧
    s(x, m) ∈ famEdges 𝒞 ∧ s(w, m) ∈ famEdges 𝒞

/-- **Pair covering supplies the web demand** at every vertex of every cluster. -/
theorem crossAtVertex_of_pairCovering {E : Finset (Sym2 V)} {S : Finset V}
    {𝒞 : Finset (Finset V)} {K : ℕ} (hK : 8 ≤ K) (h𝒞 : ClusterFamilyIn E 𝒞)
    (hES : E ⊆ cliqueEdges S)
    (hcov : ∀ e ∈ cliqueEdges S, K ≤ (apexSet (famEdges 𝒞) S e).card)
    {C : Finset V} (hC : C ∈ 𝒞) {x w : V} (hx : x ∈ C) (hw : w ∈ C) (hxw : x ≠ w) :
    CrossAtVertex 𝒞 x C := by
  obtain ⟨q, -, hqC, hxwC, hxq, hwq⟩ :=
    exists_patch_edge_at_vertex hK h𝒞 hES hcov hC hx hw hxw
  exact ⟨w, q, hw, hxw.symm, fun h => hqC (h ▸ hx), fun h => hqC (h ▸ hw), hxwC, hxq, hwq⟩

/-- **The web demand is what a routing forces.**  In any cross patch of the whole leftover with
fresh apexes, at a leftover vertex `x` whose leg lies in the cluster `C`, either a second leg at
`x` lies in `C` — the corner — or the reservoir satisfies the web demand `CrossAtVertex 𝒞 x C`,
witnessed by one of the patching cross triangles.

Together with `BKLO.crossAtVertex_of_pairCovering` this is the exact sense in which the six-cycle
web escapes the refutation of the corner mechanism: what the routing forces at each leftover vertex
is a resource the reservoir already has. -/
theorem corner_or_crossAtVertex {E H : Finset (Sym2 V)} {𝒞 : Finset (Finset V)}
    {f : Sym2 V → V} {X : Finset (Finset V)} (h𝒞 : ClusterFamilyIn E 𝒞)
    (hpatch : IsCrossPatch 𝒞 H H f X) (hfresh : ∀ e ∈ H, ∀ e' ∈ H, f e ∉ e')
    {e : Sym2 V} (he : e ∈ H) {x : V} (hx : x ∈ e) {C : Finset V} (hC : C ∈ 𝒞)
    (hleg : s(x, f e) ∈ cliqueEdges C) :
    (∃ e' ∈ H, e' ≠ e ∧ x ∈ e' ∧ s(x, f e') ∈ cliqueEdges C) ∨ CrossAtVertex 𝒞 x C := by
  classical
  have hres : ∀ C ∈ 𝒞, TriDecomp (cliqueEdges C \ routedEdges H f X) := by
    intro C hC
    have hsplit : cliqueEdges C \ routedEdges H f X
        = cliqueEdges C \ (routedEdges H f X ∩ cliqueEdges C) := by
      ext g
      simp only [Finset.mem_sdiff, Finset.mem_inter]
      tauto
    rw [hsplit]
    exact triDecomp_cliqueEdges_sdiff_pattern (h𝒞.1 C hC) (hpatch.pattern C hC)
  rcases corner_or_cross_at_vertex h𝒞 hpatch.apex hfresh hres he hx hC hleg with hcorner | hcross
  · exact Or.inl hcorner
  · right
    obtain ⟨t, ht, g, hgt, hgx, hgC⟩ := hcross
    obtain ⟨w, rfl⟩ := Sym2.mem_iff_exists.1 hgx
    have hnd : ¬ (s(x, w) : Sym2 V).IsDiag := (mem_cliqueEdgesV.1 hgC).2
    have hxw : x ≠ w := by simpa [Sym2.isDiag_iff_proj_eq] using hnd
    have hwC : w ∈ C := (mem_cliqueEdgesV.1 hgC).1 w (by simp)
    have hxt : x ∈ t := (mem_cliqueEdgesV.1 hgt).1 x (by simp)
    have hwt : w ∈ t := (mem_cliqueEdgesV.1 hgt).1 w (by simp)
    -- the third vertex of the cross triangle
    have hpair : ({x, w} : Finset V) ⊆ t := by
      intro z hz
      rcases Finset.mem_insert.1 hz with rfl | hz
      · exact hxt
      · rw [Finset.mem_singleton.1 hz]; exact hwt
    have hcard : ({x, w} : Finset V).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simpa using hxw), Finset.card_singleton]
    have hne : (t \ ({x, w} : Finset V)).Nonempty := by
      refine Finset.card_pos.1 ?_
      have hsum := Finset.card_sdiff_add_card_eq_card hpair
      have h3 := hpatch.cross_card t ht
      omega
    obtain ⟨m, hm⟩ := hne
    rw [Finset.mem_sdiff] at hm
    have hmx : m ≠ x := by intro h; exact hm.2 (by simp [h])
    have hmw : m ≠ w := by intro h; exact hm.2 (by simp [h])
    have hxm : s(x, m) ∈ cliqueEdges t := by
      refine mem_cliqueEdgesV.2 ⟨?_, by simpa [Sym2.isDiag_iff_proj_eq] using hmx.symm⟩
      intro z hz
      rcases Sym2.mem_iff.1 hz with rfl | rfl
      · exact hxt
      · exact hm.1
    have hwm : s(w, m) ∈ cliqueEdges t := by
      refine mem_cliqueEdgesV.2 ⟨?_, by simpa [Sym2.isDiag_iff_proj_eq] using hmw.symm⟩
      intro z hz
      rcases Sym2.mem_iff.1 hz with rfl | rfl
      · exact hwt
      · exact hm.1
    exact ⟨w, m, hwC, hxw.symm, hmx, hmw, hgC, hpatch.cross_res t ht hxm,
      hpatch.cross_res t ht hwm⟩

/-! ### The web, and the reduction of the routing to its existence -/

/-- **A triangle web.**  The concrete form of a routing in which every cluster consumes a triangle:
an apex covering of the whole leftover with reserved legs, a family `X` of reserved cross triangles
patching the parity defects, and a designated triangle `T C` inside every cluster which is exactly
what that cluster loses.

The designated triangles are the "tokens" of the web: the triangle of a cluster holding a leg
consists of that leg and two patch edges, each of which belongs to a cross triangle whose other two
edges are patch edges of two *other* clusters.  The web closes precisely when every designated
triangle is filled. -/
structure IsTriangleWeb (𝒞 : Finset (Finset V)) (H : Finset (Sym2 V)) (f : Sym2 V → V)
    (X : Finset (Finset V)) (T : Finset V → Finset V) : Prop where
  /-- the apex covering is genuine -/
  apex : IsApexAssignment H f
  /-- all legs are reserved -/
  legs : apexEdges H f ⊆ famEdges 𝒞
  /-- the patching triangles are triangles ... -/
  cross_card : ∀ t ∈ X, t.card = 3
  /-- ... with reserved edges ... -/
  cross_res : ∀ t ∈ X, cliqueEdges t ⊆ famEdges 𝒞
  /-- ... pairwise edge-disjoint ... -/
  cross_disj : ∀ t ∈ X, ∀ t' ∈ X, t ≠ t' → Disjoint (cliqueEdges t) (cliqueEdges t')
  /-- ... and edge-disjoint from the legs -/
  cross_legs : Disjoint (famEdges X) (apexEdges H f)
  /-- the designated set of a cluster is a triangle inside it, or empty -/
  tri_sub : ∀ C ∈ 𝒞, T C ⊆ C
  tri_card : ∀ C ∈ 𝒞, T C = ∅ ∨ (T C).card = 3
  /-- everything the cluster loses is designated ... -/
  consumed_le : ∀ C ∈ 𝒞, ∀ g ∈ routedEdges H f X, g ∈ cliqueEdges C → g ∈ cliqueEdges (T C)
  /-- ... and everything designated is lost -/
  le_consumed : ∀ C ∈ 𝒞, cliqueEdges (T C) ⊆ routedEdges H f X

/-- A web for a part `H'` of the leftover, the rest of which decomposes on its own, is a cross
patch: the designated triangles are patterns the clusters give back. -/
theorem isCrossPatch_of_partial_triangleWeb {𝒞 : Finset (Finset V)} {H H' : Finset (Sym2 V)}
    {f : Sym2 V → V} {X : Finset (Finset V)} {T : Finset V → Finset V}
    (hsub : H' ⊆ H) (hrest : TriDecomp (H \ H')) (h : IsTriangleWeb 𝒞 H' f X T) :
    IsCrossPatch 𝒞 H H' f X where
  subset := hsub
  rest := hrest
  apex := h.apex
  legs := h.legs
  cross_card := h.cross_card
  cross_res := h.cross_res
  cross_disj := h.cross_disj
  cross_legs := h.cross_legs
  pattern := by
    refine pattern_of_local (F := fun C => cliqueEdges (T C)) ?_ ?_ ?_ ?_
    · intro C hC
      rcases h.tri_card C hC with hT | hT
      · left; simp [hT, cliqueEdges]
      · exact Or.inr (Or.inl ⟨T C, h.tri_sub C hC, hT, rfl⟩)
    · intro C hC
      exact cliqueEdges_mono (h.tri_sub C hC)
    · intro C hC
      exact h.le_consumed C hC
    · intro C hC g hg hgC
      exact h.consumed_le C hC g hg hgC

/-- A web is a cross patch. -/
theorem isCrossPatch_of_triangleWeb {𝒞 : Finset (Finset V)} {H : Finset (Sym2 V)}
    {f : Sym2 V → V} {X : Finset (Finset V)} {T : Finset V → Finset V}
    (h : IsTriangleWeb 𝒞 H f X T) : IsCrossPatch 𝒞 H H f X :=
  isCrossPatch_of_partial_triangleWeb (Finset.Subset.refl _)
    (by simpa using (triDecomp_empty : TriDecomp (∅ : Finset (Sym2 V)))) h

/-- **The isolated crux.**  For every leftover degree bound `D` there is a covering multiplicity
`K` such that inside every pair-covering cluster reservoir every admissible leftover admits a
*closed triangle web*.

This is `BKLO.CrossPatchExistence` with the patterns specialised to triangles and the bookkeeping
made explicit: what has to be produced is the choice of apexes, of patching cross triangles, and of
the designated triangle of every cluster, such that the designated triangles are exactly filled.
The two local ingredients are available — apexes by pair covering, and cross triangles through
every vertex of every cluster by `BKLO.exists_cross_triangle_of_pairCovering` — and the numerical
bookkeeping closes because `3 ∣ |H|`
(`BKLO.three_dvd_card_of_triangleWeb`).  What is missing is the *global* choice: the web of
trades must terminate, i.e. the patch edges demanded by the designated triangles must be filled by
cross triangles which do not demand new clusters indefinitely. -/
def TriangleWebExistence : Prop :=
  ∀ D : ℕ, ∃ K : ℕ,
    ∀ {V : Type} [DecidableEq V] (E : Finset (Sym2 V)) (S : Finset V) (𝒞 : Finset (Finset V)),
      E ⊆ cliqueEdges S → ClusterFamilyIn E 𝒞 →
      (∀ e ∈ cliqueEdges S, K ≤ (apexSet (famEdges 𝒞) S e).card) →
      ∀ H : Finset (Sym2 V), H ⊆ E \ famEdges 𝒞 → EvenDegrees H → (∀ v : V, edeg H v ≤ D) →
        3 ∣ H.card →
        ∃ (f : Sym2 V → V) (X : Finset (Finset V)) (T : Finset V → Finset V),
          IsTriangleWeb 𝒞 H f X T

/-- The web suffices: it gives a cross patch, hence the routing, hence the target. -/
theorem crossPatchExistence_of_triangleWebExistence (h : TriangleWebExistence) :
    CrossPatchExistence := by
  intro D
  obtain ⟨K, hK⟩ := h D
  refine ⟨K, ?_⟩
  intro V _ E S 𝒞 hES h𝒞 hcov H hHsub hHeven hHdeg hHdvd
  obtain ⟨f, X, T, hweb⟩ := hK E S 𝒞 hES h𝒞 hcov H hHsub hHeven hHdeg hHdvd
  exact ⟨H, f, X, isCrossPatch_of_triangleWeb hweb⟩

/-- The routing, hence the target, follows from the existence of closed webs. -/
theorem clusterUsageRouting_of_triangleWebExistence (h : TriangleWebExistence) :
    ClusterUsageRouting :=
  clusterUsageRouting_of_crossPatch (crossPatchExistence_of_triangleWebExistence h)

/-- **The isolated crux, in its most economical form.**  Only a *part* of the leftover has to carry
a web, the rest being triangle-decomposable on its own — so the triangles of the leftover, and more
generally any decomposable part of it, cost nothing. -/
def PartialTriangleWebExistence : Prop :=
  ∀ D : ℕ, ∃ K : ℕ,
    ∀ {V : Type} [DecidableEq V] (E : Finset (Sym2 V)) (S : Finset V) (𝒞 : Finset (Finset V)),
      E ⊆ cliqueEdges S → ClusterFamilyIn E 𝒞 →
      (∀ e ∈ cliqueEdges S, K ≤ (apexSet (famEdges 𝒞) S e).card) →
      ∀ H : Finset (Sym2 V), H ⊆ E \ famEdges 𝒞 → EvenDegrees H → (∀ v : V, edeg H v ≤ D) →
        3 ∣ H.card →
        ∃ (H' : Finset (Sym2 V)) (f : Sym2 V → V) (X : Finset (Finset V))
          (T : Finset V → Finset V),
          H' ⊆ H ∧ TriDecomp (H \ H') ∧ IsTriangleWeb 𝒞 H' f X T

/-- Partial webs suffice as well. -/
theorem crossPatchExistence_of_partialTriangleWebExistence (h : PartialTriangleWebExistence) :
    CrossPatchExistence := by
  intro D
  obtain ⟨K, hK⟩ := h D
  refine ⟨K, ?_⟩
  intro V _ E S 𝒞 hES h𝒞 hcov H hHsub hHeven hHdeg hHdvd
  obtain ⟨H', f, X, T, hsub, hrest, hweb⟩ := hK E S 𝒞 hES h𝒞 hcov H hHsub hHeven hHdeg hHdvd
  exact ⟨H', f, X, isCrossPatch_of_partial_triangleWeb hsub hrest hweb⟩

/-! ### Webs combine -/

/-- The empty leftover has the empty web. -/
theorem isTriangleWeb_empty (𝒞 : Finset (Finset V)) (f : Sym2 V → V) :
    IsTriangleWeb 𝒞 (∅ : Finset (Sym2 V)) f ∅ (fun _ => ∅) where
  apex := ⟨by simp, by simp, by simp⟩
  legs := by simp [apexEdges, apexCover, apexFam, famEdges]
  cross_card := by simp
  cross_res := by simp
  cross_disj := by simp
  cross_legs := by simp [famEdges]
  tri_sub := by simp
  tri_card := by simp
  consumed_le := by
    intro C _ g hg
    simp [routedEdges, apexEdges, apexCover, apexFam, famEdges] at hg
  le_consumed := by
    intro C _
    simp [cliqueEdges]

/-- **Webs combine.**  Two webs for the two halves of a leftover, sharing the apex function and
using edge-disjoint patching triangles and disjoint sets of active clusters, assemble into a web
for the whole leftover.

This is the architecture in which the global web is to be built: a gadget for each piece of the
leftover, placed greedily so that the pieces do not interfere — no cluster is used twice and no
reserved edge is consumed twice. -/
theorem isTriangleWeb_union {𝒞 : Finset (Finset V)} {H H₁ H₂ : Finset (Sym2 V)} {f : Sym2 V → V}
    {X₁ X₂ : Finset (Finset V)} {T₁ T₂ : Finset V → Finset V}
    (hdisjHR : Disjoint (famEdges 𝒞) H) (hH : H = H₁ ∪ H₂)
    (hass : IsApexAssignment H f)
    (hw₁ : IsTriangleWeb 𝒞 H₁ f X₁ T₁) (hw₂ : IsTriangleWeb 𝒞 H₂ f X₂ T₂)
    (hXX : Disjoint (famEdges X₁) (famEdges X₂))
    (hXL₂ : Disjoint (famEdges X₁) (apexEdges H₂ f))
    (hXL₁ : Disjoint (famEdges X₂) (apexEdges H₁ f))
    (hT : ∀ C ∈ 𝒞, T₁ C = ∅ ∨ T₂ C = ∅) :
    IsTriangleWeb 𝒞 H f (X₁ ∪ X₂) (fun C => if T₁ C = ∅ then T₂ C else T₁ C) := by
  classical
  -- the legs of the two halves make up the legs of the whole
  have hcover : apexCover H f = apexCover H₁ f ∪ apexCover H₂ f := by
    rw [hH, apexCover, apexCover, apexCover, apexFam, apexFam, apexFam, Finset.image_union,
      famEdges, famEdges, famEdges, Finset.union_biUnion]
  have hpart : ∀ (H' : Finset (Sym2 V)), H' ⊆ H → apexEdges H' f ⊆ famEdges 𝒞 →
      apexEdges H' f = apexCover H' f \ H := by
    intro H' hH' hlegs
    apply Finset.Subset.antisymm
    · intro g hg
      refine Finset.mem_sdiff.2 ⟨(Finset.mem_sdiff.1 hg).1, ?_⟩
      exact fun hgH => (Finset.disjoint_left.1 hdisjHR) (hlegs hg) hgH
    · intro g hg
      obtain ⟨hg1, hg2⟩ := Finset.mem_sdiff.1 hg
      exact Finset.mem_sdiff.2 ⟨hg1, fun hgH' => hg2 (hH' hgH')⟩
  have hlegs : apexEdges H f = apexEdges H₁ f ∪ apexEdges H₂ f := by
    rw [hpart H₁ (by rw [hH]; exact Finset.subset_union_left) hw₁.legs,
      hpart H₂ (by rw [hH]; exact Finset.subset_union_right) hw₂.legs, apexEdges, hcover,
      Finset.union_sdiff_distrib]
  have hfam : famEdges (X₁ ∪ X₂) = famEdges X₁ ∪ famEdges X₂ := by
    rw [famEdges, famEdges, famEdges, Finset.union_biUnion]
  have hrouted : routedEdges H f (X₁ ∪ X₂)
      = routedEdges H₁ f X₁ ∪ routedEdges H₂ f X₂ := by
    rw [routedEdges, routedEdges, routedEdges, hlegs, hfam]
    ac_rfl
  refine
    { apex := hass
      legs := ?_
      cross_card := ?_
      cross_res := ?_
      cross_disj := ?_
      cross_legs := ?_
      tri_sub := ?_
      tri_card := ?_
      consumed_le := ?_
      le_consumed := ?_ }
  · rw [hlegs]; exact Finset.union_subset hw₁.legs hw₂.legs
  · intro t ht
    rcases Finset.mem_union.1 ht with h | h
    · exact hw₁.cross_card t h
    · exact hw₂.cross_card t h
  · intro t ht
    rcases Finset.mem_union.1 ht with h | h
    · exact hw₁.cross_res t h
    · exact hw₂.cross_res t h
  · intro t ht t' ht' hne
    have hsub : ∀ s ∈ X₁, cliqueEdges s ⊆ famEdges X₁ := fun s hs =>
      Finset.subset_biUnion_of_mem cliqueEdges hs
    have hsub' : ∀ s ∈ X₂, cliqueEdges s ⊆ famEdges X₂ := fun s hs =>
      Finset.subset_biUnion_of_mem cliqueEdges hs
    rcases Finset.mem_union.1 ht with h | h <;> rcases Finset.mem_union.1 ht' with h' | h'
    · exact hw₁.cross_disj t h t' h' hne
    · exact Finset.disjoint_of_subset_left (hsub t h)
        (Finset.disjoint_of_subset_right (hsub' t' h') hXX)
    · exact Finset.disjoint_of_subset_left (hsub' t h)
        (Finset.disjoint_of_subset_right (hsub t' h') hXX.symm)
    · exact hw₂.cross_disj t h t' h' hne
  · rw [hfam, hlegs]
    refine Finset.disjoint_union_left.2 ⟨?_, ?_⟩ <;>
      refine Finset.disjoint_union_right.2 ⟨?_, ?_⟩
    · exact hw₁.cross_legs
    · exact hXL₂
    · exact hXL₁
    · exact hw₂.cross_legs
  · intro C hC
    by_cases h : T₁ C = ∅
    · simp only [if_pos h]
      exact hw₂.tri_sub C hC
    · simp only [if_neg h]
      exact hw₁.tri_sub C hC
  · intro C hC
    by_cases h : T₁ C = ∅
    · simp only [if_pos h]
      exact hw₂.tri_card C hC
    · simp only [if_neg h]
      exact hw₁.tri_card C hC
  · intro C hC g hg hgC
    rw [hrouted] at hg
    rcases Finset.mem_union.1 hg with hg | hg
    · have hg' := hw₁.consumed_le C hC g hg hgC
      have hne : T₁ C ≠ ∅ := by
        rintro h
        rw [h] at hg'
        simp [cliqueEdges] at hg'
      simp only [if_neg hne]
      exact hg'
    · have hg' := hw₂.consumed_le C hC g hg hgC
      have hne : T₂ C ≠ ∅ := by
        rintro h
        rw [h] at hg'
        simp [cliqueEdges] at hg'
      have h₁ : T₁ C = ∅ := by
        rcases hT C hC with h | h
        · exact h
        · exact absurd h hne
      simp only [if_pos h₁]
      exact hg'
  · intro C hC
    rw [hrouted]
    by_cases h : T₁ C = ∅
    · simp only [if_pos h]
      exact (hw₂.le_consumed C hC).trans Finset.subset_union_right
    · simp only [if_neg h]
      exact (hw₁.le_consumed C hC).trans Finset.subset_union_left

/-! ### The arithmetic of the web -/

/-- A set of reserved edges is counted cluster by cluster: the clusters are edge-disjoint and every
reserved edge lies in one of them. -/
theorem card_eq_sum_over_clusters {E : Finset (Sym2 V)} {𝒞 : Finset (Finset V)}
    {U : Finset (Sym2 V)} (h𝒞 : ClusterFamilyIn E 𝒞) (hU : U ⊆ famEdges 𝒞) :
    U.card = ∑ C ∈ 𝒞, (U ∩ cliqueEdges C).card := by
  classical
  have hsplit : U = 𝒞.biUnion (fun C => U ∩ cliqueEdges C) := by
    ext g
    simp only [Finset.mem_biUnion, Finset.mem_inter]
    constructor
    · intro hg
      obtain ⟨C, hC, hgC⟩ := Finset.mem_biUnion.1 (hU hg)
      exact ⟨C, hC, hg, hgC⟩
    · rintro ⟨C, -, hg, -⟩
      exact hg
  have hdisj : ∀ C ∈ 𝒞, ∀ C' ∈ 𝒞, C ≠ C' →
      Disjoint (U ∩ cliqueEdges C) (U ∩ cliqueEdges C') := by
    intro C hC C' hC' hne
    exact Finset.disjoint_of_subset_left Finset.inter_subset_right
      (Finset.disjoint_of_subset_right Finset.inter_subset_right (h𝒞.2.2 C hC C' hC' hne))
  have hcount := Finset.card_biUnion hdisj
  rw [← hsplit] at hcount
  exact hcount

/-- **The web is numerically consistent exactly when `3 ∣ |H|`.**  In a closed triangle web every
cluster loses a triangle, so the consumed set has a number of edges divisible by three; it consists
of the `2|H|` legs and the `3|X|` patch edges, whence `3 ∣ 2|H|`, i.e. `3 ∣ |H|`.

This is where the divisibility hypothesis of the routing statement enters — globally, through the
whole web, and not cluster by cluster. -/
theorem three_dvd_card_of_triangleWeb {E : Finset (Sym2 V)} {𝒞 : Finset (Finset V)}
    {H : Finset (Sym2 V)} {f : Sym2 V → V} {X : Finset (Finset V)} {T : Finset V → Finset V}
    (h𝒞 : ClusterFamilyIn E 𝒞) (h : IsTriangleWeb 𝒞 H f X T) : 3 ∣ H.card := by
  classical
  have hX : TriFamilyIn (famEdges 𝒞) X := ⟨h.cross_card, h.cross_res, h.cross_disj⟩
  have hUsub : routedEdges H f X ⊆ famEdges 𝒞 :=
    Finset.union_subset h.legs (famEdges_subset_of_triFamilyIn hX)
  -- counted cluster by cluster the consumed set is a multiple of three
  have hterm : ∀ C ∈ 𝒞, 3 ∣ (routedEdges H f X ∩ cliqueEdges C).card := by
    intro C hC
    have heq : routedEdges H f X ∩ cliqueEdges C = cliqueEdges (T C) := by
      apply Finset.Subset.antisymm
      · intro g hg
        exact h.consumed_le C hC g (Finset.mem_inter.1 hg).1 (Finset.mem_inter.1 hg).2
      · intro g hg
        exact Finset.mem_inter.2 ⟨h.le_consumed C hC hg, cliqueEdges_mono (h.tri_sub C hC) hg⟩
    rw [heq]
    rcases h.tri_card C hC with hT | hT
    · simp [hT, cliqueEdges]
    · rw [cliqueEdges_card_three hT]
  have hdvd : 3 ∣ (routedEdges H f X).card := by
    rw [card_eq_sum_over_clusters h𝒞 hUsub]
    exact Finset.dvd_sum hterm
  -- and it consists of the legs and the patch edges
  have hcard : (routedEdges H f X).card = 2 * H.card + 3 * X.card := by
    rw [routedEdges, Finset.union_comm, Finset.card_union_of_disjoint h.cross_legs,
      card_famEdges_of_triFamily hX, card_apexEdges h.apex]
    omega
  omega

/-! ### The global step is not "even and `3`-divisible implies decomposable" -/

/-- **A warning.**  The auxiliary graph formed on the clusters by the patch edges cannot be closed
up by the principle "even degrees and a number of edges divisible by three imply triangle
decomposability": that principle is false.  A six-cycle has even degrees and six edges and contains
no triangle whatsoever.  (This is also why the patterns a cluster can give back have to be listed
explicitly in `BKLO.IsClusterPattern`.) -/
theorem exists_even_three_dvd_not_triDecomp :
    ∃ G : Finset (Sym2 (Fin 6)), EvenDegrees G ∧ 3 ∣ G.card ∧ ¬ TriDecomp G := by
  have hp : ∀ i j : Fin 6, i ≠ j → (id i : Fin 6) ≠ id j := fun i j h => h
  refine ⟨hexEdges (id : Fin 6 → Fin 6), evenDegrees_hexEdges hp, ?_,
    not_triDecomp_hexEdges hp⟩
  rw [hexEdges_card hp]
  decide +kernel

end BKLO
