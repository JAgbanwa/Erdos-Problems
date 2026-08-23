/-
# The routing, in explicit form: legs plus cross triangles.

`BKLO/ClusterReservoir.lean` reduces the target to `BKLO.ClusterUsageRouting`, and
`BKLO/ClusterObstruction.lean` shows that the legs of an apex covering can never be the whole
story: for a *spread* leftover they leave a vertex of odd degree in some cluster, and a cluster
gives its unused part back only if what it loses has even degrees.  The repair mechanism available
is a **cross triangle** — a triangle all of whose edges are reserved but which is not contained in
a cluster, so that its three edges lie in three pairwise distinct clusters
(`BKLO.third_edge_notMem_clusters`).

This file makes the resulting shape of a routing completely explicit and reduces the routing
statement to it.  A *cross patch* for the leftover `H` consists of

* a part `H'` of `H` covered by apex triangles with reserved legs (the rest of `H`, `H \ H'`,
  being triangle-decomposable on its own — e.g. the triangles of `H`),
* a family `X` of cross triangles, edge-disjoint from each other and from the legs,

such that inside every cluster the consumed edges — the legs together with the cross-triangle edges,
`BKLO.routedEdges` — form a pattern the cluster can give back.  `BKLO.triDecomp_of_crossPatch`
turns such data into `TriDecomp (famEdges 𝒞 ∪ H)`, so that `BKLO.ClusterUsageRouting` follows from
the *existence* of cross patches, `BKLO.CrossPatchExistence`
(`BKLO.clusterUsageRouting_of_crossPatch`).  This is a strictly more elementary statement than the
routing itself: no triangle decomposition occurs in it any more, only the choice of apexes and of
patching triangles.

The second half of the file records what such a choice must satisfy — the exact reason why the
counting `2|H|` legs, `4|H|` patch edges, `4|H|/3` cross triangles is not by itself enough:

* `BKLO.even_consumed_in_cluster` — in **any** routing, the set of edges a cluster loses has even
  degrees at every vertex.  (`K₇` has even degrees and the unused part, being decomposable, has
  even degrees.)
* `BKLO.exists_second_leg_in_cluster` — consequently, if the patching triangles avoid the vertices
  touched by the leftover, then at every leftover vertex `x` the legs **pair up inside clusters**:
  whenever the leg of a leftover edge `e` at `x` lies in the cluster `C`, some *other* leftover
  edge at `x` has its leg at `x` in the same cluster `C`.

So a cross patch cannot be assembled by choosing the apexes independently and then matching
defects to patches: whether a cross triangle repairs a given defect is not a free choice, since
each of its edges lies in the one cluster determined by that edge's endpoints.  What the choice of
apexes has to achieve is the *corner* condition of `exists_second_leg_in_cluster` (or its variant
in which a patch edge at `x` takes the role of the second leg), and that is a property of the
reservoir which pair covering — `K` reserved common neighbours for every pair, with no control at
all over how those neighbours are distributed among the clusters through `x` — does not provide.
`BOUNDED_LEFTOVER_STATUS.md` §10 discusses this.

Everything in this file is `sorry`-free.
-/
import BKLO.ClusterObstruction

open Finset

namespace BKLO

variable {V : Type*} [DecidableEq V]

/-! ### Cross patches -/

/-- The reserved edges a routing consumes: the legs of the apex covering of `H'` together with the
edges of the patching cross triangles `X`. -/
def routedEdges (H' : Finset (Sym2 V)) (f : Sym2 V → V) (X : Finset (Finset V)) :
    Finset (Sym2 V) :=
  apexEdges H' f ∪ famEdges X

/-- **A cross patch** for the leftover `H` inside the cluster reservoir `𝒞`: an apex covering of a
part `H'` of `H` whose legs are reserved, a triangle-decomposable remainder `H \ H'`, and a family
`X` of reserved patching triangles, such that the edges consumed inside every cluster form a
pattern the cluster gives back. -/
structure IsCrossPatch (𝒞 : Finset (Finset V)) (H H' : Finset (Sym2 V)) (f : Sym2 V → V)
    (X : Finset (Finset V)) : Prop where
  /-- the apex-covered part of the leftover -/
  subset : H' ⊆ H
  /-- the remainder of the leftover decomposes on its own -/
  rest : TriDecomp (H \ H')
  /-- the covering triangles are genuine and pairwise edge-disjoint -/
  apex : IsApexAssignment H' f
  /-- all legs are reserved -/
  legs : apexEdges H' f ⊆ famEdges 𝒞
  /-- the patching triangles are triangles ... -/
  cross_card : ∀ t ∈ X, t.card = 3
  /-- ... all of whose edges are reserved ... -/
  cross_res : ∀ t ∈ X, cliqueEdges t ⊆ famEdges 𝒞
  /-- ... and which are pairwise edge-disjoint ... -/
  cross_disj : ∀ t ∈ X, ∀ t' ∈ X, t ≠ t' → Disjoint (cliqueEdges t) (cliqueEdges t')
  /-- ... and edge-disjoint from the legs -/
  cross_legs : Disjoint (famEdges X) (apexEdges H' f)
  /-- every cluster loses a pattern it can give back -/
  pattern : ∀ C ∈ 𝒞, IsClusterPattern C (routedEdges H' f X ∩ cliqueEdges C)

/-- The consumed edges of a cross patch are reserved. -/
theorem routedEdges_subset {𝒞 : Finset (Finset V)} {H H' : Finset (Sym2 V)} {f : Sym2 V → V}
    {X : Finset (Finset V)} (h : IsCrossPatch 𝒞 H H' f X) :
    routedEdges H' f X ⊆ famEdges 𝒞 := by
  refine Finset.union_subset h.legs ?_
  intro g hg
  obtain ⟨t, ht, hgt⟩ := Finset.mem_biUnion.1 hg
  exact h.cross_res t ht hgt

/-- **The consumed edges together with the leftover decompose into triangles**: the apex triangles,
the cross triangles, and the triangles of the untouched part of the leftover. -/
theorem triDecomp_routedEdges_union {𝒞 : Finset (Finset V)} {H H' : Finset (Sym2 V)}
    {f : Sym2 V → V} {X : Finset (Finset V)} (hdisj : Disjoint (famEdges 𝒞) H)
    (h : IsCrossPatch 𝒞 H H' f X) : TriDecomp (routedEdges H' f X ∪ H) := by
  classical
  have hHR : Disjoint (apexEdges H' f) H := Finset.disjoint_of_subset_left h.legs hdisj
  have hXR : Disjoint (famEdges X) H := by
    refine Finset.disjoint_left.2 fun g hg hgH => ?_
    obtain ⟨t, ht, hgt⟩ := Finset.mem_biUnion.1 hg
    exact (Finset.disjoint_left.1 hdisj) (h.cross_res t ht hgt) hgH
  -- the three pieces
  have hsplit : routedEdges H' f X ∪ H
      = apexCover H' f ∪ (famEdges X ∪ (H \ H')) := by
    rw [apexCover_eq_union h.apex.nondiag, routedEdges]
    ext g
    simp only [Finset.mem_union, Finset.mem_sdiff]
    constructor
    · rintro ((hA | hX) | hH)
      · exact Or.inl (Or.inr hA)
      · exact Or.inr (Or.inl hX)
      · by_cases hH' : g ∈ H'
        · exact Or.inl (Or.inl hH')
        · exact Or.inr (Or.inr ⟨hH, hH'⟩)
    · rintro ((hH' | hA) | hX | ⟨hH, _⟩)
      · exact Or.inr (h.subset hH')
      · exact Or.inl (Or.inl hA)
      · exact Or.inl (Or.inr hX)
      · exact Or.inr hH
  have hd2 : Disjoint (famEdges X) (H \ H') :=
    Finset.disjoint_of_subset_right Finset.sdiff_subset hXR
  have hd1 : Disjoint (apexCover H' f) (famEdges X ∪ (H \ H')) := by
    rw [apexCover_eq_union h.apex.nondiag]
    refine Finset.disjoint_union_left.2 ⟨?_, ?_⟩
    · refine Finset.disjoint_union_right.2 ⟨?_, ?_⟩
      · exact Finset.disjoint_of_subset_left (fun g hg => h.subset hg) hXR.symm
      · exact Finset.disjoint_left.2 fun g hg hg' => (Finset.mem_sdiff.1 hg').2 hg
    · refine Finset.disjoint_union_right.2 ⟨h.cross_legs.symm, ?_⟩
      exact Finset.disjoint_of_subset_right Finset.sdiff_subset hHR
  rw [hsplit]
  refine TriDecomp.union hd1 (triDecomp_apexCover h.apex) (TriDecomp.union hd2 ?_ h.rest)
  exact TriFamilyIn.triDecomp (E := famEdges 𝒞) ⟨h.cross_card, h.cross_res, h.cross_disj⟩

/-- **A cross patch absorbs the leftover.**  The whole reservoir together with the leftover is
triangle-decomposable: the consumed edges and the leftover decompose into the apex and cross
triangles, and every cluster gives back what it did not lose. -/
theorem triDecomp_of_crossPatch {E H H' : Finset (Sym2 V)} {𝒞 : Finset (Finset V)}
    {f : Sym2 V → V} {X : Finset (Finset V)} (h𝒞 : ClusterFamilyIn E 𝒞)
    (hdisj : Disjoint (famEdges 𝒞) H) (h : IsCrossPatch 𝒞 H H' f X) :
    TriDecomp (famEdges 𝒞 ∪ H) :=
  triDecomp_reservoir_of_pattern_usage h𝒞 hdisj (routedEdges_subset h)
    (triDecomp_routedEdges_union hdisj h) h.pattern

/-! ### The routing statement, reduced to the existence of cross patches -/

/-- **The remaining gap, in explicit form.**  For every leftover degree bound `D` there is a
covering multiplicity `K` such that inside every pair-covering cluster reservoir every even
leftover of maximum degree at most `D` with `3 ∣ |H|` admits a cross patch: an apex covering of
part of it with reserved legs, and reserved cross triangles patching the parity defects, meeting
every cluster in a pattern.

Compared with `BKLO.ClusterUsageRouting` and `BKLO.ClusterPatternRouting` this contains no
decomposition statement at all: what has to be produced is the choice of apexes and of patching
triangles.  The counting is forced and consistent: the apex covering of `H'` consumes `2|H'|` legs,
each cluster's consumed set has size divisible by three and even degrees
(`BKLO.even_consumed_in_cluster`), and the patching triangles supply three edges each. -/
def CrossPatchExistence : Prop :=
  ∀ D : ℕ, ∃ K : ℕ,
    ∀ {V : Type} [DecidableEq V] (E : Finset (Sym2 V)) (S : Finset V) (𝒞 : Finset (Finset V)),
      E ⊆ cliqueEdges S → ClusterFamilyIn E 𝒞 →
      (∀ e ∈ cliqueEdges S, K ≤ (apexSet (famEdges 𝒞) S e).card) →
      ∀ H : Finset (Sym2 V), H ⊆ E \ famEdges 𝒞 → EvenDegrees H → (∀ v : V, edeg H v ≤ D) →
        3 ∣ H.card →
        ∃ (H' : Finset (Sym2 V)) (f : Sym2 V → V) (X : Finset (Finset V)),
          IsCrossPatch 𝒞 H H' f X

/-- Cross patches suffice: they give the routing, hence (with the reservoir of
`BKLO/ClusterCompletion.lean`) the target. -/
theorem clusterUsageRouting_of_crossPatch (h : CrossPatchExistence) : ClusterUsageRouting := by
  intro D
  obtain ⟨K, hK⟩ := h D
  refine ⟨K, ?_⟩
  intro V _ E S 𝒞 hES h𝒞 hcov H hHsub hHeven hHdeg hHdvd
  obtain ⟨H', f, X, hpatch⟩ := hK E S 𝒞 hES h𝒞 hcov H hHsub hHeven hHdeg hHdvd
  have hdisj : Disjoint (famEdges 𝒞) H :=
    Finset.disjoint_right.2 fun e he he' => (Finset.mem_sdiff.1 (hHsub he)).2 he'
  exact triDecomp_of_crossPatch h𝒞 hdisj hpatch

/-- **The trivial instance.**  A leftover which is already triangle-decomposable — for example a
disjoint union of triangles — is absorbed with the empty cross patch: nothing is consumed and every
cluster is given back whole. -/
theorem isCrossPatch_of_triDecomp (𝒞 : Finset (Finset V)) {H : Finset (Sym2 V)} (hH : TriDecomp H)
    (f : Sym2 V → V) : IsCrossPatch 𝒞 H ∅ f ∅ where
  subset := Finset.empty_subset _
  rest := by simpa using hH
  apex := ⟨by simp, by simp, by simp⟩
  legs := by simp [apexEdges, apexCover, apexFam, famEdges]
  cross_card := by simp
  cross_res := by simp
  cross_disj := by simp
  cross_legs := by simp [famEdges]
  pattern := by
    intro C _
    left
    simp [routedEdges, apexEdges, apexCover, apexFam, famEdges]

/-! ### Checking the pattern condition locally -/

/-- An edge lies in at most one cluster: the clusters of a cluster family are edge-disjoint. -/
theorem cluster_unique_of_mem {E : Finset (Sym2 V)} {𝒞 : Finset (Finset V)}
    (h𝒞 : ClusterFamilyIn E 𝒞) {C C' : Finset V} (hC : C ∈ 𝒞) (hC' : C' ∈ 𝒞) {g : Sym2 V}
    (hg : g ∈ cliqueEdges C) (hg' : g ∈ cliqueEdges C') : C = C' := by
  by_contra hne
  exact (Finset.disjoint_left.1 (h𝒞.2.2 C hC C' hC' hne)) hg hg'

/-- **The pattern condition is local.**  Designate for every cluster `C` the set `F C` of edges it
is meant to lose.  If each `F C` is a pattern inside `C`, is consumed, and catches every consumed
edge of `C`, then the consumed set of every cluster is a pattern.

This is the interface in which a routing built from explicit gadgets — for every leftover vertex a
pairing of its leftover edges and a cluster holding both their apexes, plus a cross triangle for
every three patch edges — is to be checked: no global reasoning is needed, only that a consumed
edge lying in a cluster belongs to that cluster's designated triangle. -/
theorem pattern_of_local {𝒞 : Finset (Finset V)} {U : Finset (Sym2 V)}
    {F : Finset V → Finset (Sym2 V)} (hF : ∀ C ∈ 𝒞, IsClusterPattern C (F C))
    (hFsub : ∀ C ∈ 𝒞, F C ⊆ cliqueEdges C) (hin : ∀ C ∈ 𝒞, F C ⊆ U)
    (hout : ∀ C ∈ 𝒞, ∀ g ∈ U, g ∈ cliqueEdges C → g ∈ F C) :
    ∀ C ∈ 𝒞, IsClusterPattern C (U ∩ cliqueEdges C) := by
  intro C hC
  have : U ∩ cliqueEdges C = F C := by
    apply Finset.Subset.antisymm
    · intro g hg
      exact hout C hC g (Finset.mem_inter.1 hg).1 (Finset.mem_inter.1 hg).2
    · intro g hg
      exact Finset.mem_inter.2 ⟨hin C hC hg, hFsub C hC hg⟩
  rw [this]
  exact hF C hC

/-! ### Routings are trades: a subgraph with two orthogonal decompositions -/

/-- **The crisp form of a routing.**  Let `Γ` be a set of reserved edges which

* meets every cluster in a pattern the cluster gives back (so `Γ` is a union of at most one
  triangle or six-cycle per cluster), and
* contains the legs of an apex covering of `H` and becomes *triangle-decomposable* once those legs
  are removed.

Then `Γ` is the consumed set of a cross patch.  In other words: a routing is a subgraph of the
reservoir carrying two "orthogonal" triangle structures — the cluster patterns on one side, the
patching triangles plus the legs on the other.  (This is why the smallest routings look like
trades: the octahedron `K_{2,2,2}`, whose twelve edges have two disjoint triangle decompositions,
is the smallest closed configuration of four cluster triangles and four patching triangles.) -/
theorem isCrossPatch_of_trade {𝒞 : Finset (Finset V)} {H Γ : Finset (Sym2 V)} {f : Sym2 V → V}
    (hass : IsApexAssignment H f) (hlegs : apexEdges H f ⊆ Γ) (hΓ : Γ ⊆ famEdges 𝒞)
    (hpat : ∀ C ∈ 𝒞, IsClusterPattern C (Γ ∩ cliqueEdges C))
    (hcross : TriDecomp (Γ \ apexEdges H f)) :
    ∃ X : Finset (Finset V), IsCrossPatch 𝒞 H H f X ∧ routedEdges H f X = Γ := by
  classical
  obtain ⟨X, hXcard, hXdisj, hXedges⟩ := hcross
  have hXsub : famEdges X ⊆ famEdges 𝒞 := by
    rw [hXedges]; exact Finset.sdiff_subset.trans hΓ
  have hrouted : routedEdges H f X = Γ := by
    rw [routedEdges, hXedges]
    ext g
    simp only [Finset.mem_union, Finset.mem_sdiff]
    constructor
    · rintro (hA | ⟨hΓg, _⟩)
      · exact hlegs hA
      · exact hΓg
    · intro hg
      by_cases hA : g ∈ apexEdges H f
      · exact Or.inl hA
      · exact Or.inr ⟨hg, hA⟩
  refine ⟨X, ?_, hrouted⟩
  refine ⟨Finset.Subset.refl _, by simpa using (triDecomp_empty : TriDecomp (∅ : Finset (Sym2 V))),
    hass, hlegs.trans hΓ, hXcard, ?_, hXdisj, ?_, ?_⟩
  · intro t ht
    exact (Finset.subset_biUnion_of_mem cliqueEdges ht).trans hXsub
  · rw [hXedges]; exact Finset.sdiff_disjoint
  · intro C hC
    rw [hrouted]
    exact hpat C hC

/-- **A trade absorbs the leftover.**  Combining `BKLO.isCrossPatch_of_trade` with
`BKLO.triDecomp_of_crossPatch`. -/
theorem triDecomp_of_trade {E H Γ : Finset (Sym2 V)} {𝒞 : Finset (Finset V)} {f : Sym2 V → V}
    (h𝒞 : ClusterFamilyIn E 𝒞) (hdisj : Disjoint (famEdges 𝒞) H)
    (hass : IsApexAssignment H f) (hlegs : apexEdges H f ⊆ Γ) (hΓ : Γ ⊆ famEdges 𝒞)
    (hpat : ∀ C ∈ 𝒞, IsClusterPattern C (Γ ∩ cliqueEdges C))
    (hcross : TriDecomp (Γ \ apexEdges H f)) : TriDecomp (famEdges 𝒞 ∪ H) := by
  obtain ⟨X, hX, _⟩ := isCrossPatch_of_trade hass hlegs hΓ hpat hcross
  exact triDecomp_of_crossPatch h𝒞 hdisj hX

/-! ### What a routing is forced to look like -/

/-- **Parity is forced.**  In any routing, the set `U` of reserved edges a cluster loses has even
degrees at every vertex: a `K₇` has all degrees even, and the unused part, being
triangle-decomposable, has even degrees too. -/
theorem even_consumed_in_cluster {C : Finset V} (hC : C.card = 7) {U : Finset (Sym2 V)}
    (hres : TriDecomp (cliqueEdges C \ U)) (v : V) : Even (edeg (cliqueEdges C ∩ U) v) := by
  classical
  have hsplit := edeg_sdiff_add_edeg_inter (cliqueEdges C) U v
  have heven : Even (edeg (cliqueEdges C \ U) v) := hres.triDivisible.1 v
  have hall : edeg (cliqueEdges C) v = if v ∈ C then 6 else 0 := edeg_cliqueEdges_seven hC v
  rcases Nat.even_or_odd (edeg (cliqueEdges C ∩ U) v) with h | h
  · exact h
  · exfalso
    rw [Nat.even_iff] at heven
    rw [Nat.odd_iff] at h
    rw [hall] at hsplit
    by_cases hv : v ∈ C
    · rw [if_pos hv] at hsplit; omega
    · rw [if_neg hv] at hsplit; omega

/-- A leg of the apex covering is an edge joining an endpoint of a leftover edge to its apex. -/
theorem mem_apexEdges_iff_leg {H : Finset (Sym2 V)} {f : Sym2 V → V}
    (hass : IsApexAssignment H f) {g : Sym2 V} (hg : g ∈ apexEdges H f) : ∃ e ∈ H, ∃ u ∈ e, g = s(u, f e) := by
  classical
  obtain ⟨hgcov, hgH⟩ := Finset.mem_sdiff.1 hg
  obtain ⟨t, ht, hgt⟩ := Finset.mem_biUnion.1 hgcov
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 ht
  have := (mem_cliqueEdges_apexTri_iff (hass.nondiag e he) (hass.apex_notMem e he)).1 hgt
  rcases this with rfl | ⟨u, hu, rfl⟩
  · exact absurd he hgH
  · exact ⟨e, he, u, hu, rfl⟩

/-- **The legs must pair up inside clusters.**

Suppose the leftover `H` is covered by apex triangles with reserved legs, with *fresh* apexes (no
apex is a vertex of a leftover edge — the standard situation, cf.
`BKLO.isApexAssignment_of_fresh`), and suppose the routing patches the parity defects with reserved
edges `W` avoiding all vertices touched by the leftover (this is what a cross triangle whose
vertices are untouched by `H` does).  If every cluster is able to give back its unused part, then
at every leftover vertex `x` the legs pair up inside clusters: for every leftover edge `e` at `x`
there is a *second* leftover edge `e'` at `x` whose leg at `x` lies in the same cluster.

This is the *corner condition*.  It is a property of the reservoir — of how the reserved common
neighbours of a pair are distributed among the clusters through a vertex — and not of the leftover;
pair covering says nothing about it.  It is also the exact point at which the naive counting
argument (`2|H|` legs, `4|H|` patch edges, `4|H|/3` cross triangles) stops being sufficient: the
cluster in which a patch edge is consumed is determined by its endpoints, so patches cannot be
matched to defects freely. -/
theorem exists_second_leg_in_cluster {E H : Finset (Sym2 V)} {𝒞 : Finset (Finset V)}
    {f : Sym2 V → V} {W : Finset (Sym2 V)} (h𝒞 : ClusterFamilyIn E 𝒞)
    (hass : IsApexAssignment H f) (hfresh : ∀ e ∈ H, ∀ e' ∈ H, f e ∉ e')
    (hW : ∀ g ∈ W, ∀ u ∈ g, ∀ e ∈ H, u ∉ e)
    (hres : ∀ C ∈ 𝒞, TriDecomp (cliqueEdges C \ (apexEdges H f ∪ W)))
    {e : Sym2 V} (he : e ∈ H) {x : V} (hx : x ∈ e) {C : Finset V} (hC : C ∈ 𝒞)
    (hleg : s(x, f e) ∈ cliqueEdges C) :
    ∃ e' ∈ H, e' ≠ e ∧ x ∈ e' ∧ s(x, f e') ∈ cliqueEdges C := by
  classical
  set U : Finset (Sym2 V) := apexEdges H f ∪ W with hU
  -- the leg of `e` at `x` is one of the consumed edges of `C` at `x`
  have hlegmem : s(x, f e) ∈ apexEdges H f := by
    refine Finset.mem_sdiff.2 ⟨?_, ?_⟩
    · refine Finset.mem_biUnion.2 ⟨apexTri e (f e), Finset.mem_image.2 ⟨e, he, rfl⟩, ?_⟩
      exact (mem_cliqueEdges_apexTri_iff (hass.nondiag e he) (hass.apex_notMem e he)).2
        (Or.inr ⟨x, hx, rfl⟩)
    · intro hmem
      exact hfresh e he _ hmem (by simp)
  -- the consumed edges of `C` at `x`
  set F : Finset (Sym2 V) := (cliqueEdges C ∩ U).filter (fun g => x ∈ g) with hF
  have hmemF : s(x, f e) ∈ F := by
    refine Finset.mem_filter.2 ⟨Finset.mem_inter.2 ⟨hleg, Finset.mem_union_left _ hlegmem⟩, ?_⟩
    simp
  have heven : Even F.card := by
    have := even_consumed_in_cluster (h𝒞.1 C hC) (hres C hC) x
    simpa [edeg, hF] using this
  -- an even nonempty set has a second element
  have hcard : 1 < F.card := by
    have hpos : 0 < F.card := Finset.card_pos.2 ⟨_, hmemF⟩
    obtain ⟨k, hk⟩ := heven
    omega
  obtain ⟨g, hgF, hgne⟩ := Finset.exists_mem_ne hcard (s(x, f e))
  -- that second edge is a leg, at `x`, of another leftover edge
  obtain ⟨hgU, hgx⟩ := Finset.mem_filter.1 hgF
  obtain ⟨hgC, hgU⟩ := Finset.mem_inter.1 hgU
  have hgapex : g ∈ apexEdges H f := by
    rcases Finset.mem_union.1 hgU with h | h
    · exact h
    · exact absurd he (fun he' => hW g h x hgx e he' hx)
  obtain ⟨e', he', u, hu, rfl⟩ := mem_apexEdges_iff_leg hass hgapex
  -- `x` is the endpoint, not the apex (the apex is fresh)
  have hxu : x = u := by
    have : x = u ∨ x = f e' := by
      rcases Sym2.mem_iff.1 hgx with h | h
      · exact Or.inl h
      · exact Or.inr h
    rcases this with h | h
    · exact h
    · exact absurd hx (by rw [h]; exact hfresh e' he' e he)
  subst hxu
  refine ⟨e', he', ?_, hu, hgC⟩
  rintro rfl
  exact hgne rfl

/-! ### The property of the reservoir that a routing needs -/

/-- **Corner covering.**  For every vertex `x` and every pair `y, y'` of vertices there is a
cluster through `x` containing a reserved neighbour of `y` and a *different* reserved neighbour of
`y'`.

This is what an apex covering needs in order to have its legs pair up inside clusters: covering the
two leftover edges `xy`, `xy'` by apexes `z`, `z'` puts the legs `xz`, `xz'` into the clusters
containing them, and unless those clusters coincide the parity of `x` inside them is wrong.  Pair
covering — `K` reserved common neighbours for every pair — is a statement about the *number* of
available apexes and says nothing about how they are distributed among the clusters through `x`,
which is what corner covering controls.  Counting leaves room for it: a vertex lies in about
`γ|S|/6` clusters, each of which reaches about `7γ|S|` vertices by a reserved edge and so covers
about `49γ²|S|²` corners, giving about `8γ³|S|³` corners against the `|S|²` that must be covered. -/
def CornerCovering (𝒞 : Finset (Finset V)) (S : Finset V) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, ∀ y' ∈ S, ∃ C ∈ 𝒞, x ∈ C ∧ ∃ z ∈ C, ∃ z' ∈ C, z ≠ z' ∧
    s(y, z) ∈ famEdges 𝒞 ∧ s(y', z') ∈ famEdges 𝒞

/-- **Corner covering is necessary.**  If a leftover with exactly the two edges `xy` and `xy'` at
`x` (the second edge is not assumed to be present; `honly` only limits which edges can occur) is
routed with fresh apexes and with patches avoiding the vertices it touches, then the
reservoir contains the corner configuration at `(x, y, y')`: one cluster through `x` holding a
reserved neighbour of `y` and a different reserved neighbour of `y'`.

So the routing gap is not only a matching problem for a fixed reservoir; it needs the reservoir to
have a property that `BKLO.ClusterReservoirExistence` does not assert. -/
theorem corner_of_routing {E H : Finset (Sym2 V)} {𝒞 : Finset (Finset V)} {f : Sym2 V → V}
    {W : Finset (Sym2 V)} (h𝒞 : ClusterFamilyIn E 𝒞)
    (hass : IsApexAssignment H f) (hfresh : ∀ e ∈ H, ∀ e' ∈ H, f e ∉ e')
    (hlegs : apexEdges H f ⊆ famEdges 𝒞)
    (hW : ∀ g ∈ W, ∀ u ∈ g, ∀ e ∈ H, u ∉ e)
    (hres : ∀ C ∈ 𝒞, TriDecomp (cliqueEdges C \ (apexEdges H f ∪ W)))
    {x y y' : V} (he : s(x, y) ∈ H)
    (honly : ∀ g ∈ H, x ∈ g → g = s(x, y) ∨ g = s(x, y')) (hyy' : s(x, y) ≠ s(x, y')) :
    ∃ C ∈ 𝒞, x ∈ C ∧ ∃ z ∈ C, ∃ z' ∈ C, z ≠ z' ∧
      s(y, z) ∈ famEdges 𝒞 ∧ s(y', z') ∈ famEdges 𝒞 := by
  classical
  -- the leg of `xy` at `x` is reserved, so it lies in a cluster
  have hlegmem : s(x, f s(x, y)) ∈ apexEdges H f := by
    refine Finset.mem_sdiff.2 ⟨?_, ?_⟩
    · refine Finset.mem_biUnion.2 ⟨apexTri s(x, y) (f s(x, y)),
        Finset.mem_image.2 ⟨_, he, rfl⟩, ?_⟩
      exact (mem_cliqueEdges_apexTri_iff (hass.nondiag _ he) (hass.apex_notMem _ he)).2
        (Or.inr ⟨x, by simp, rfl⟩)
    · intro hmem
      exact hfresh _ he _ hmem (by simp)
  obtain ⟨C, hC, hlegC⟩ := Finset.mem_biUnion.1 (hlegs hlegmem)
  obtain ⟨g, hg, hgne, hgx, hgC⟩ :=
    exists_second_leg_in_cluster h𝒞 hass hfresh hW hres he (by simp) hC hlegC
  -- the second leftover edge at `x` is `xy'`
  have hgeq : g = s(x, y') := by
    rcases honly g hg hgx with h | h
    · exact absurd h hgne
    · exact h
  subst hgeq
  refine ⟨C, hC, (mem_cliqueEdgesV.1 hlegC).1 x (by simp), f s(x, y),
    (mem_cliqueEdgesV.1 hlegC).1 _ (by simp), f s(x, y'),
    (mem_cliqueEdgesV.1 hgC).1 _ (by simp), ?_, ?_, ?_⟩
  · -- distinct apexes: otherwise the two covering triangles share the leg at `x`
    intro hcon
    have hd := hass.edge_disjoint _ he _ hg hyy'
    refine (Finset.disjoint_left.1 hd) (a := s(x, f s(x, y))) ?_ ?_
    · exact (mem_cliqueEdges_apexTri_iff (hass.nondiag _ he) (hass.apex_notMem _ he)).2
        (Or.inr ⟨x, by simp, rfl⟩)
    · rw [hcon]
      exact (mem_cliqueEdges_apexTri_iff (hass.nondiag _ hg) (hass.apex_notMem _ hg)).2
        (Or.inr ⟨x, by simp, rfl⟩)
  · -- the leg at the other endpoint is reserved as well
    refine hlegs (Finset.mem_sdiff.2 ⟨?_, ?_⟩)
    · refine Finset.mem_biUnion.2 ⟨apexTri s(x, y) (f s(x, y)),
        Finset.mem_image.2 ⟨_, he, rfl⟩, ?_⟩
      exact (mem_cliqueEdges_apexTri_iff (hass.nondiag _ he) (hass.apex_notMem _ he)).2
        (Or.inr ⟨y, by simp, rfl⟩)
    · intro hmem
      exact hfresh _ he _ hmem (by simp)
  · refine hlegs (Finset.mem_sdiff.2 ⟨?_, ?_⟩)
    · refine Finset.mem_biUnion.2 ⟨apexTri s(x, y') (f s(x, y')),
        Finset.mem_image.2 ⟨_, hg, rfl⟩, ?_⟩
      exact (mem_cliqueEdges_apexTri_iff (hass.nondiag _ hg) (hass.apex_notMem _ hg)).2
        (Or.inr ⟨y', by simp, rfl⟩)
    · intro hmem
      exact hfresh _ hg _ hmem (by simp)

end BKLO
