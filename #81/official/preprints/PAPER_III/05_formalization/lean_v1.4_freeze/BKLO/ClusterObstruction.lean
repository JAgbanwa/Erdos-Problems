/-
# The limit of the per-cluster mechanism: spread leftovers.

`BKLO/ClusterReservoir.lean` reduces the bounded-leftover absorber to a routing statement, and
supplies the mechanism that makes a cluster reservoir work: whatever a cluster loses, it gives back
the rest, provided what it loses is a *pattern* — nothing, a triangle, or a six-cycle
(`BKLO.triDecomp_reservoir_of_pattern_usage`).  All three patterns have even degrees, and this is
forced: a cluster is a `K₇`, so every vertex of it has even degree `6`, and if the unused part is to
be triangle-decomposable then the consumed part must have even degrees too.

This file proves that this per-cluster mechanism has a hard limit.  Call a leftover **spread** (for
a given cluster family) if no cluster contains two distinct vertices touched by the leftover — for
a sparse reservoir this is the typical situation, since a vertex has only `O(γ|S|)` cluster
partners out of `|S|` vertices.  Then, for a *nonempty* spread leftover covered by apex triangles
with reserved legs, some cluster is left with a vertex of odd degree, and its unused part is *not*
triangle-decomposable (`BKLO.exists_cluster_not_triDecomp_of_spread`).

The mechanism is exactly this: a leg is an edge `{x, w}` with `x` touched by the leftover and `w`
its apex; the two legs of one covering triangle can never lie in the same cluster (the leftover
edge itself is not reserved), so inside a cluster the apex `w` of a leg receives exactly one leg
unless a second leftover vertex of that cluster also sends it one.  With a spread leftover there is
no second leftover vertex, so `w` has odd degree.

The consequence for the blueprint is precise: a *per-cluster* give-back cannot absorb spread
leftovers, and the remaining routing statement `BKLO.ClusterUsageRouting` — which is not restricted
to per-cluster give-back, and allows the repairing triangles to use reserved edges of several
clusters at once — has to be attacked with triangles that cross clusters.  Everything here is
`sorry`-free.
-/
import BKLO.ClusterCompletion

open Finset

namespace BKLO

variable {V : Type*} [DecidableEq V]

/-! ### Degrees and set difference -/

/-- The degree of a vertex splits along a set difference. -/
theorem edeg_sdiff_add_edeg_inter (A B : Finset (Sym2 V)) (v : V) :
    edeg (A \ B) v + edeg (A ∩ B) v = edeg A v := by
  classical
  unfold edeg
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext e
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_inter]
    tauto
  · refine Finset.disjoint_left.2 ?_
    intro e he he'
    simp only [Finset.mem_filter, Finset.mem_sdiff] at he
    simp only [Finset.mem_filter, Finset.mem_inter] at he'
    exact he.1.2 he'.1.2

/-! ### Spread leftovers defeat the per-cluster mechanism -/

/-- **The obstruction.**  Let the leftover `H` be nonempty and *spread*: no cluster contains two
distinct vertices touched by `H`.  Cover `H` by apex triangles whose legs are all reserved.  Then
some cluster has a vertex of odd degree in the unused part, so that part is not
triangle-decomposable: the reservoir cannot be given back cluster by cluster.

The cluster exhibited is the one containing a leg `{x, w}` of a covering triangle; the offending
vertex is the apex `w`, which receives that one leg and — for want of a second leftover vertex in
the cluster — no other. -/
theorem exists_cluster_not_triDecomp_of_spread {E H : Finset (Sym2 V)} {𝒞 : Finset (Finset V)}
    {f : Sym2 V → V} (h𝒞 : ClusterFamilyIn E 𝒞) (hdisj : Disjoint (famEdges 𝒞) H)
    (hass : IsApexAssignment H f) (hlegs : ∀ e ∈ H, ∀ u ∈ e, s(u, f e) ∈ famEdges 𝒞)
    (hspread : ∀ C ∈ 𝒞, ∀ x ∈ C, ∀ y ∈ C, (∃ e ∈ H, x ∈ e) → (∃ e ∈ H, y ∈ e) → x = y)
    (hne : H.Nonempty) :
    ∃ C ∈ 𝒞, ¬ TriDecomp (cliqueEdges C \ apexEdges H f) := by
  classical
  obtain ⟨e₀, he₀⟩ := hne
  have hnd : ¬ e₀.IsDiag := hass.nondiag e₀ he₀
  revert he₀ hnd
  induction e₀ using Sym2.ind with
  | _ x y =>
  intro he₀ hnd
  set w : V := f s(x, y) with hw
  have hwmem : w ∉ s(x, y) := hass.apex_notMem _ he₀
  have hwx : w ≠ x := fun h => hwmem (by rw [h]; simp)
  -- the leg `{x, w}` is reserved, hence not in `H`, hence an apex edge
  have hlegres : s(x, w) ∈ famEdges 𝒞 := hlegs _ he₀ x (by simp)
  have hlegH : s(x, w) ∉ H := Finset.disjoint_left.1 hdisj hlegres
  have hxwtri : s(x, w) ∈ cliqueEdges (apexTri s(x, y) w) := by
    refine mem_cliqueEdgesV.2 ⟨?_, ?_⟩
    · intro z hz
      simp only [Sym2.mem_iff] at hz
      rcases hz with rfl | rfl
      · exact Finset.mem_insert_of_mem (by simp)
      · exact Finset.mem_insert_self _ _
    · simpa [Sym2.isDiag_iff_proj_eq] using fun h => hwx h.symm
  have hlegapex : s(x, w) ∈ apexEdges H f := by
    refine Finset.mem_sdiff.2 ⟨?_, hlegH⟩
    exact Finset.mem_biUnion.2 ⟨apexTri s(x, y) w, Finset.mem_image.2 ⟨_, he₀, rfl⟩, hxwtri⟩
  -- the cluster containing that leg
  obtain ⟨C, hC, hxwC⟩ := Finset.mem_biUnion.1 hlegres
  have hxC : x ∈ C := (mem_cliqueEdgesV.1 hxwC).1 x (by simp)
  have hwC : w ∈ C := (mem_cliqueEdgesV.1 hxwC).1 w (by simp)
  -- the apex `w` is not touched by `H`
  have hxtouch : ∃ e ∈ H, x ∈ e := ⟨s(x, y), he₀, by simp⟩
  have hwuntouched : ¬ ∃ e ∈ H, w ∈ e := by
    rintro hwt
    exact hwx (hspread C hC w hwC x hxC hwt hxtouch)
  -- `{x, w}` is the only apex edge at `w` inside the cluster
  have hfilter : (cliqueEdges C ∩ apexEdges H f).filter (fun g => w ∈ g) = {s(x, w)} := by
    ext g
    simp only [Finset.mem_filter, Finset.mem_inter, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨hgC, hgapex⟩, hwg⟩
      obtain ⟨u, rfl⟩ := Sym2.mem_iff_exists.1 hwg
      obtain ⟨t, ht, hgt⟩ := Finset.mem_biUnion.1 (Finset.mem_sdiff.1 hgapex).1
      obtain ⟨e', he', rfl⟩ := Finset.mem_image.1 ht
      have hsub := (mem_cliqueEdgesV.1 hgt).1
      have huv : u ∈ apexTri e' (f e') := hsub u (by simp)
      have hwv : w ∈ apexTri e' (f e') := hsub w (by simp)
      have hwne : w ≠ u := by
        have := (mem_cliqueEdgesV.1 hgt).2
        simpa [Sym2.isDiag_iff_proj_eq] using this
      -- `w` is not an endpoint of `e'`, so it is the apex of `e'`
      have hwapex : w = f e' := by
        rcases Finset.mem_insert.1 hwv with h | h
        · exact h
        · exact absurd ⟨e', he', by simpa using h⟩ hwuntouched
      have hue : u ∈ e' := by
        rcases Finset.mem_insert.1 huv with h | h
        · exact absurd (h.trans hwapex.symm).symm hwne
        · simpa using h
      have huC : u ∈ C := (mem_cliqueEdgesV.1 hgC).1 u (by simp)
      have hux : u = x := hspread C hC u huC x hxC ⟨e', he', hue⟩ hxtouch
      rw [hux, Sym2.eq_swap]
    · rintro rfl
      exact ⟨⟨hxwC, hlegapex⟩, by simp⟩
  have hone : edeg (cliqueEdges C ∩ apexEdges H f) w = 1 := by
    unfold edeg
    rw [hfilter, Finset.card_singleton]
  have hsix : edeg (cliqueEdges C) w = 6 := by
    rw [edeg_cliqueEdges_seven (h𝒞.1 C hC), if_pos hwC]
  refine ⟨C, hC, fun hdec => ?_⟩
  have heven : Even (edeg (cliqueEdges C \ apexEdges H f) w) := hdec.triDivisible.1 w
  have hsplit := edeg_sdiff_add_edeg_inter (cliqueEdges C) (apexEdges H f) w
  rw [hone, hsix] at hsplit
  rw [Nat.even_iff] at heven
  omega

/-- **Consequently, no cluster pattern criterion applies to a spread leftover.**  Under the
hypotheses above, the legs of the covering do not meet the clusters in patterns; the reservoir
cannot be handed back cluster by cluster, and the routing has to use triangles crossing clusters. -/
theorem not_forall_isClusterPattern_of_spread {E H : Finset (Sym2 V)} {𝒞 : Finset (Finset V)}
    {f : Sym2 V → V} (h𝒞 : ClusterFamilyIn E 𝒞) (hdisj : Disjoint (famEdges 𝒞) H)
    (hass : IsApexAssignment H f) (hlegs : ∀ e ∈ H, ∀ u ∈ e, s(u, f e) ∈ famEdges 𝒞)
    (hspread : ∀ C ∈ 𝒞, ∀ x ∈ C, ∀ y ∈ C, (∃ e ∈ H, x ∈ e) → (∃ e ∈ H, y ∈ e) → x = y)
    (hne : H.Nonempty) :
    ¬ ∀ C ∈ 𝒞, IsClusterPattern C (apexEdges H f ∩ cliqueEdges C) := by
  classical
  obtain ⟨C, hC, hnot⟩ :=
    exists_cluster_not_triDecomp_of_spread h𝒞 hdisj hass hlegs hspread hne
  intro hpat
  refine hnot ?_
  have hsplit : cliqueEdges C \ apexEdges H f
      = cliqueEdges C \ (apexEdges H f ∩ cliqueEdges C) := by
    ext e
    simp only [Finset.mem_sdiff, Finset.mem_inter]
    tauto
  rw [hsplit]
  exact triDecomp_cliqueEdges_sdiff_pattern (h𝒞.1 C hC) (hpat C hC)

/-! ### The structure of reserved triangles

A cluster is a *complete* graph, and clusters are edge-disjoint.  Consequently a triangle all of
whose edges are reserved is of exactly one of two kinds: it lies inside a single cluster, or its
three edges lie in three pairwise distinct clusters.  This is the mechanism available for repairing
the parity defects that the obstruction above exhibits: a **cross triangle** consumes exactly one
edge in each of three different clusters, so it can be used to patch three clusters at once. -/

/-- Two edges of a triangle inside one cluster force the third edge into that cluster. -/
theorem third_edge_mem_cluster {C : Finset V} {a b c : V} (hac : a ≠ c)
    (hab : s(a, b) ∈ cliqueEdges C) (hbc : s(b, c) ∈ cliqueEdges C) :
    s(a, c) ∈ cliqueEdges C := by
  refine mem_cliqueEdgesV.2 ⟨?_, by simpa [Sym2.isDiag_iff_proj_eq] using hac⟩
  intro z hz
  simp only [Sym2.mem_iff] at hz
  rcases hz with rfl | rfl
  · exact (mem_cliqueEdgesV.1 hab).1 z (by simp)
  · exact (mem_cliqueEdgesV.1 hbc).1 z (by simp)

/-- **A reserved triangle is inside a cluster, or meets three distinct clusters.**  If two of its
edges lie in two *different* clusters, the third edge lies in neither of them. -/
theorem third_edge_notMem_clusters {E : Finset (Sym2 V)} {𝒞 : Finset (Finset V)}
    (h𝒞 : ClusterFamilyIn E 𝒞) {C₁ C₂ : Finset V} (hC₁ : C₁ ∈ 𝒞) (hC₂ : C₂ ∈ 𝒞) (hne : C₁ ≠ C₂)
    {a b c : V} (hac : a ≠ c) (hab : s(a, b) ∈ cliqueEdges C₁) (hbc : s(b, c) ∈ cliqueEdges C₂) :
    s(a, c) ∉ cliqueEdges C₁ ∧ s(a, c) ∉ cliqueEdges C₂ := by
  constructor
  · intro hmem
    have hb : s(b, c) ∈ cliqueEdges C₁ := by
      have := third_edge_mem_cluster (a := b) (b := a) (c := c) (by
        rintro rfl
        exact (mem_cliqueEdgesV.1 hbc).2 (by simp [Sym2.isDiag_iff_proj_eq]))
        (by rwa [Sym2.eq_swap]) hmem
      exact this
    exact Finset.disjoint_left.1 (h𝒞.2.2 C₁ hC₁ C₂ hC₂ hne) hb hbc
  · intro hmem
    have hb : s(a, b) ∈ cliqueEdges C₂ := by
      have := third_edge_mem_cluster (a := a) (b := c) (c := b) (by
        rintro rfl
        exact (mem_cliqueEdgesV.1 hab).2 (by simp [Sym2.isDiag_iff_proj_eq]))
        hmem (by rwa [Sym2.eq_swap])
      exact this
    exact Finset.disjoint_left.1 (h𝒞.2.2 C₁ hC₁ C₂ hC₂ hne) hab hb

end BKLO
