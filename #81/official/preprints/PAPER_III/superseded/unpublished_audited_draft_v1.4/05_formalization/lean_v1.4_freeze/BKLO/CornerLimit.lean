/-
# What a corner routing forces the reservoir to contain

`BKLO/CornerRouting.lean` shows that *corner data* absorbs a bounded-degree leftover, and states the
remaining gap as `BKLO.CornerReservoirExistence`: a sparse cluster reservoir providing corner data
for every even bounded-degree leftover.  This file proves the sharp limitation of that mechanism.

The observation is that a corner routing forces a **triangle of reserved edges linking three
vertices of the leftover**.  Indeed the patch edges — one per transition — have to group into
triangles, and:

* distinct transitions get distinct corner clusters, and a cluster is determined by any one of its
  edges, so distinct transitions have distinct patch edges;
* two transitions at the *same* vertex `x` cannot have patch edges sharing an apex `b`, since the
  leg `xb` would then lie in both their corner clusters.

So the three patch edges of a patch triangle `abc` come from transitions at three *distinct*
vertices `x, y, z`, and the clusters of the three transitions witness
`BKLO.CornerLinked 𝒞 x y z`: a triangle `abc` of reserved edges together with, for each of its
edges, a vertex of the cluster of that edge.  This is `BKLO.exists_cornerLinked_of_cornerRouting`.

The condition is a genuine constraint on the reservoir, and it is *scarce*: a reservoir of maximum
degree `γ|S|` contains at most `γ²|S|³` triangles, and each of them links at most `7³` vertex
triples, whereas a leftover triangle may sit on **any** three vertices.  Counting therefore refutes
the statement outright: `BKLO.not_cornerReservoirExistence`.

This is not a defect of the corner mechanism alone: the same count applies to any routing whose
patch edges are reserved, and it says that the *pairing* of the legs at a vertex through a single
cluster (which is what makes a patch edge appear) can only be afforded for the triples the reservoir
happens to link.

Everything in this file is `sorry`-free.
-/
import BKLO.CornerRouting

open Finset

namespace BKLO

variable {V : Type*} [DecidableEq V]

/-! ### Corner-linked triples -/

/-- Three vertices are **corner-linked** by the reservoir `𝒞` if there is a triangle `abc` of
reserved edges such that `x` lies in the cluster of `ab`, `y` in the cluster of `bc` and `z` in the
cluster of `ca`.  (The clusters are recorded explicitly; since clusters are edge-disjoint, the
cluster containing a given edge is unique.) -/
def CornerLinked (𝒞 : Finset (Finset V)) (x y z : V) : Prop :=
  ∃ a b c : V, a ≠ b ∧ b ≠ c ∧ a ≠ c ∧
    ∃ Cx ∈ 𝒞, ∃ Cy ∈ 𝒞, ∃ Cz ∈ 𝒞,
      x ∈ Cx ∧ a ∈ Cx ∧ b ∈ Cx ∧
      y ∈ Cy ∧ b ∈ Cy ∧ c ∈ Cy ∧
      z ∈ Cz ∧ c ∈ Cz ∧ a ∈ Cz

omit [DecidableEq V] in
theorem CornerLinked.rotate {𝒞 : Finset (Finset V)} {x y z : V} (h : CornerLinked 𝒞 x y z) :
    CornerLinked 𝒞 y z x := by
  obtain ⟨a, b, c, hab, hbc, hac, Cx, hCx, Cy, hCy, Cz, hCz, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨b, c, a, hbc, hac.symm, hab.symm, Cy, hCy, Cz, hCz, Cx, hCx,
    h4, h5, h6, h7, h8, h9, h1, h2, h3⟩

omit [DecidableEq V] in
theorem CornerLinked.swap {𝒞 : Finset (Finset V)} {x y z : V} (h : CornerLinked 𝒞 x y z) :
    CornerLinked 𝒞 x z y := by
  obtain ⟨a, b, c, hab, hbc, hac, Cx, hCx, Cy, hCy, Cz, hCz, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨b, a, c, hab.symm, hac, hbc, Cx, hCx, Cz, hCz, Cy, hCy,
    h1, h3, h2, h7, h9, h8, h4, h6, h5⟩

/-! ### Corner data attached to a patch edge -/

variable {E : Finset (Sym2 V)} {𝒞 : Finset (Finset V)} {H : Finset (Sym2 V)} {f : Sym2 V → V}
  {Tr : Finset (Transition V)} {cl : Transition V → Finset V}

/-- The corner cluster of a transition contains its vertex and the two endpoints of its patch
edge, all three distinct. -/
theorem corner_data_of_patch (h : IsCornerRouting 𝒞 H f Tr cl) {τ : Transition V} (hτ : τ ∈ Tr)
    {a b : V} (hab : transPatch f τ = s(a, b)) :
    cl τ ∈ 𝒞 ∧ τ.1 ∈ cl τ ∧ a ∈ cl τ ∧ b ∈ cl τ ∧ τ.1 ≠ a ∧ τ.1 ≠ b ∧ a ≠ b := by
  have hsub := h.corner τ hτ
  have h1 : τ.1 ∈ cl τ := hsub (by simp [transTri])
  have h2 : f τ.2.1 ∈ cl τ := hsub (by simp [transTri])
  have h3 : f τ.2.2 ∈ cl τ := hsub (by simp [transTri])
  have hne1 := h.ne_apex₁ hτ
  have hne2 := h.ne_apex₂ hτ
  have hne3 := h.apex_ne hτ
  rw [transPatch, Sym2.eq_iff] at hab
  rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨h.cluster_mem τ hτ, h1, h2, h3, hne1, hne2, hne3⟩
  · exact ⟨h.cluster_mem τ hτ, h1, h3, h2, hne2, hne1, hne3.symm⟩

/-- The leg joining the vertex of a transition to an endpoint of its patch edge is an edge of the
corner cluster. -/
theorem leg_mem_cliqueEdges_cl (h : IsCornerRouting 𝒞 H f Tr cl) {τ : Transition V} (hτ : τ ∈ Tr)
    {a b : V} (hab : transPatch f τ = s(a, b)) : s(τ.1, b) ∈ cliqueEdges (cl τ) := by
  obtain ⟨_, h1, _, h3, _, hne2, _⟩ := corner_data_of_patch h hτ hab
  refine mem_cliqueEdgesV.2 ⟨?_, ?_⟩
  · intro u hu
    rcases Sym2.mem_iff.1 hu with rfl | rfl
    · exact h1
    · exact h3
  · simpa [Sym2.isDiag_iff_proj_eq] using hne2

/-- **Two transitions whose patch edges share an apex sit at different vertices.**  If they sat at
the same vertex, the leg to the shared apex would lie in both their corner clusters, so the
clusters, and hence the transitions, would coincide — and then their patch edges would coincide
too. -/
theorem trans_vertex_ne (h𝒞 : ClusterFamilyIn E 𝒞) (h : IsCornerRouting 𝒞 H f Tr cl)
    {τ σ : Transition V} (hτ : τ ∈ Tr) (hσ : σ ∈ Tr) {a b c : V}
    (hab : transPatch f τ = s(a, b)) (hbc : transPatch f σ = s(b, c)) (hac : a ≠ c) :
    τ.1 ≠ σ.1 := by
  intro hxy
  have h1 : s(τ.1, b) ∈ cliqueEdges (cl τ) := leg_mem_cliqueEdges_cl h hτ hab
  have h2 : s(σ.1, b) ∈ cliqueEdges (cl σ) := by
    have := leg_mem_cliqueEdges_cl h hσ (a := c) (b := b) (by rw [hbc]; exact Sym2.eq_swap)
    exact this
  rw [← hxy] at h2
  have hcl : cl τ = cl σ :=
    cluster_unique_of_mem h𝒞 (h.cluster_mem τ hτ) (h.cluster_mem σ hσ) h1 h2
  have hts : τ = σ := h.cluster_inj τ hτ σ hσ hcl
  subst hts
  rw [hab] at hbc
  rw [Sym2.eq_iff] at hbc
  obtain ⟨hb, hc⟩ | ⟨hb, hc⟩ := hbc
  · exact ((corner_data_of_patch h hτ hab).2.2.2.2.2.2) hb
  · exact hac hb

/-! ### The linked triple produced by a routing -/

/-- **A corner routing of a nonempty leftover links three of its vertices.**

The patch edges group into triangles; the three edges of one such triangle are the patch edges of
three transitions, which sit at three distinct vertices of the leftover, and the corner clusters of
those transitions exhibit `BKLO.CornerLinked`. -/
theorem exists_cornerLinked_of_cornerRouting (h𝒞 : ClusterFamilyIn E 𝒞)
    (h : IsCornerRouting 𝒞 H f Tr cl) (hne : H.Nonempty) :
    ∃ x y z : V, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      (∃ e ∈ H, x ∈ e) ∧ (∃ e ∈ H, y ∈ e) ∧ (∃ e ∈ H, z ∈ e) ∧ CornerLinked 𝒞 x y z := by
  classical
  -- some transition exists
  obtain ⟨e, he⟩ := hne
  have hnd : ¬ e.IsDiag := h.apex.nondiag e he
  obtain ⟨u, hu⟩ : ∃ u, u ∈ e := by
    induction e using Sym2.ind with
    | _ p q => exact ⟨p, by simp⟩
  obtain ⟨τ₀, hτ₀, _, _⟩ := h.pairing e he u hu
  -- a patch triangle
  obtain ⟨P, hP3, _, hPfam⟩ := h.patch
  have hp0 : transPatch f τ₀ ∈ patchEdges f Tr := Finset.mem_image.2 ⟨τ₀, hτ₀, rfl⟩
  obtain ⟨t, htP, _⟩ := Finset.mem_biUnion.1 (hPfam ▸ hp0)
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.1 (hP3 t htP)
  have hsub : cliqueEdges ({a, b, c} : Finset V) ⊆ patchEdges f Tr := by
    rw [← hPfam]
    exact Finset.subset_biUnion_of_mem cliqueEdges htP
  rw [cliqueEdgesV_triple hab hbc hac] at hsub
  have hE1 : s(a, b) ∈ patchEdges f Tr := hsub (by simp)
  have hE2 : s(b, c) ∈ patchEdges f Tr := hsub (by simp)
  have hE3 : s(a, c) ∈ patchEdges f Tr := hsub (by simp)
  obtain ⟨τ, hτ, hpτ⟩ := Finset.mem_image.1 hE1
  obtain ⟨σ, hσ, hpσ⟩ := Finset.mem_image.1 hE2
  obtain ⟨ρ, hρ, hpρ⟩ := Finset.mem_image.1 hE3
  -- the three vertices are distinct
  have hxy : τ.1 ≠ σ.1 := trans_vertex_ne h𝒞 h hτ hσ hpτ hpσ hac
  have hyz : σ.1 ≠ ρ.1 :=
    trans_vertex_ne h𝒞 h hσ hρ hpσ (by rw [hpρ]; exact Sym2.eq_swap) hab.symm
  have hxz : τ.1 ≠ ρ.1 :=
    trans_vertex_ne h𝒞 h hτ hρ (by rw [hpτ]; exact Sym2.eq_swap) hpρ hbc
  -- and they carry corner data
  obtain ⟨hCτ, hτ1, hτa, hτb, _, _, _⟩ := corner_data_of_patch h hτ hpτ
  obtain ⟨hCσ, hσ1, hσb, hσc, _, _, _⟩ := corner_data_of_patch h hσ hpσ
  obtain ⟨hCρ, hρ1, hρc, hρa, _, _, _⟩ :=
    corner_data_of_patch h hρ (a := c) (b := a) (by rw [hpρ]; exact Sym2.eq_swap)
  refine ⟨τ.1, σ.1, ρ.1, hxy, hyz, hxz, ⟨τ.2.1, h.trans_edge₁ τ hτ, h.trans_at₁ τ hτ⟩,
    ⟨σ.2.1, h.trans_edge₁ σ hσ, h.trans_at₁ σ hσ⟩,
    ⟨ρ.2.1, h.trans_edge₁ ρ hρ, h.trans_at₁ ρ hρ⟩, ?_⟩
  exact ⟨a, b, c, hab, hbc, hac, cl τ, hCτ, cl σ, hCσ, cl ρ, hCρ,
    hτ1, hτa, hτb, hσ1, hσb, hσc, hρ1, hρc, hρa⟩

/-- **No corner routing without a linked triple.**  If the reservoir links no three vertices of the
nonempty leftover, then the leftover has no corner routing at all — in particular no *part* of a
leftover whose vertices are pairwise unlinked can be routed, so this obstruction is not an artefact
of asking to route the whole leftover. -/
theorem not_cornerRouting_of_unlinked (h𝒞 : ClusterFamilyIn E 𝒞) (hne : H.Nonempty)
    (hun : ∀ x y z : V, (∃ e ∈ H, x ∈ e) → (∃ e ∈ H, y ∈ e) → (∃ e ∈ H, z ∈ e) →
      ¬ CornerLinked 𝒞 x y z) :
    ¬ ∃ (f : Sym2 V → V) (Tr : Finset (Transition V)) (cl : Transition V → Finset V),
        IsCornerRouting 𝒞 H f Tr cl := by
  rintro ⟨f, Tr, cl, hroute⟩
  obtain ⟨x, y, z, _, _, _, hx, hy, hz, hlink⟩ :=
    exists_cornerLinked_of_cornerRouting h𝒞 hroute hne
  exact hun x y z hx hy hz hlink

/-! ### Counting: a sparse reservoir links few triples -/

/-- The cluster containing a given reserved edge (`∅` if there is none).  It is well defined
because clusters are edge-disjoint (`BKLO.clusterOf_eq`). -/
noncomputable def clusterOf (𝒞 : Finset (Finset V)) (e : Sym2 V) : Finset V :=
  open Classical in
  if h : ∃ C, C ∈ 𝒞 ∧ e ∈ cliqueEdges C then h.choose else ∅

theorem clusterOf_eq (h𝒞 : ClusterFamilyIn E 𝒞) {C : Finset V} (hC : C ∈ 𝒞) {e : Sym2 V}
    (he : e ∈ cliqueEdges C) : clusterOf 𝒞 e = C := by
  have hex : ∃ C, C ∈ 𝒞 ∧ e ∈ cliqueEdges C := ⟨C, hC, he⟩
  rw [clusterOf, dif_pos hex]
  obtain ⟨hC', he'⟩ := hex.choose_spec
  exact cluster_unique_of_mem h𝒞 hC' hC he' he

/-- The reserved neighbours of a vertex. -/
def resNbr [Fintype V] (R : Finset (Sym2 V)) (a : V) : Finset V :=
  Finset.univ.filter (fun b => s(a, b) ∈ R)

theorem card_resNbr_le [Fintype V] {R : Finset (Sym2 V)} (a : V) :
    (resNbr R a).card ≤ edeg R a := by
  classical
  refine Finset.card_le_card_of_injOn (fun b => s(a, b)) ?_ ?_
  · intro b hb
    have hb' : s(a, b) ∈ R := by simpa [resNbr] using hb
    exact Finset.mem_coe.2 (Finset.mem_filter.2 ⟨hb', by simp⟩)
  · intro b _ b' _ hbb'
    rw [Sym2.eq_iff] at hbb'
    rcases hbb' with ⟨_, h⟩ | ⟨h1, h2⟩
    · exact h
    · exact h2.trans h1

/-- A crude bound for a set of triples described by a first and a second choice. -/
theorem card_triples_le [Fintype V] {T : Finset (V × V × V)} {A : V → Finset V}
    {B : V → V → Finset V} (hT : ∀ p ∈ T, p.2.1 ∈ A p.1 ∧ p.2.2 ∈ B p.1 p.2.1) {m k : ℕ}
    (hA : ∀ a, (A a).card ≤ m) (hB : ∀ a b, (B a b).card ≤ k) :
    T.card ≤ Fintype.card V * (m * k) := by
  classical
  have hsub : T ⊆ Finset.univ.biUnion
      (fun a => (A a).biUnion (fun b => (B a b).image (fun c => (a, b, c)))) := by
    intro p hp
    obtain ⟨h1, h2⟩ := hT p hp
    refine Finset.mem_biUnion.2 ⟨p.1, Finset.mem_univ _, Finset.mem_biUnion.2 ⟨p.2.1, h1, ?_⟩⟩
    exact Finset.mem_image.2 ⟨p.2.2, h2, rfl⟩
  have hstep : ∀ a : V,
      ((A a).biUnion (fun b => (B a b).image (fun c => (a, b, c)))).card ≤ m * k := by
    intro a
    calc ((A a).biUnion (fun b => (B a b).image (fun c => (a, b, c)))).card
        ≤ ∑ b ∈ A a, ((B a b).image (fun c => (a, b, c))).card := Finset.card_biUnion_le
      _ ≤ ∑ _b ∈ A a, k :=
          Finset.sum_le_sum (fun b _ => (Finset.card_image_le).trans (hB a b))
      _ = (A a).card * k := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ m * k := Nat.mul_le_mul_right _ (hA a)
  calc T.card ≤ _ := Finset.card_le_card hsub
    _ ≤ ∑ a : V, ((A a).biUnion (fun b => (B a b).image (fun c => (a, b, c)))).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _a : V, (m * k) := Finset.sum_le_sum (fun a _ => hstep a)
    _ = Fintype.card V * (m * k) := by
        rw [Finset.sum_const, smul_eq_mul, Finset.card_univ]

/-- Triples of vertices spanning a triangle of reserved edges. -/
noncomputable def resTriangles [Fintype V] (R : Finset (Sym2 V)) : Finset (V × V × V) :=
  Finset.univ.filter (fun p => s(p.1, p.2.1) ∈ R ∧ s(p.2.1, p.2.2) ∈ R ∧ s(p.1, p.2.2) ∈ R)

/-- **A sparse reservoir has few triangles.** -/
theorem card_resTriangles_le [Fintype V] {R : Finset (Sym2 V)} {d : ℕ} (hd : ∀ v, edeg R v ≤ d) :
    (resTriangles R).card ≤ Fintype.card V * (d * d) := by
  classical
  refine card_triples_le (A := fun a => resNbr R a) (B := fun _ b => resNbr R b) ?_
    (fun a => (card_resNbr_le a).trans (hd a)) (fun _ b => (card_resNbr_le b).trans (hd b))
  intro p hp
  rw [resTriangles, Finset.mem_filter] at hp
  exact ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, hp.2.1⟩,
    Finset.mem_filter.2 ⟨Finset.mem_univ _, hp.2.2.1⟩⟩

/-- The triples linked by the reservoir. -/
noncomputable def linkedTriples [Fintype V] (𝒞 : Finset (Finset V)) : Finset (V × V × V) :=
  open Classical in
  Finset.univ.filter (fun p => CornerLinked 𝒞 p.1 p.2.1 p.2.2)

/-- **A sparse reservoir links few triples.**  Each linked triple comes from a triangle of reserved
edges together with, for each of its three edges, a vertex of the (unique) cluster of that edge. -/
theorem card_linkedTriples_le [Fintype V] (h𝒞 : ClusterFamilyIn E 𝒞) :
    (linkedTriples 𝒞).card ≤ 343 * (resTriangles (famEdges 𝒞)).card := by
  classical
  set R := famEdges 𝒞 with hR
  have hsub : linkedTriples 𝒞 ⊆ (resTriangles R).biUnion (fun p =>
      (clusterOf 𝒞 s(p.1, p.2.1)) ×ˢ ((clusterOf 𝒞 s(p.2.1, p.2.2)) ×ˢ
        (clusterOf 𝒞 s(p.1, p.2.2)))) := by
    intro p hp
    rw [linkedTriples, Finset.mem_filter] at hp
    obtain ⟨a, b, c, hab, hbc, hac, Cx, hCx, Cy, hCy, Cz, hCz,
      hx, ha1, hb1, hy, hb2, hc2, hz, hc3, ha3⟩ := hp.2
    have hedge : ∀ (u v : V), u ≠ v → ∀ C ∈ 𝒞, u ∈ C → v ∈ C → s(u, v) ∈ cliqueEdges C := by
      intro u v huv C _ hu hv
      refine mem_cliqueEdgesV.2 ⟨?_, ?_⟩
      · intro w hw
        rcases Sym2.mem_iff.1 hw with rfl | rfl
        exacts [hu, hv]
      · simpa [Sym2.isDiag_iff_proj_eq] using huv
    have e1 : s(a, b) ∈ cliqueEdges Cx := hedge a b hab Cx hCx ha1 hb1
    have e2 : s(b, c) ∈ cliqueEdges Cy := hedge b c hbc Cy hCy hb2 hc2
    have e3 : s(a, c) ∈ cliqueEdges Cz := by
      have := hedge c a hac.symm Cz hCz hc3 ha3
      rwa [Sym2.eq_swap] at this
    refine Finset.mem_biUnion.2 ⟨(a, b, c), ?_, ?_⟩
    · refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_, ?_, ?_⟩
      · exact Finset.mem_biUnion.2 ⟨Cx, hCx, e1⟩
      · exact Finset.mem_biUnion.2 ⟨Cy, hCy, e2⟩
      · exact Finset.mem_biUnion.2 ⟨Cz, hCz, e3⟩
    · refine Finset.mem_product.2 ⟨?_, Finset.mem_product.2 ⟨?_, ?_⟩⟩
      · rw [clusterOf_eq h𝒞 hCx e1]; exact hx
      · rw [clusterOf_eq h𝒞 hCy e2]; exact hy
      · rw [clusterOf_eq h𝒞 hCz e3]; exact hz
  have hcard : ∀ p : V × V × V,
      ((clusterOf 𝒞 s(p.1, p.2.1)) ×ˢ ((clusterOf 𝒞 s(p.2.1, p.2.2)) ×ˢ
        (clusterOf 𝒞 s(p.1, p.2.2)))).card ≤ 343 := by
    intro p
    have h7 : ∀ e : Sym2 V, (clusterOf 𝒞 e).card ≤ 7 := by
      intro e
      by_cases hex : ∃ C, C ∈ 𝒞 ∧ e ∈ cliqueEdges C
      · obtain ⟨C, hC, he⟩ := hex
        rw [clusterOf_eq h𝒞 hC he, h𝒞.1 C hC]
      · rw [clusterOf, dif_neg hex]
        simp
    rw [Finset.card_product, Finset.card_product]
    calc (clusterOf 𝒞 s(p.1, p.2.1)).card *
          ((clusterOf 𝒞 s(p.2.1, p.2.2)).card * (clusterOf 𝒞 s(p.1, p.2.2)).card)
        ≤ 7 * (7 * 7) :=
          Nat.mul_le_mul (h7 _) (Nat.mul_le_mul (h7 _) (h7 _))
      _ = 343 := by norm_num
  calc (linkedTriples 𝒞).card ≤ _ := Finset.card_le_card hsub
    _ ≤ ∑ _p ∈ resTriangles R, 343 := by
        refine (Finset.card_biUnion_le).trans (Finset.sum_le_sum ?_)
        intro p _
        exact hcard p
    _ = 343 * (resTriangles R).card := by
        rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]

/-- **Most triples are unlinked.**  In a cluster reservoir of maximum degree `d` on `n` vertices
with `1000 d ≤ n` and `4000 ≤ n`, some three vertices span a triangle of *unreserved* edges and are
not corner-linked.  (The counting: at most `3n²` degenerate triples, at most `3n²d` triples with a
reserved edge, and at most `343 n d²` linked ones — fewer than `n³` in total.) -/
theorem exists_unlinked_triangle [Fintype V] {E : Finset (Sym2 V)} {C7 : Finset (Finset V)}
    (hfam : ClusterFamilyIn E C7) {d : ℕ} (hd : ∀ v, edeg (famEdges C7) v ≤ d)
    (hdn : 1000 * d ≤ Fintype.card V) (hn : 4000 ≤ Fintype.card V) :
    ∃ x y z : V, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧ s(x, y) ∉ famEdges C7 ∧ s(y, z) ∉ famEdges C7 ∧
      s(x, z) ∉ famEdges C7 ∧ ¬ CornerLinked C7 x y z := by
  classical
  set n := Fintype.card V with hncard
  set R := famEdges C7 with hR
  set B1 : Finset (V × V × V) := Finset.univ.filter (fun p => p.1 = p.2.1) with hB1def
  set B2 : Finset (V × V × V) := Finset.univ.filter (fun p => p.2.1 = p.2.2) with hB2def
  set B3 : Finset (V × V × V) := Finset.univ.filter (fun p => p.1 = p.2.2) with hB3def
  set B4 : Finset (V × V × V) := Finset.univ.filter (fun p => s(p.1, p.2.1) ∈ R) with hB4def
  set B5 : Finset (V × V × V) := Finset.univ.filter (fun p => s(p.2.1, p.2.2) ∈ R) with hB5def
  set B6 : Finset (V × V × V) := Finset.univ.filter (fun p => s(p.1, p.2.2) ∈ R) with hB6def
  set B7 : Finset (V × V × V) := linkedTriples C7 with hB7def
  have hcB1 : B1.card ≤ n * (1 * n) := by
    refine card_triples_le (A := fun a => {a}) (B := fun _ _ => Finset.univ) ?_
      (fun a => by simp) (fun _ _ => by simp [Finset.card_univ, hncard])
    intro p hp
    rw [hB1def, Finset.mem_filter] at hp
    exact ⟨by simp [hp.2], Finset.mem_univ _⟩
  have hcB2 : B2.card ≤ n * (n * 1) := by
    refine card_triples_le (A := fun _ => Finset.univ) (B := fun _ b => {b}) ?_
      (fun a => by simp [Finset.card_univ, hncard]) (fun _ _ => by simp)
    intro p hp
    rw [hB2def, Finset.mem_filter] at hp
    exact ⟨Finset.mem_univ _, by simp [hp.2]⟩
  have hcB3 : B3.card ≤ n * (n * 1) := by
    refine card_triples_le (A := fun _ => Finset.univ) (B := fun a _ => {a}) ?_
      (fun a => by simp [Finset.card_univ, hncard]) (fun _ _ => by simp)
    intro p hp
    rw [hB3def, Finset.mem_filter] at hp
    exact ⟨Finset.mem_univ _, by simp [hp.2]⟩
  have hcB4 : B4.card ≤ n * (d * n) := by
    refine card_triples_le (A := fun a => resNbr R a) (B := fun _ _ => Finset.univ) ?_
      (fun a => (card_resNbr_le a).trans (hd a)) (fun _ _ => by simp [Finset.card_univ, hncard])
    intro p hp
    rw [hB4def, Finset.mem_filter] at hp
    exact ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, hp.2⟩, Finset.mem_univ _⟩
  have hcB5 : B5.card ≤ n * (n * d) := by
    refine card_triples_le (A := fun _ => Finset.univ) (B := fun _ b => resNbr R b) ?_
      (fun a => by simp [Finset.card_univ, hncard]) (fun _ b => (card_resNbr_le b).trans (hd b))
    intro p hp
    rw [hB5def, Finset.mem_filter] at hp
    exact ⟨Finset.mem_univ _, Finset.mem_filter.2 ⟨Finset.mem_univ _, hp.2⟩⟩
  have hcB6 : B6.card ≤ n * (n * d) := by
    refine card_triples_le (A := fun _ => Finset.univ) (B := fun a _ => resNbr R a) ?_
      (fun a => by simp [Finset.card_univ, hncard]) (fun a _ => (card_resNbr_le a).trans (hd a))
    intro p hp
    rw [hB6def, Finset.mem_filter] at hp
    exact ⟨Finset.mem_univ _, Finset.mem_filter.2 ⟨Finset.mem_univ _, hp.2⟩⟩
  have hcB7 : B7.card ≤ 343 * (n * (d * d)) :=
    (card_linkedTriples_le hfam).trans (Nat.mul_le_mul_left _ (card_resTriangles_le hd))
  set U : Finset (V × V × V) := B1 ∪ B2 ∪ B3 ∪ B4 ∪ B5 ∪ B6 ∪ B7 with hUdef
  have hUcard : U.card ≤ 3 * (n * n) + 3 * (n * (n * d)) + 343 * (n * (d * d)) := by
    have hsum : U.card ≤ B1.card + B2.card + B3.card + B4.card + B5.card + B6.card + B7.card := by
      rw [hUdef]
      refine le_trans (Finset.card_union_le _ _) (Nat.add_le_add_right ?_ _)
      refine le_trans (Finset.card_union_le _ _) (Nat.add_le_add_right ?_ _)
      refine le_trans (Finset.card_union_le _ _) (Nat.add_le_add_right ?_ _)
      refine le_trans (Finset.card_union_le _ _) (Nat.add_le_add_right ?_ _)
      refine le_trans (Finset.card_union_le _ _) (Nat.add_le_add_right ?_ _)
      exact Finset.card_union_le _ _
    refine hsum.trans ?_
    linarith only [hcB1, hcB2, hcB3, hcB4, hcB5, hcB6, hcB7]
  have hlt : U.card < (Finset.univ : Finset (V × V × V)).card := by
    have huniv : (Finset.univ : Finset (V × V × V)).card = n * (n * n) := by
      rw [Finset.card_univ, Fintype.card_prod, Fintype.card_prod, hncard]
    rw [huniv]
    refine lt_of_le_of_lt hUcard ?_
    have k1 : 1000000 * (3 * (n * n)) ≤ 750 * (n * (n * n)) := by nlinarith only [hn]
    have k2 : 1000000 * (3 * (n * (n * d))) ≤ 3000 * (n * (n * n)) := by nlinarith only [hdn]
    have k3 : 1000000 * (343 * (n * (d * d))) ≤ 343 * (n * (n * n)) := by nlinarith
    have key : 1000000 * (3 * (n * n) + 3 * (n * (n * d)) + 343 * (n * (d * d)))
        < 1000000 * (n * (n * n)) := by nlinarith
    exact lt_of_mul_lt_mul_left key (Nat.zero_le _)
  obtain ⟨p, hp⟩ : ∃ p : V × V × V, p ∉ U := by
    by_contra hcon
    push_neg at hcon
    exact absurd (Finset.card_le_card (fun p _ => hcon p)) (not_le.2 hlt)
  rw [hUdef] at hp
  simp only [Finset.mem_union, not_or] at hp
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := hp
  rw [hB1def] at h1; rw [hB2def] at h2; rw [hB3def] at h3
  rw [hB4def] at h4; rw [hB5def] at h5; rw [hB6def] at h6
  rw [hB7def, linkedTriples] at h7
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2 h3 h4 h5 h6 h7
  exact ⟨p.1, p.2.1, p.2.2, h1, h2, h3, h4, h5, h6, h7⟩

/-! ### The corner reservoir does not exist -/

/-- **`BKLO.CornerReservoirExistence` is false.**

Take the host to be a complete graph on `n` vertices and `γ = 1/1000`.  Whatever cluster reservoir
of maximum degree `γn` is reserved, `BKLO.exists_unlinked_triangle` produces three vertices
`x, y, z` spanning a triangle of unreserved host edges which the reservoir does not corner-link.
The triangle `H` on them is an admissible leftover — even, of maximum degree `2`, with `3 ∣ |H|` —
and a corner routing of it would corner-link its three vertices
(`BKLO.exists_cornerLinked_of_cornerRouting`).

So the corner mechanism, in the strict form in which every leftover edge is covered by an apex
triangle and the legs are paired inside corner clusters, cannot be supplied by any sparse
reservoir: pairing two legs at a vertex creates a patch edge, patch edges must group into
triangles, and a triangle of patch edges links three leftover vertices through three clusters — a
resource of which a reservoir of maximum degree `γ|S|` has only `O(γ²|S|³)`, against the `|S|³`
vertex triples that may carry the leftover. -/
theorem not_cornerReservoirExistence : ¬ CornerReservoirExistence := by
  classical
  intro hCR
  obtain ⟨n₀, hres⟩ := hCR (1 / 1000 : ℝ) (by norm_num) 3
  set n := max n₀ 4000 with hndef
  have hn4000 : 4000 ≤ n := le_max_right _ _
  have hnn₀ : n₀ ≤ n := le_max_left _ _
  have hcardfin : (Finset.univ : Finset (Fin n)).card = n := by simp
  -- the complete host
  have hdegE : ∀ v ∈ (Finset.univ : Finset (Fin n)),
      (9 / 10 + (1 / 1000 : ℝ)) * ((Finset.univ : Finset (Fin n)).card : ℝ) ≤
        (edeg (cliqueEdges (Finset.univ : Finset (Fin n))) v : ℝ) := by
    intro v _
    have hv : edeg (cliqueEdges (Finset.univ : Finset (Fin n))) v = n - 1 := by
      rw [edeg_cliqueEdges_card v, if_pos (Finset.mem_univ v), hcardfin]
    rw [hv, hcardfin]
    have h1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      have : (1 : ℕ) ≤ n := by omega
      push_cast [Nat.cast_sub this]
      ring
    rw [h1]
    have hn : (4000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn4000
    linarith
  obtain ⟨Cl, hfam, hdeg, hcorner⟩ :=
    hres (V := Fin n) (cliqueEdges (Finset.univ : Finset (Fin n))) Finset.univ
      (by rw [hcardfin]; exact hnn₀) (Finset.Subset.refl _) hdegE
  -- the reservoir is sparse
  set d := n / 1000 with hddef
  have hd : ∀ v : Fin n, edeg (famEdges Cl) v ≤ d := by
    intro v
    have h := hdeg v
    rw [hcardfin] at h
    have h' : (1000 : ℝ) * (edeg (famEdges Cl) v : ℝ) ≤ (n : ℝ) := by linarith
    have h'' : 1000 * edeg (famEdges Cl) v ≤ n := by exact_mod_cast h'
    rw [hddef, Nat.le_div_iff_mul_le (by norm_num : 0 < 1000)]
    omega
  have hcardV : Fintype.card (Fin n) = n := by simp
  obtain ⟨x, y, z, hxy, hyz, hxz, hRxy, hRyz, hRxz, hnotlinked⟩ :=
    exists_unlinked_triangle hfam hd (by rw [hcardV, hddef]; omega) (by rw [hcardV]; exact hn4000)
  -- the leftover: the triangle on `x, y, z`
  set T : Finset (Fin n) := {x, y, z} with hTdef
  have hT3 : T.card = 3 := Finset.card_eq_three.2 ⟨x, y, z, hxy, hxz, hyz, rfl⟩
  set H : Finset (Sym2 (Fin n)) := cliqueEdges T with hHdef
  have hHtriple : H = ({s(x, y), s(y, z), s(x, z)} : Finset (Sym2 (Fin n))) :=
    cliqueEdgesV_triple hxy hyz hxz
  have hHcard : H.card = 3 := cliqueEdges_card_three hT3
  have hHsub : H ⊆ cliqueEdges (Finset.univ : Finset (Fin n)) \ famEdges Cl := by
    intro e he
    rw [hHtriple] at he
    have hmem : ∀ (u v : Fin n), u ≠ v → s(u, v) ∈ cliqueEdges (Finset.univ : Finset (Fin n)) := by
      intro u v huv
      exact mem_cliqueEdgesV.2 ⟨fun w _ => Finset.mem_univ w, by
        simpa [Sym2.isDiag_iff_proj_eq] using huv⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl
    · exact Finset.mem_sdiff.2 ⟨hmem x y hxy, hRxy⟩
    · exact Finset.mem_sdiff.2 ⟨hmem y z hyz, hRyz⟩
    · exact Finset.mem_sdiff.2 ⟨hmem x z hxz, hRxz⟩
  have hHdeg : ∀ v : Fin n, edeg H v = if v ∈ T then 2 else 0 := fun v => edeg_cliqueEdges hT3 v
  obtain ⟨f, Tr, cl, hroute⟩ := hcorner H hHsub
    (fun v => by rw [hHdeg v]; split <;> decide)
    (fun v => by rw [hHdeg v]; split <;> norm_num)
    (by rw [hHcard])
  have hHne : H.Nonempty := Finset.card_pos.1 (by rw [hHcard]; norm_num)
  obtain ⟨x', y', z', hne1, hne2, hne3, ⟨e₁, he₁, hu₁⟩, ⟨e₂, he₂, hu₂⟩, ⟨e₃, he₃, hu₃⟩, hlink⟩ :=
    exists_cornerLinked_of_cornerRouting hfam hroute hHne
  have hin : ∀ (u : Fin n) (e : Sym2 (Fin n)), e ∈ H → u ∈ e → u = x ∨ u = y ∨ u = z := by
    intro u e he hue
    have := (mem_cliqueEdgesV.1 (hHdef ▸ he)).1 u hue
    simpa [hTdef] using this
  have hx' := hin x' e₁ he₁ hu₁
  have hy' := hin y' e₂ he₂ hu₂
  have hz' := hin z' e₃ he₃ hu₃
  refine hnotlinked ?_
  rcases hx' with rfl | rfl | rfl <;> rcases hy' with rfl | rfl | rfl <;>
      rcases hz' with rfl | rfl | rfl <;>
    first
      | exact absurd rfl hne1
      | exact absurd rfl hne2
      | exact absurd rfl hne3
      | exact hlink
      | exact hlink.swap
      | exact hlink.rotate
      | exact hlink.rotate.rotate
      | exact hlink.swap.rotate
      | exact hlink.swap.rotate.rotate

end BKLO
