/-
# Routing a bounded-degree leftover through **corner clusters**

`BKLO/CrossPatch.lean` reduces the absorption of the leftover by a `K₇`-cluster reservoir to the
existence of a *cross patch*, and shows that a routing forces the reservoir to satisfy the corner
condition `BKLO.CornerCovering`.  This file carries out the second half of the design recorded in
`BOUNDED_LEFTOVER_STATUS.md` §10: it turns explicit **corner data** into an actual absorption.

The data is exactly what the design prescribes:

* an apex covering of the leftover `H` (every leftover edge `e` gets an apex `f e`, its two legs
  being reserved);
* a **pairing** of the legs at every vertex: a family `Tr` of *transitions* `τ = (x, e, e')`, `e`
  and `e'` two distinct leftover edges at `x`, such that every incidence `(x, e)` occurs in a
  transition;
* for each transition a **corner cluster** `cl τ ∈ 𝒞` containing `x`, `f e` and `f e'`, distinct
  transitions getting distinct clusters;
* the resulting **patch edges** `s(f e, f e')` — one per transition, all of them joining apexes —
  forming a triangle-decomposable graph.

`BKLO.triDecomp_of_cornerRouting` then gives `TriDecomp (famEdges 𝒞 ∪ H)`: inside the corner cluster
of a transition the consumed edges are exactly the triangle `{x, f e, f e'}` — a pattern the cluster
gives back — every other cluster loses nothing, and the consumed edges together with `H` decompose
into the apex triangles and the patch triangles.  `BKLO.CornerReservoirExistence` packages this into
a statement — a sparse cluster reservoir providing corner data for every bounded-degree even
leftover — from which the target `BKLO.AbsorberDenseK3BoundedLeftover` follows
(`BKLO.absorberDenseK3BoundedLeftover_of_cornerReservoir`), via the intermediate
`BKLO.ClusterReservoirRouting`.

The point of the reduction is that no decomposition occurs in `CornerReservoirExistence` any more,
and no parity or divisibility reasoning either: what has to be produced is a choice of apexes, a pairing
of the legs at each vertex, corner clusters for the pairs, and a triangle structure on the patch
edges.  The counting is exactly right: the pairing has `|H|` transitions
(`BKLO.card_transitions_eq`), hence `|H|` patch edges, and `3 ∣ |H|` is precisely what makes them
groupable into patch triangles.

Everything in this file is `sorry`-free.
-/
import BKLO.ClusterCompletion
import BKLO.CrossPatch

open Finset

namespace BKLO

variable {V : Type*} [DecidableEq V]

/-! ### Transitions -/

/-- A **transition** `(x, e, e')`: a vertex together with two leftover edges at it whose legs are
to be consumed inside one corner cluster. -/
abbrev Transition (V : Type*) := V × Sym2 V × Sym2 V

/-- The **patch edge** of a transition: the edge joining the apexes of its two leftover edges. -/
def transPatch (f : Sym2 V → V) (τ : Transition V) : Sym2 V := s(f τ.2.1, f τ.2.2)

/-- The triangle a transition consumes inside its corner cluster: its vertex and the two apexes. -/
def transTri (f : Sym2 V → V) (τ : Transition V) : Finset V := {τ.1, f τ.2.1, f τ.2.2}

/-- All patch edges of a family of transitions. -/
def patchEdges (f : Sym2 V → V) (Tr : Finset (Transition V)) : Finset (Sym2 V) :=
  Tr.image (transPatch f)

/-- **Corner routing data** for the leftover `H` inside the cluster reservoir `𝒞`. -/
structure IsCornerRouting (𝒞 : Finset (Finset V)) (H : Finset (Sym2 V)) (f : Sym2 V → V)
    (Tr : Finset (Transition V)) (cl : Transition V → Finset V) : Prop where
  /-- the covering triangles are genuine and pairwise edge-disjoint -/
  apex : IsApexAssignment H f
  /-- the apexes are fresh: no apex is a vertex of a leftover edge -/
  fresh : ∀ e ∈ H, ∀ e' ∈ H, f e ∉ e'
  /-- all legs are reserved -/
  legs : apexEdges H f ⊆ famEdges 𝒞
  /-- a transition consists of two distinct leftover edges at its vertex -/
  trans_edge₁ : ∀ τ ∈ Tr, τ.2.1 ∈ H
  trans_edge₂ : ∀ τ ∈ Tr, τ.2.2 ∈ H
  trans_at₁ : ∀ τ ∈ Tr, τ.1 ∈ τ.2.1
  trans_at₂ : ∀ τ ∈ Tr, τ.1 ∈ τ.2.2
  trans_ne : ∀ τ ∈ Tr, τ.2.1 ≠ τ.2.2
  /-- every leg belongs to a transition: the legs at each vertex are paired up -/
  pairing : ∀ e ∈ H, ∀ x ∈ e, ∃ τ ∈ Tr, τ.1 = x ∧ (τ.2.1 = e ∨ τ.2.2 = e)
  /-- the corner cluster of a transition is a cluster ... -/
  cluster_mem : ∀ τ ∈ Tr, cl τ ∈ 𝒞
  /-- ... containing the transition's vertex and both apexes ... -/
  corner : ∀ τ ∈ Tr, transTri f τ ⊆ cl τ
  /-- ... and different transitions use different clusters -/
  cluster_inj : ∀ τ ∈ Tr, ∀ σ ∈ Tr, cl τ = cl σ → τ = σ
  /-- the patch edges group into reserved triangles -/
  patch : TriDecomp (patchEdges f Tr)

namespace IsCornerRouting

variable {𝒞 : Finset (Finset V)} {H : Finset (Sym2 V)} {f : Sym2 V → V}
  {Tr : Finset (Transition V)} {cl : Transition V → Finset V}

/-- A leg is a reserved edge of the apex covering. -/
theorem leg_mem_apexEdges (h : IsCornerRouting 𝒞 H f Tr cl) {e : Sym2 V} (he : e ∈ H) {x : V}
    (hx : x ∈ e) : s(x, f e) ∈ apexEdges H f := by
  refine Finset.mem_sdiff.2 ⟨?_, ?_⟩
  · refine Finset.mem_biUnion.2 ⟨apexTri e (f e), Finset.mem_image.2 ⟨e, he, rfl⟩, ?_⟩
    exact (mem_cliqueEdges_apexTri_iff (h.apex.nondiag e he) (h.apex.apex_notMem e he)).2
      (Or.inr ⟨x, hx, rfl⟩)
  · intro hmem
    exact h.fresh e he _ hmem (by simp)

/-- The two leftover edges of a transition have different apexes: otherwise their covering
triangles would share the leg at the transition's vertex. -/
theorem apex_ne (h : IsCornerRouting 𝒞 H f Tr cl) {τ : Transition V} (hτ : τ ∈ Tr) :
    f τ.2.1 ≠ f τ.2.2 := by
  intro hcon
  have h1 := h.trans_edge₁ τ hτ
  have h2 := h.trans_edge₂ τ hτ
  have hd := h.apex.edge_disjoint _ h1 _ h2 (h.trans_ne τ hτ)
  refine (Finset.disjoint_left.1 hd) (a := s(τ.1, f τ.2.1)) ?_ ?_
  · exact (mem_cliqueEdges_apexTri_iff (h.apex.nondiag _ h1) (h.apex.apex_notMem _ h1)).2
      (Or.inr ⟨τ.1, h.trans_at₁ τ hτ, rfl⟩)
  · rw [hcon]
    exact (mem_cliqueEdges_apexTri_iff (h.apex.nondiag _ h2) (h.apex.apex_notMem _ h2)).2
      (Or.inr ⟨τ.1, h.trans_at₂ τ hτ, rfl⟩)

/-- The vertex of a transition is neither of its two apexes. -/
theorem ne_apex₁ (h : IsCornerRouting 𝒞 H f Tr cl) {τ : Transition V} (hτ : τ ∈ Tr) :
    τ.1 ≠ f τ.2.1 := by
  intro hcon
  exact h.apex.apex_notMem _ (h.trans_edge₁ τ hτ) (hcon ▸ h.trans_at₁ τ hτ)

theorem ne_apex₂ (h : IsCornerRouting 𝒞 H f Tr cl) {τ : Transition V} (hτ : τ ∈ Tr) :
    τ.1 ≠ f τ.2.2 := by
  intro hcon
  exact h.apex.apex_notMem _ (h.trans_edge₂ τ hτ) (hcon ▸ h.trans_at₂ τ hτ)

/-- The consumed triangle of a transition is a genuine triangle. -/
theorem transTri_card (h : IsCornerRouting 𝒞 H f Tr cl) {τ : Transition V} (hτ : τ ∈ Tr) :
    (transTri f τ).card = 3 := by
  have h1 := h.ne_apex₁ hτ
  have h2 := h.ne_apex₂ hτ
  have h3 := h.apex_ne hτ
  rw [transTri, Finset.card_insert_of_notMem (by simp [h1, h2]),
    Finset.card_insert_of_notMem (by simp [h3])]
  simp

/-- The three edges of the consumed triangle of a transition. -/
theorem cliqueEdges_transTri (h : IsCornerRouting 𝒞 H f Tr cl) {τ : Transition V} (hτ : τ ∈ Tr) :
    cliqueEdges (transTri f τ)
      = {s(τ.1, f τ.2.1), s(f τ.2.1, f τ.2.2), s(τ.1, f τ.2.2)} :=
  cliqueEdgesV_triple (h.ne_apex₁ hτ) (h.apex_ne hτ) (h.ne_apex₂ hτ)

/-- The consumed edges: legs and patch edges. -/
theorem consumed_transTri (h : IsCornerRouting 𝒞 H f Tr cl) {τ : Transition V} (hτ : τ ∈ Tr) :
    cliqueEdges (transTri f τ) ⊆ apexEdges H f ∪ patchEdges f Tr := by
  rw [h.cliqueEdges_transTri hτ]
  intro g hg
  simp only [Finset.mem_insert, Finset.mem_singleton] at hg
  rcases hg with rfl | rfl | rfl
  · exact Finset.mem_union_left _
      (h.leg_mem_apexEdges (h.trans_edge₁ τ hτ) (h.trans_at₁ τ hτ))
  · exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨τ, hτ, rfl⟩)
  · exact Finset.mem_union_left _
      (h.leg_mem_apexEdges (h.trans_edge₂ τ hτ) (h.trans_at₂ τ hτ))

/-- Every leg lies in the consumed triangle of one of its transitions. -/
theorem leg_mem_transTri (h : IsCornerRouting 𝒞 H f Tr cl) {e : Sym2 V} (he : e ∈ H) {x : V}
    (hx : x ∈ e) : ∃ τ ∈ Tr, s(x, f e) ∈ cliqueEdges (transTri f τ) := by
  obtain ⟨τ, hτ, hx', hcase⟩ := h.pairing e he x hx
  refine ⟨τ, hτ, ?_⟩
  rw [h.cliqueEdges_transTri hτ]
  rcases hcase with hc | hc
  · simp [← hx', ← hc]
  · simp [← hx', ← hc]

/-- The patch edge of a transition lies in its consumed triangle. -/
theorem patch_mem_transTri (h : IsCornerRouting 𝒞 H f Tr cl) {τ : Transition V} (hτ : τ ∈ Tr) :
    transPatch f τ ∈ cliqueEdges (transTri f τ) := by
  rw [h.cliqueEdges_transTri hτ]
  simp [transPatch]

end IsCornerRouting

/-! ### The routing -/

variable {E : Finset (Sym2 V)} {𝒞 : Finset (Finset V)} {H : Finset (Sym2 V)} {f : Sym2 V → V}
  {Tr : Finset (Transition V)} {cl : Transition V → Finset V}

/-- The consumed set of a corner routing: the legs together with the patch edges. -/
def cornerConsumed (H : Finset (Sym2 V)) (f : Sym2 V → V) (Tr : Finset (Transition V)) :
    Finset (Sym2 V) :=
  apexEdges H f ∪ patchEdges f Tr

/-- The cluster of a consumed edge is the corner cluster of its transition. -/
theorem cluster_eq_of_consumed (h𝒞 : ClusterFamilyIn E 𝒞) (h : IsCornerRouting 𝒞 H f Tr cl)
    {C : Finset V} (hC : C ∈ 𝒞) {g : Sym2 V} (hg : g ∈ cornerConsumed H f Tr)
    (hgC : g ∈ cliqueEdges C) :
    ∃ τ ∈ Tr, cl τ = C ∧ g ∈ cliqueEdges (transTri f τ) := by
  have key : ∀ τ ∈ Tr, g ∈ cliqueEdges (transTri f τ) → cl τ = C := by
    intro τ hτ hgτ
    have : g ∈ cliqueEdges (cl τ) := cliqueEdges_mono (h.corner τ hτ) hgτ
    exact cluster_unique_of_mem h𝒞 (h.cluster_mem τ hτ) hC this hgC
  rcases Finset.mem_union.1 hg with hleg | hpatch
  · obtain ⟨e, he, u, hu, rfl⟩ := mem_apexEdges_iff_leg h.apex hleg
    obtain ⟨τ, hτ, hgτ⟩ := h.leg_mem_transTri he hu
    exact ⟨τ, hτ, key τ hτ hgτ, hgτ⟩
  · obtain ⟨τ, hτ, rfl⟩ := Finset.mem_image.1 hpatch
    exact ⟨τ, hτ, key τ hτ (h.patch_mem_transTri hτ), h.patch_mem_transTri hτ⟩

/-- **No patch edge is a leg.**  A patch edge joins two apexes, and no apex is a vertex of a
leftover edge, while every leg has such a vertex as an endpoint. -/
theorem patch_disjoint_legs (h : IsCornerRouting 𝒞 H f Tr cl) :
    Disjoint (patchEdges f Tr) (apexEdges H f) := by
  refine Finset.disjoint_left.2 ?_
  rintro g hg hleg
  obtain ⟨τ, hτ, rfl⟩ := Finset.mem_image.1 hg
  obtain ⟨e, he, u, hu, hguv⟩ := mem_apexEdges_iff_leg h.apex hleg
  rw [transPatch, Sym2.eq_iff] at hguv
  rcases hguv with ⟨h1', _⟩ | ⟨_, h2'⟩
  · exact h.fresh _ (h.trans_edge₁ τ hτ) _ he (h1' ▸ hu)
  · exact h.fresh _ (h.trans_edge₂ τ hτ) _ he (h2' ▸ hu)

/-- **The consumed edges are reserved.** -/
theorem cornerConsumed_subset (h : IsCornerRouting 𝒞 H f Tr cl) :
    cornerConsumed H f Tr ⊆ famEdges 𝒞 := by
  refine Finset.union_subset h.legs ?_
  intro g hg
  obtain ⟨τ, hτ, rfl⟩ := Finset.mem_image.1 hg
  exact Finset.mem_biUnion.2 ⟨cl τ, h.cluster_mem τ hτ,
    cliqueEdges_mono (h.corner τ hτ) (h.patch_mem_transTri hτ)⟩

/-- **Every cluster loses a pattern.**  A cluster used by a transition loses exactly the triangle
`{x, f e, f e'}`; every other cluster loses nothing. -/
theorem pattern_of_cornerRouting (h𝒞 : ClusterFamilyIn E 𝒞) (h : IsCornerRouting 𝒞 H f Tr cl) :
    ∀ C ∈ 𝒞, IsClusterPattern C (cornerConsumed H f Tr ∩ cliqueEdges C) := by
  classical
  set F : Finset V → Finset (Sym2 V) := fun C =>
    (Tr.filter (fun τ => cl τ = C)).biUnion (fun τ => cliqueEdges (transTri f τ)) with hFdef
  have hsingle : ∀ C ∈ 𝒞, ∀ τ ∈ Tr, cl τ = C → Tr.filter (fun σ => cl σ = C) = {τ} := by
    intro C _ τ hτ hclτ
    apply Finset.Subset.antisymm
    · intro σ hσ
      rw [Finset.mem_filter] at hσ
      exact Finset.mem_singleton.2 (h.cluster_inj σ hσ.1 τ hτ (by rw [hσ.2, hclτ]))
    · intro σ hσ
      rw [Finset.mem_singleton] at hσ
      subst hσ
      exact Finset.mem_filter.2 ⟨hτ, hclτ⟩
  refine pattern_of_local (F := F) ?_ ?_ ?_ ?_
  · -- each `F C` is a pattern
    intro C hC
    by_cases hne : ∃ τ ∈ Tr, cl τ = C
    · obtain ⟨τ, hτ, hclτ⟩ := hne
      right; left
      refine ⟨transTri f τ, ?_, h.transTri_card hτ, ?_⟩
      · rw [← hclτ]; exact h.corner τ hτ
      · rw [hFdef]
        simp [hsingle C hC τ hτ hclτ]
    · push_neg at hne
      left
      rw [hFdef]
      have : Tr.filter (fun τ => cl τ = C) = ∅ := by
        refine Finset.filter_eq_empty_iff.2 ?_
        intro τ hτ
        exact hne τ hτ
      simp [this]
  · -- `F C` lies inside `C`
    intro C hC g hg
    rw [hFdef] at hg
    obtain ⟨τ, hτ, hgτ⟩ := Finset.mem_biUnion.1 hg
    rw [Finset.mem_filter] at hτ
    rw [← hτ.2]
    exact cliqueEdges_mono (h.corner τ hτ.1) hgτ
  · -- `F C` is consumed
    intro C _ g hg
    rw [hFdef] at hg
    obtain ⟨τ, hτ, hgτ⟩ := Finset.mem_biUnion.1 hg
    rw [Finset.mem_filter] at hτ
    exact h.consumed_transTri hτ.1 hgτ
  · -- every consumed edge of `C` lies in `F C`
    intro C hC g hg hgC
    obtain ⟨τ, hτ, hclτ, hgτ⟩ := cluster_eq_of_consumed h𝒞 h hC hg hgC
    rw [hFdef]
    exact Finset.mem_biUnion.2 ⟨τ, Finset.mem_filter.2 ⟨hτ, hclτ⟩, hgτ⟩

/-- **Corner data absorbs the leftover.**  If the legs of an apex covering of `H` are paired up at
every vertex, each pair being routed through a corner cluster holding both apexes, and if the patch
edges — one per pair — form a triangle-decomposable graph, then the whole reservoir together with
the leftover is triangle-decomposable. -/
theorem triDecomp_of_cornerRouting (h𝒞 : ClusterFamilyIn E 𝒞) (hdisj : Disjoint (famEdges 𝒞) H)
    (h : IsCornerRouting 𝒞 H f Tr cl) : TriDecomp (famEdges 𝒞 ∪ H) := by
  classical
  have hdis := patch_disjoint_legs h
  have hsdiff : (apexEdges H f ∪ patchEdges f Tr) \ apexEdges H f = patchEdges f Tr := by
    ext g
    simp only [Finset.mem_sdiff, Finset.mem_union]
    constructor
    · rintro ⟨hg | hg, hg'⟩
      · exact absurd hg hg'
      · exact hg
    · intro hg
      exact ⟨Or.inr hg, fun hc => (Finset.disjoint_left.1 hdis) hg hc⟩
  refine triDecomp_of_trade h𝒞 hdisj h.apex Finset.subset_union_left
    (cornerConsumed_subset h) (pattern_of_cornerRouting h𝒞 h) ?_
  rw [hsdiff]
  exact h.patch

/-! ### The counting -/

/-- The **incidences** of the leftover: pairs `(x, e)` with `x` an endpoint of the leftover edge
`e`.  There are `2|H|` of them. -/
def incidences (H : Finset (Sym2 V)) : Finset (V × Sym2 V) :=
  H.biUnion (fun e => e.toFinset.image (fun x => (x, e)))

/-- The two incidences a transition pairs up. -/
def transInc (τ : Transition V) : Finset (V × Sym2 V) := {(τ.1, τ.2.1), (τ.1, τ.2.2)}

theorem card_incidences {H : Finset (Sym2 V)} (hnd : ∀ e ∈ H, ¬ e.IsDiag) :
    (incidences H).card = 2 * H.card := by
  classical
  have hdisj : ∀ e ∈ H, ∀ e' ∈ H, e ≠ e' →
      Disjoint (e.toFinset.image (fun x => (x, e))) (e'.toFinset.image (fun x => (x, e'))) := by
    intro e _ e' _ hne
    refine Finset.disjoint_left.2 ?_
    rintro ⟨x, g⟩ hg hg'
    obtain ⟨a, _, ha⟩ := Finset.mem_image.1 hg
    obtain ⟨b, _, hb⟩ := Finset.mem_image.1 hg'
    apply hne
    have h1 : e = g := congrArg Prod.snd ha
    have h2 : e' = g := congrArg Prod.snd hb
    rw [h1, h2]
  have hcard : ∀ e ∈ H, (e.toFinset.image (fun x => (x, e))).card = 2 := by
    intro e he
    rw [Finset.card_image_of_injective _ (fun a b hab => congrArg Prod.fst hab)]
    induction e using Sym2.ind with
    | _ x y =>
      have hxy : x ≠ y := by simpa [Sym2.isDiag_iff_proj_eq] using hnd _ he
      rw [Sym2.toFinset_mk_eq]
      simp [hxy]
  rw [incidences, Finset.card_biUnion hdisj, Finset.sum_congr rfl hcard, Finset.sum_const,
    smul_eq_mul, Nat.mul_comm]

/-- **The pairing has exactly `|H|` transitions**, hence there are exactly `|H|` patch edges to be
grouped into triangles — which is possible only because `3 ∣ |H|`.  (The hypotheses say that the
transitions partition the incidences of `H`: `BKLO.IsCornerRouting.pairing` gives the covering,
here we add that no incidence is used twice.) -/
theorem card_transitions_eq {H : Finset (Sym2 V)} {f : Sym2 V → V} {Tr : Finset (Transition V)}
    {cl : Transition V → Finset V} {𝒞 : Finset (Finset V)} (h : IsCornerRouting 𝒞 H f Tr cl)
    (hdisj : ∀ τ ∈ Tr, ∀ σ ∈ Tr, τ ≠ σ → Disjoint (transInc τ) (transInc σ))
    (hpart : Tr.biUnion transInc = incidences H) : Tr.card = H.card := by
  classical
  have hcard : ∀ τ ∈ Tr, (transInc τ).card = 2 := by
    intro τ hτ
    have hne : ((τ.1, τ.2.1) : V × Sym2 V) ≠ (τ.1, τ.2.2) := by
      simp [Prod.ext_iff, h.trans_ne τ hτ]
    rw [transInc, Finset.card_insert_of_notMem (by simpa using hne), Finset.card_singleton]
  have h1 : (Tr.biUnion transInc).card = 2 * Tr.card := by
    rw [Finset.card_biUnion hdisj, Finset.sum_congr rfl hcard, Finset.sum_const, smul_eq_mul,
      Nat.mul_comm]
  rw [hpart, card_incidences (fun e he => h.apex.nondiag e he)] at h1
  omega

/-- There are at most `|H|` patch edges. -/
theorem card_patchEdges_le {H : Finset (Sym2 V)} {f : Sym2 V → V} {Tr : Finset (Transition V)}
    {cl : Transition V → Finset V} {𝒞 : Finset (Finset V)} (h : IsCornerRouting 𝒞 H f Tr cl)
    (hdisj : ∀ τ ∈ Tr, ∀ σ ∈ Tr, τ ≠ σ → Disjoint (transInc τ) (transInc σ))
    (hpart : Tr.biUnion transInc = incidences H) : (patchEdges f Tr).card ≤ H.card := by
  rw [← card_transitions_eq h hdisj hpart]
  exact Finset.card_image_le

/-! ### The remaining gap, with the reservoir bundled in -/

/-- **A cluster reservoir that absorbs bounded-degree leftovers.**

For every `γ > 0` and every leftover degree bound `D`, every large dense host contains a sparse
edge-disjoint family of `K₇`s absorbing every even leftover of maximum degree at most `D` with
`3 ∣ |H|`.

This is `BKLO.ClusterUsageRouting` with the reservoir *bundled in* rather than universally
quantified.  The distinction matters: the analysis of `BKLO/CrossPatch.lean`
(`BKLO.corner_of_routing`) shows that a routing forces the reservoir to satisfy conditions —
corner covering, and more — which a merely pair-covering reservoir need not satisfy, so the
universally quantified form is the wrong statement to aim at. -/
def ClusterReservoirRouting : Prop :=
  ∀ γ : ℝ, 0 < γ → ∀ D : ℕ, ∃ n₀ : ℕ,
    ∀ {V : Type} [DecidableEq V] (E : Finset (Sym2 V)) (S : Finset V),
      n₀ ≤ S.card → E ⊆ cliqueEdges S →
      (∀ v ∈ S, (9 / 10 + γ) * (S.card : ℝ) ≤ (edeg E v : ℝ)) →
      ∃ 𝒞 : Finset (Finset V), ClusterFamilyIn E 𝒞 ∧
        (∀ v : V, (edeg (famEdges 𝒞) v : ℝ) ≤ γ * (S.card : ℝ)) ∧
        ∀ H : Finset (Sym2 V), H ⊆ E \ famEdges 𝒞 → EvenDegrees H → (∀ v : V, edeg H v ≤ D) →
          3 ∣ H.card → TriDecomp (famEdges 𝒞 ∪ H)

/-- **The absorbing cluster reservoir gives the packing reservoir**, hence the target.  The lines
of the clusters form the triangle packing, and the whole of it is consumed. -/
theorem packingReservoirExistence_of_clusterReservoirRouting (h : ClusterReservoirRouting) :
    PackingReservoirExistence := by
  classical
  intro γ hγ D
  obtain ⟨n₀, hres⟩ := h γ hγ D
  refine ⟨n₀, ?_⟩
  intro V _ E S hn hES _ hdeg
  obtain ⟨𝒞, h𝒞, h𝒞deg, habs⟩ := hres E S hn hES hdeg
  obtain ⟨ell, hsts, _⟩ := exists_sts_choice h𝒞.1
  have hfam : famEdges (clusterLines ell 𝒞) = famEdges 𝒞 := famEdges_clusterLines hsts
  refine ⟨clusterLines ell 𝒞, h𝒞.triFamilyIn_lines hsts, ?_, ?_⟩
  · intro v; rw [hfam]; exact h𝒞deg v
  · intro H hHsub hHeven hHdeg hHdvd
    rw [hfam] at hHsub
    refine ⟨clusterLines ell 𝒞, Finset.Subset.refl _, ?_⟩
    rw [hfam]
    exact habs H hHsub hHeven hHdeg hHdvd

/-- **The bounded-leftover absorber from an absorbing cluster reservoir.** -/
theorem absorberDenseK3BoundedLeftover_of_clusterReservoirRouting (h : ClusterReservoirRouting) :
    AbsorberDenseK3BoundedLeftover :=
  absorberDenseK3BoundedLeftover_of_packingReservoir
    (packingReservoirExistence_of_clusterReservoirRouting h)

/-- **The remaining gap, in corner form.**

For every `γ > 0` and every leftover degree bound `D`, every large dense host contains a sparse
edge-disjoint family of `K₇`s which provides *corner data* for every even leftover of maximum
degree at most `D` with `3 ∣ |H|`: apexes with reserved legs, a pairing of the legs at every
vertex, a corner cluster holding both apexes of each pair, and patch edges forming a
triangle-decomposable graph.

Compared with `BKLO.CrossPatchExistence` this asks for no pattern condition and for no
decomposition of the consumed set: the cluster patterns are *produced* by the corner clusters
(`BKLO.pattern_of_cornerRouting`), and the only decomposition left is that of the patch edges,
which live entirely among the apexes. -/
def CornerReservoirExistence : Prop :=
  ∀ γ : ℝ, 0 < γ → ∀ D : ℕ, ∃ n₀ : ℕ,
    ∀ {V : Type} [DecidableEq V] (E : Finset (Sym2 V)) (S : Finset V),
      n₀ ≤ S.card → E ⊆ cliqueEdges S →
      (∀ v ∈ S, (9 / 10 + γ) * (S.card : ℝ) ≤ (edeg E v : ℝ)) →
      ∃ 𝒞 : Finset (Finset V), ClusterFamilyIn E 𝒞 ∧
        (∀ v : V, (edeg (famEdges 𝒞) v : ℝ) ≤ γ * (S.card : ℝ)) ∧
        ∀ H : Finset (Sym2 V), H ⊆ E \ famEdges 𝒞 → EvenDegrees H → (∀ v : V, edeg H v ≤ D) →
          3 ∣ H.card →
          ∃ (f : Sym2 V → V) (Tr : Finset (Transition V)) (cl : Transition V → Finset V),
            IsCornerRouting 𝒞 H f Tr cl

/-- Corner data suffices: it absorbs the leftover. -/
theorem clusterReservoirRouting_of_cornerReservoir (h : CornerReservoirExistence) :
    ClusterReservoirRouting := by
  intro γ hγ D
  obtain ⟨n₀, hres⟩ := h γ hγ D
  refine ⟨n₀, ?_⟩
  intro V _ E S hn hES hdeg
  obtain ⟨𝒞, h𝒞, h𝒞deg, hcorner⟩ := hres E S hn hES hdeg
  refine ⟨𝒞, h𝒞, h𝒞deg, ?_⟩
  intro H hHsub hHeven hHdeg hHdvd
  obtain ⟨f, Tr, cl, hroute⟩ := hcorner H hHsub hHeven hHdeg hHdvd
  have hdisj : Disjoint (famEdges 𝒞) H :=
    Finset.disjoint_right.2 fun e he he' => (Finset.mem_sdiff.1 (hHsub he)).2 he'
  exact triDecomp_of_cornerRouting h𝒞 hdisj hroute

/-- **The bounded-leftover absorber from corner routings.** -/
theorem absorberDenseK3BoundedLeftover_of_cornerReservoir (h : CornerReservoirExistence) :
    AbsorberDenseK3BoundedLeftover :=
  absorberDenseK3BoundedLeftover_of_clusterReservoirRouting
    (clusterReservoirRouting_of_cornerReservoir h)

/-! ### Routing only part of the leftover

`BKLO.CornerReservoirExistence` asks for corner data for *the whole* leftover.  That is too much:
it is refuted in `BKLO/CornerLimit.lean` (`BKLO.not_cornerReservoirExistence`), already by a
leftover which is a single triangle — a triangle needs no reservoir at all, yet a corner routing of
it would force the reservoir to link its three vertices.  The statement below is the corrected
form: only a part `H'` of the leftover is routed, the rest being triangle-decomposable on its own,
exactly as in `BKLO.IsCrossPatch`. -/

/-- **Corner data for a part of the leftover suffices.**  If `H'` is routed through corner clusters
and the remaining leftover decomposes by itself, the whole reservoir together with the leftover is
triangle-decomposable. -/
theorem triDecomp_of_partial_cornerRouting (h𝒞 : ClusterFamilyIn E 𝒞)
    (hdisj : Disjoint (famEdges 𝒞) H) {H' : Finset (Sym2 V)} (hH' : H' ⊆ H)
    (h : IsCornerRouting 𝒞 H' f Tr cl) (hrest : TriDecomp (H \ H')) :
    TriDecomp (famEdges 𝒞 ∪ H) := by
  classical
  have hdisj' : Disjoint (famEdges 𝒞) H' :=
    Finset.disjoint_of_subset_right hH' hdisj
  have hmain : TriDecomp (famEdges 𝒞 ∪ H') := triDecomp_of_cornerRouting h𝒞 hdisj' h
  have hd : Disjoint (famEdges 𝒞 ∪ H') (H \ H') := by
    refine Finset.disjoint_left.2 ?_
    intro e he he'
    rcases Finset.mem_union.1 he with hR | hH'e
    · exact (Finset.disjoint_left.1 hdisj) hR (Finset.mem_sdiff.1 he').1
    · exact (Finset.mem_sdiff.1 he').2 hH'e
  have := hmain.union hd hrest
  have heq : (famEdges 𝒞 ∪ H') ∪ (H \ H') = famEdges 𝒞 ∪ H := by
    ext e
    simp only [Finset.mem_union, Finset.mem_sdiff]
    constructor
    · rintro ((hR | hH'e) | ⟨hHe, _⟩)
      exacts [Or.inl hR, Or.inr (hH' hH'e), Or.inr hHe]
    · rintro (hR | hHe)
      · exact Or.inl (Or.inl hR)
      · by_cases hc : e ∈ H'
        · exact Or.inl (Or.inr hc)
        · exact Or.inr ⟨hHe, hc⟩
  rwa [heq] at this

/-- **The corrected remaining gap.**  A sparse cluster reservoir which, for every even leftover of
bounded degree with `3 ∣ |H|`, provides corner data for *some part* `H'` of it, the rest of the
leftover being triangle-decomposable on its own.

Unlike `BKLO.CornerReservoirExistence` this is not refuted by a triangle-decomposable leftover
(take `H' = ∅`).  It is still open; `BKLO/CornerLimit.lean` shows what it demands of the reservoir:
for every nonempty routed part, three of its vertices must be corner-linked. -/
def PartialCornerReservoirExistence : Prop :=
  ∀ γ : ℝ, 0 < γ → ∀ D : ℕ, ∃ n₀ : ℕ,
    ∀ {V : Type} [DecidableEq V] (E : Finset (Sym2 V)) (S : Finset V),
      n₀ ≤ S.card → E ⊆ cliqueEdges S →
      (∀ v ∈ S, (9 / 10 + γ) * (S.card : ℝ) ≤ (edeg E v : ℝ)) →
      ∃ 𝒞 : Finset (Finset V), ClusterFamilyIn E 𝒞 ∧
        (∀ v : V, (edeg (famEdges 𝒞) v : ℝ) ≤ γ * (S.card : ℝ)) ∧
        ∀ H : Finset (Sym2 V), H ⊆ E \ famEdges 𝒞 → EvenDegrees H → (∀ v : V, edeg H v ≤ D) →
          3 ∣ H.card →
          ∃ (H' : Finset (Sym2 V)) (f : Sym2 V → V) (Tr : Finset (Transition V))
            (cl : Transition V → Finset V),
            H' ⊆ H ∧ TriDecomp (H \ H') ∧ IsCornerRouting 𝒞 H' f Tr cl

/-- Partial corner data suffices. -/
theorem clusterReservoirRouting_of_partialCornerReservoir
    (h : PartialCornerReservoirExistence) : ClusterReservoirRouting := by
  intro γ hγ D
  obtain ⟨n₀, hres⟩ := h γ hγ D
  refine ⟨n₀, ?_⟩
  intro V _ E S hn hES hdeg
  obtain ⟨𝒞, h𝒞, h𝒞deg, hcorner⟩ := hres E S hn hES hdeg
  refine ⟨𝒞, h𝒞, h𝒞deg, ?_⟩
  intro H hHsub hHeven hHdeg hHdvd
  obtain ⟨H', f, Tr, cl, hH', hrest, hroute⟩ := hcorner H hHsub hHeven hHdeg hHdvd
  have hdisj : Disjoint (famEdges 𝒞) H :=
    Finset.disjoint_right.2 fun e he he' => (Finset.mem_sdiff.1 (hHsub he)).2 he'
  exact triDecomp_of_partial_cornerRouting h𝒞 hdisj hH' hroute hrest

/-- **The bounded-leftover absorber from partial corner routings.** -/
theorem absorberDenseK3BoundedLeftover_of_partialCornerReservoir
    (h : PartialCornerReservoirExistence) : AbsorberDenseK3BoundedLeftover :=
  absorberDenseK3BoundedLeftover_of_clusterReservoirRouting
    (clusterReservoirRouting_of_partialCornerReservoir h)

end BKLO
