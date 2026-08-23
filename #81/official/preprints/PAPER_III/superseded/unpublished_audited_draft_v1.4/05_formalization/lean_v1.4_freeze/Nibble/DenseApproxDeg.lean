/-
# Nibble — degree-bounded near-perfect integral triangle packings for dense graphs

This file translates the hypergraph nibble output into pure `SimpleGraph` / `Finset (Sym2 V)`
language and assembles the *degree-bounded* approximate triangle decomposition of a dense graph.

* `Nibble.edgesOf` — the edge set of a vertex set, as unordered pairs; `Nibble.pack`,
  `Nibble.leftover` — the triangle family and the uncovered edge set attached to a matching of the
  edge-type triangle hypergraph `Nibble.YusterE.triangleHypergraphSub`.
* `Nibble.pack_triangles`, `Nibble.pack_pairwise_edge_disjoint` — the translated matching *is* an
  edge-disjoint family of `G`-triangles.
* `Nibble.card_leftover_filter_le`, `Nibble.card_leftover_le`, `Nibble.card_uncovered_add` — the
  uncovered graph edges (globally, and at each vertex) are counted by the uncovered hypergraph
  vertices.
* `Nibble.dense_approx_global` — **unconditional**: for every `β > 0` there are a density threshold
  `θ < 1` and an `n₀` such that every graph on at least `n₀` vertices with minimum degree at least
  `θ|V|` carries an edge-disjoint family of triangles whose uncovered edge set has at most `β|V|²`
  edges.  This is the library's tight-band nibble (`Nibble.nibbleTheoremMostCeil_holds`) fed with the
  near-complete near-regularity data (`Nibble.YusterE.triangleSub_linearSized_data_of_minDeg`) and
  then translated by the dictionary above.
* `Nibble.DenseTriangleNibbleDeg` — **the single residual**: at the Dross density threshold
  `9|V| ≤ 10 δ(G)` the edge-type triangle hypergraph admits a matching whose *uncovered set meets
  every star in at most `β|V|` vertices*.
* `Nibble.dense_approx_deg_bounded` — the target theorem, proved from that residual: a
  degree-bounded near-perfect integral triangle packing for graphs with `9|V| ≤ 10 δ(G)`.
* `Nibble.card_uncoveredAt_le`, `Nibble.dense_approx_deg_bounded_trivial` — the star of a vertex has
  at most `|V|` members, and consequently the target conclusion holds unconditionally (with the
  empty packing) for `β ≥ 1`: the residual only carries content for `β < 1`.

## Why the residual is needed

Two independent things are missing from the current library interfaces, and the residual isolates
exactly their conjunction.

1. *The band.*  `Nibble.YusterE.triangleSub_dense_data` shows that for `9|V| ≤ 10 δ(G)` the triangle
   hypergraph is nearly `|V|`-regular with band `μ = 1/5` (its vertex degrees are the codegrees
   `|N(u) ∩ N(v)| ∈ [2δ − |V|, |V|] = [(4/5)|V|, |V|]`, and that window is sharp at this density).
   The consumer `Nibble.NibbleTheoremMostCeil` instead fixes its own band `μ = μ(β) > 0`, which is
   small when `β` is; the near-regularity input it requires is therefore available only in the
   near-complete regime `δ(G) ≥ (1 − μ/2)|V|` — which is what `Nibble.dense_approx_global` below
   uses.  This is not a defect of the wiring: a `(1 ± 1/5)`-regular `3`-uniform hypergraph need not
   have a near-perfect matching at all.  At `δ(G) ≥ (9/10)|V|` the near-perfect *fractional*
   triangle decomposition is a genuinely deeper input (Dross' theorem).
2. *The stars.*  `Nibble.NibbleTheoremMostCeil` returns only the global size `|M| ≥ (1−β)|V_H|/3`;
   it says nothing about how the uncovered hypergraph vertices distribute over the stars of the
   graph vertices, which is exactly the per-vertex bound `edgeDeg L v ≤ ⌈β|V|⌉` asked for here.

Everything else — the whole hypergraph ↔ graph dictionary, the edge-disjointness of the translated
packing, the counting of the leftover globally and per vertex, and the unconditional dense global
statement — is proved here.

Sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.TightNibble
import Nibble.Tight.DenseRegDischarge
import Nibble.YusterBridgePacking

open Finset SimpleGraph Hypergraph Nibble.YusterE

namespace Nibble

/-! ### The edge set of a vertex set -/

/-- The edge set of a finite vertex set `t`, as unordered pairs. -/
def edgesOf {V : Type*} [DecidableEq V] (t : Finset V) : Finset (Sym2 V) :=
  t.offDiag.image Sym2.mk

theorem mem_edgesOf {V : Type*} [DecidableEq V] {t : Finset V} {e : Sym2 V} :
    e ∈ edgesOf t ↔ ¬ e.IsDiag ∧ ∀ x ∈ e, x ∈ t := by
  induction e with
  | _ a b =>
    simp only [edgesOf, Finset.mem_image, Finset.mem_offDiag, Prod.exists, Sym2.eq_iff,
      Sym2.isDiag_iff_proj_eq, Sym2.mem_iff]
    constructor
    · rintro ⟨x, y, ⟨hx, hy, hxy⟩, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩
      · exact ⟨hxy, by rintro z (rfl | rfl) <;> assumption⟩
      · exact ⟨fun h => hxy h.symm, by rintro z (rfl | rfl) <;> assumption⟩
    · rintro ⟨hne, hmem⟩
      exact ⟨a, b, ⟨hmem a (Or.inl rfl), hmem b (Or.inr rfl), hne⟩, Or.inl ⟨rfl, rfl⟩⟩

/-- `Sym2.toFinset` is injective. -/
theorem sym2_toFinset_injective {W : Type*} [DecidableEq W] :
    Function.Injective (Sym2.toFinset (α := W)) := by
  intro e f h
  refine Sym2.ext (fun x => ?_)
  rw [← Sym2.mem_toFinset, ← Sym2.mem_toFinset, h]

/-- Every unordered pair has a member. -/
theorem sym2_exists_mem {W : Type*} (e : Sym2 W) : ∃ x, x ∈ e := by
  induction e with
  | _ a b => exact ⟨a, Sym2.mem_mk_left a b⟩

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The endpoint set of an edge of `G` is a `2`-clique. -/
theorem toFinset_mem_cliqueFinset (G : SimpleGraph V) [DecidableRel G.Adj] {e : Sym2 V}
    (he : e ∈ G.edgeFinset) : e.toFinset ∈ G.cliqueFinset 2 := by
  rw [SimpleGraph.mem_cliqueFinset_iff]
  induction e with
  | _ a b =>
    have h : G.Adj a b := by simpa using he
    have hf : (s(a, b) : Sym2 V).toFinset = {a, b} := by ext x; simp [Sym2.mem_toFinset]
    rw [hf]
    refine ⟨?_, ?_⟩
    · simp only [Finset.coe_insert, Finset.coe_singleton]
      exact SimpleGraph.isClique_pair.mpr (fun _ => h)
    · rw [Finset.card_insert_of_notMem (by simp [h.ne]), Finset.card_singleton]

/-! ### The hypergraph ↔ graph dictionary -/

/-- The vertex set spanned by a hyperedge of the edge-type triangle hypergraph: the union of the
underlying graph edges. -/
def triOf (G : SimpleGraph V) [DecidableRel G.Adj] (T : Finset (EdgeV G)) : Finset V :=
  T.biUnion (fun E => E.val)

/-- Membership characterisation of the edge-type triangle hypergraph. -/
theorem mem_triangleHypergraphSub_iff (G : SimpleGraph V) [DecidableRel G.Adj]
    {T : Finset (EdgeV G)} :
    T ∈ triangleHypergraphSub G ↔
      ∃ t : Finset V, G.IsNClique 3 t ∧
        T = (t.powersetCard 2).subtype (· ∈ G.cliqueFinset 2) := by
  simp only [triangleHypergraphSub, Finset.mem_image, SimpleGraph.mem_cliqueFinset_iff]
  constructor
  · rintro ⟨t, ht, rfl⟩; exact ⟨t, ht, rfl⟩
  · rintro ⟨t, ht, rfl⟩; exact ⟨t, ht, rfl⟩

/-- The vertex set spanned by the hyperedge coming from the triangle `t` is `t` itself. -/
theorem triOf_subtype (G : SimpleGraph V) [DecidableRel G.Adj] {t : Finset V}
    (ht : G.IsNClique 3 t) :
    triOf G ((t.powersetCard 2).subtype (· ∈ G.cliqueFinset 2)) = t := by
  apply Finset.Subset.antisymm
  · refine Finset.biUnion_subset.mpr ?_
    intro E hE
    rw [Finset.mem_subtype, Finset.mem_powersetCard] at hE
    exact hE.1
  · intro x hx
    obtain ⟨y, hy, hyx⟩ : ∃ y ∈ t, y ≠ x := by
      have hne : (t.erase x).Nonempty := by
        rw [← Finset.card_pos, Finset.card_erase_of_mem hx, ht.card_eq]; omega
      obtain ⟨y, hy⟩ := hne
      exact ⟨y, Finset.mem_of_mem_erase hy, Finset.ne_of_mem_erase hy⟩
    have hsub : ({x, y} : Finset V) ⊆ t := by
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact hx
      · rw [Finset.mem_singleton] at hz; subst hz; exact hy
    have hcard : ({x, y} : Finset V).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simpa using fun h => hyx h.symm),
        Finset.card_singleton]
    have hclique : ({x, y} : Finset V) ∈ G.cliqueFinset 2 := by
      rw [SimpleGraph.mem_cliqueFinset_iff]
      exact ⟨ht.isClique.subset hsub, hcard⟩
    refine Finset.mem_biUnion.mpr ⟨⟨({x, y} : Finset V), hclique⟩, ?_, ?_⟩
    · rw [Finset.mem_subtype, Finset.mem_powersetCard]
      exact ⟨hsub, hcard⟩
    · exact Finset.mem_insert_self _ _

/-- The vertex set spanned by a hyperedge is a triangle. -/
theorem triOf_isNClique (G : SimpleGraph V) [DecidableRel G.Adj] {T : Finset (EdgeV G)}
    (hT : T ∈ triangleHypergraphSub G) : G.IsNClique 3 (triOf G T) := by
  obtain ⟨t, ht, rfl⟩ := (mem_triangleHypergraphSub_iff G).mp hT
  rw [triOf_subtype G ht]
  exact ht

/-- Every graph edge inside the vertex set spanned by a hyperedge belongs to that hyperedge. -/
theorem mem_of_subset_triOf (G : SimpleGraph V) [DecidableRel G.Adj] {T : Finset (EdgeV G)}
    (hT : T ∈ triangleHypergraphSub G) {s : Finset V} (hs : s ∈ G.cliqueFinset 2)
    (hsub : s ⊆ triOf G T) : (⟨s, hs⟩ : EdgeV G) ∈ T := by
  obtain ⟨t, ht, rfl⟩ := (mem_triangleHypergraphSub_iff G).mp hT
  rw [triOf_subtype G ht] at hsub
  rw [Finset.mem_subtype, Finset.mem_powersetCard]
  exact ⟨hsub, (SimpleGraph.mem_cliqueFinset_iff.mp hs).card_eq⟩

/-! ### The packing and the leftover attached to a matching -/

/-- The triangle family attached to a family of hyperedges. -/
def pack (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset (EdgeV G))) :
    Finset (Finset V) :=
  M.image (triOf G)

/-- The edges of `G` left uncovered by the triangle family `pack G M`. -/
def leftover (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset (EdgeV G))) :
    Finset (Sym2 V) :=
  G.edgeFinset \ ((pack G M).biUnion edgesOf)

/-- The hypergraph vertices (i.e. graph edges) left uncovered by `M`. -/
def uncovered (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset (EdgeV G))) :
    Finset (EdgeV G) :=
  Finset.univ.filter (fun E => ∀ T ∈ M, E ∉ T)

/-- The hypergraph vertices at the graph vertex `v` left uncovered by `M`. -/
def uncoveredAt (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset (EdgeV G))) (v : V) :
    Finset (EdgeV G) :=
  Finset.univ.filter (fun E => v ∈ E.val ∧ ∀ T ∈ M, E ∉ T)

/-- **The translated matching is a family of `G`-triangles.** -/
theorem pack_triangles (G : SimpleGraph V) [DecidableRel G.Adj] {M : Finset (Finset (EdgeV G))}
    (hM : IsMatching (triangleHypergraphSub G) M) : ∀ t ∈ pack G M, G.IsNClique 3 t := by
  intro t ht
  obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp ht
  exact triOf_isNClique G (hM.subset hT)

/-- **The translated matching is edge-disjoint.** -/
theorem pack_pairwise_edge_disjoint (G : SimpleGraph V) [DecidableRel G.Adj]
    {M : Finset (Finset (EdgeV G))} (hM : IsMatching (triangleHypergraphSub G) M) :
    (pack G M : Set (Finset V)).Pairwise (fun s t => Disjoint (edgesOf s) (edgesOf t)) := by
  intro t₁ ht₁ t₂ ht₂ hne
  obtain ⟨T₁, hT₁, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp ht₁)
  obtain ⟨T₂, hT₂, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp ht₂)
  rw [Finset.disjoint_left]
  intro e he1 he2
  rw [mem_edgesOf] at he1 he2
  have hcard : e.toFinset.card = 2 := by rw [Sym2.card_toFinset, if_neg he1.1]
  have hsub1 : e.toFinset ⊆ triOf G T₁ := fun x hx => he1.2 x (Sym2.mem_toFinset.mp hx)
  have hsub2 : e.toFinset ⊆ triOf G T₂ := fun x hx => he2.2 x (Sym2.mem_toFinset.mp hx)
  have hcl : e.toFinset ∈ G.cliqueFinset 2 := by
    rw [SimpleGraph.mem_cliqueFinset_iff]
    exact ⟨(triOf_isNClique G (hM.subset hT₁)).isClique.subset (Finset.coe_subset.mpr hsub1), hcard⟩
  have hE1 : (⟨e.toFinset, hcl⟩ : EdgeV G) ∈ T₁ := mem_of_subset_triOf G (hM.subset hT₁) hcl hsub1
  have hE2 : (⟨e.toFinset, hcl⟩ : EdgeV G) ∈ T₂ := mem_of_subset_triOf G (hM.subset hT₂) hcl hsub2
  have hTne : T₁ ≠ T₂ := fun h => hne (by rw [h])
  exact Finset.disjoint_left.mp (hM.disjoint T₁ hT₁ T₂ hT₂ hTne) hE1 hE2

/-- An uncovered graph edge gives an uncovered hypergraph vertex. -/
theorem toFinset_mem_uncovered (G : SimpleGraph V) [DecidableRel G.Adj]
    {M : Finset (Finset (EdgeV G))} {e : Sym2 V} (he : e ∈ leftover G M) :
    ∃ h : e.toFinset ∈ G.cliqueFinset 2, (⟨e.toFinset, h⟩ : EdgeV G) ∈ uncovered G M := by
  rw [leftover, Finset.mem_sdiff] at he
  obtain ⟨heE, hecov⟩ := he
  refine ⟨toFinset_mem_cliqueFinset G heE, ?_⟩
  rw [uncovered, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  intro T hT hmem
  refine hecov (Finset.mem_biUnion.mpr ⟨triOf G T, Finset.mem_image.mpr ⟨T, hT, rfl⟩, ?_⟩)
  rw [mem_edgesOf]
  refine ⟨SimpleGraph.not_isDiag_of_mem_edgeFinset heE, ?_⟩
  intro x hx
  exact Finset.subset_biUnion_of_mem (fun E : EdgeV G => E.val) hmem (Sym2.mem_toFinset.mpr hx)

/-- **Per-vertex leftover count.**  The uncovered graph edges at `v` are at most the uncovered
hypergraph vertices at `v`. -/
theorem card_leftover_filter_le (G : SimpleGraph V) [DecidableRel G.Adj]
    {M : Finset (Finset (EdgeV G))} (v : V) :
    ((leftover G M).filter (fun e => v ∈ e)).card ≤ (uncoveredAt G M v).card := by
  classical
  have hsub : ((leftover G M).filter (fun e => v ∈ e)).image Sym2.toFinset ⊆
      (uncoveredAt G M v).image Subtype.val := by
    intro s hs
    rw [Finset.mem_image] at hs
    obtain ⟨e, he, rfl⟩ := hs
    rw [Finset.mem_filter] at he
    obtain ⟨heL, hev⟩ := he
    obtain ⟨hcl, hunc⟩ := toFinset_mem_uncovered G heL
    refine Finset.mem_image.mpr ⟨⟨e.toFinset, hcl⟩, ?_, rfl⟩
    rw [uncovered, Finset.mem_filter] at hunc
    rw [uncoveredAt, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, Sym2.mem_toFinset.mpr hev, hunc.2⟩
  calc ((leftover G M).filter (fun e => v ∈ e)).card
      = (((leftover G M).filter (fun e => v ∈ e)).image Sym2.toFinset).card := by
        rw [Finset.card_image_of_injective _ sym2_toFinset_injective]
    _ ≤ ((uncoveredAt G M v).image Subtype.val).card := Finset.card_le_card hsub
    _ ≤ (uncoveredAt G M v).card := Finset.card_image_le

/-- **Global leftover count.**  The uncovered graph edges are at most the uncovered hypergraph
vertices. -/
theorem card_leftover_le (G : SimpleGraph V) [DecidableRel G.Adj]
    {M : Finset (Finset (EdgeV G))} :
    (leftover G M).card ≤ (uncovered G M).card := by
  classical
  have hsub : (leftover G M).image Sym2.toFinset ⊆ (uncovered G M).image Subtype.val := by
    intro s hs
    rw [Finset.mem_image] at hs
    obtain ⟨e, he, rfl⟩ := hs
    obtain ⟨hcl, hunc⟩ := toFinset_mem_uncovered G he
    exact Finset.mem_image.mpr ⟨⟨e.toFinset, hcl⟩, hunc, rfl⟩
  calc (leftover G M).card = ((leftover G M).image Sym2.toFinset).card := by
        rw [Finset.card_image_of_injective _ sym2_toFinset_injective]
    _ ≤ ((uncovered G M).image Subtype.val).card := Finset.card_le_card hsub
    _ ≤ (uncovered G M).card := Finset.card_image_le

/-- **The uncovered hypergraph vertices are all but `3|M|`.** -/
theorem card_uncovered_add (G : SimpleGraph V) [DecidableRel G.Adj]
    {M : Finset (Finset (EdgeV G))} (hM : IsMatching (triangleHypergraphSub G) M) :
    (uncovered G M).card + 3 * M.card = Fintype.card (EdgeV G) := by
  classical
  have huni : ∀ T ∈ M, T.card = 3 := fun T hT => triangleHypergraphSub_uniform G T (hM.subset hT)
  have hcov : (M.biUnion (fun T => T)).card = 3 * M.card := by
    rw [Finset.card_biUnion (fun T hT T' hT' hne => hM.disjoint T hT T' hT' hne),
      Finset.sum_congr rfl huni, Finset.sum_const, smul_eq_mul, mul_comm]
  have hset : uncovered G M = Finset.univ \ M.biUnion (fun T => T) := by
    ext E
    simp [uncovered, Finset.mem_sdiff, Finset.mem_biUnion]
  have hle : 3 * M.card ≤ Fintype.card (EdgeV G) := by
    rw [← hcov, ← Finset.card_univ]
    exact Finset.card_le_card (Finset.subset_univ _)
  rw [hset, Finset.card_sdiff, Finset.inter_univ, hcov, Finset.card_univ]
  omega

/-- **The star of a vertex is small.**  At most `|V|` hypergraph vertices (i.e. graph edges) contain
a given graph vertex `v`; so the residual bound below is only a constraint for `β < 1`. -/
theorem card_uncoveredAt_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset (EdgeV G))) (v : V) :
    (uncoveredAt G M v).card ≤ Fintype.card V := by
  classical
  have hmem : ∀ E ∈ uncoveredAt G M v, E.val.erase v ∈
      Finset.univ.image (fun x : V => ({x} : Finset V)) := by
    intro E hE
    rw [uncoveredAt, Finset.mem_filter] at hE
    have hcard2 : E.val.card = 2 :=
      (SimpleGraph.mem_cliqueFinset_iff.mp E.property).card_eq
    have hcard1 : (E.val.erase v).card = 1 := by
      rw [Finset.card_erase_of_mem hE.2.1, hcard2]
    obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hcard1
    exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, hx.symm⟩
  have hinj : ∀ E ∈ uncoveredAt G M v, ∀ E' ∈ uncoveredAt G M v,
      E.val.erase v = E'.val.erase v → E = E' := by
    intro E hE E' hE' heq
    rw [uncoveredAt, Finset.mem_filter] at hE hE'
    refine Subtype.ext ?_
    rw [← Finset.insert_erase hE.2.1, ← Finset.insert_erase hE'.2.1, heq]
  calc (uncoveredAt G M v).card
      ≤ (Finset.univ.image (fun x : V => ({x} : Finset V))).card :=
        Finset.card_le_card_of_injOn _ hmem hinj
    _ ≤ (Finset.univ : Finset V).card := Finset.card_image_le
    _ = Fintype.card V := Finset.card_univ

/-! ### The unconditional dense global statement -/

/-- **A near-perfect edge-disjoint triangle packing for near-complete graphs, unconditionally.**
For every `β > 0` there are a density threshold `θ < 1` and a size threshold `n₀` such that every
graph on at least `n₀` vertices with minimum degree at least `θ|V|` has an edge-disjoint family of
triangles whose uncovered edge set has at most `β|V|²` edges.

This is the library's tight-band nibble `Nibble.nibbleTheoremMostCeil_holds` applied to the
edge-type triangle hypergraph, translated to graph language by the dictionary above.  The threshold
`θ = 1 − μ/2` is the one at which the nibble's own band `μ` is available; it is *not* the Dross
threshold `9/10` of `Nibble.dense_approx_deg_bounded`. -/
theorem dense_approx_global (β : ℝ) (hβ : 0 < β) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧ ∃ n₀ : ℕ,
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        n₀ ≤ Fintype.card V → (∀ x : V, θ * (Fintype.card V : ℝ) ≤ (G.degree x : ℝ)) →
        ∃ (P : Finset (Finset V)) (L : Finset (Sym2 V)),
          (∀ t ∈ P, G.IsNClique 3 t) ∧
          (P : Set (Finset V)).Pairwise (fun s t => Disjoint (edgesOf s) (edgesOf t)) ∧
          L = G.edgeFinset \ (P.biUnion edgesOf) ∧
          (L.card : ℝ) ≤ β * (Fintype.card V : ℝ) ^ 2 := by
  classical
  obtain ⟨μ, hμ, η, hη, d₀, hd₀, hmain⟩ := nibbleTheoremMostCeil_holds 3 (by norm_num) β hβ
  have hmpos : 0 < min μ 1 := lt_min hμ one_pos
  have hm1 : min μ 1 ≤ 1 := min_le_right _ _
  have hmμ : min μ 1 ≤ μ := min_le_left _ _
  refine ⟨1 - min μ 1 / 2, by linarith, by linarith, ⌈max d₀ (max (1 / μ) 1)⌉₊, ?_⟩
  intro V _ _ G _ hV hdeg
  have hnR : max d₀ (max (1 / μ) 1) ≤ (Fintype.card V : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast hV)
  have hd0 : d₀ ≤ (Fintype.card V : ℝ) := le_trans (le_max_left _ _) hnR
  have hinv : 1 / μ ≤ (Fintype.card V : ℝ) :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hnR
  have hn1 : (1 : ℝ) ≤ (Fintype.card V : ℝ) :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hnR
  have hnpos : (0 : ℝ) < (Fintype.card V : ℝ) := lt_of_lt_of_le one_pos hn1
  set D : ℕ := ⌈(1 - min μ 1 / 2) * (Fintype.card V : ℝ)⌉₊ with hDdef
  have hD : ∀ x, D ≤ G.degree x := fun x => Nat.ceil_le.mpr (hdeg x)
  have hDR : (1 - min μ 1 / 2) * (Fintype.card V : ℝ) ≤ (D : ℝ) := Nat.le_ceil _
  have h2DR : (Fintype.card V : ℝ) ≤ 2 * (D : ℝ) := by nlinarith
  have h2D : Fintype.card V ≤ 2 * D := by exact_mod_cast h2DR
  have hcodeg : (1 : ℝ) ≤ μ * (Fintype.card V : ℝ) := by
    rw [div_le_iff₀ hμ] at hinv
    linarith
  obtain ⟨hreg, hcod, hceil, -⟩ :=
    triangleSub_linearSized_data_of_minDeg (μ := μ) (η := η) (d := (Fintype.card V : ℝ)) (L := 1)
      G D hD h2D hη.le hcodeg (by rw [one_mul]) (by nlinarith) (by nlinarith)
  obtain ⟨M, hM, hMcard⟩ :=
    hmain (triangleHypergraphSub G) (Fintype.card V : ℝ) hnpos hd0
      (triangleHypergraphSub_uniform G) hreg hcod hceil
  refine ⟨pack G M, leftover G M, pack_triangles G hM, pack_pairwise_edge_disjoint G hM, rfl, ?_⟩
  -- counting: the leftover is at most `|E| − 3|M| ≤ β|E| ≤ β|V|²`
  have hcount := card_uncovered_add G hM
  have hEcard : (Fintype.card (EdgeV G) : ℝ) = ((G.cliqueFinset 2).card : ℝ) := by
    exact_mod_cast card_EdgeV G
  have hle : ((leftover G M).card : ℝ) ≤ ((uncovered G M).card : ℝ) := by
    exact_mod_cast card_leftover_le G (M := M)
  have hsum : ((uncovered G M).card : ℝ) + 3 * (M.card : ℝ) = (Fintype.card (EdgeV G) : ℝ) := by
    exact_mod_cast hcount
  have hEsq : ((G.cliqueFinset 2).card : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 := edge_card_le_card_sq G
  rw [hEcard] at hsum hMcard
  have hβE : β * ((G.cliqueFinset 2).card : ℝ) ≤ β * (Fintype.card V : ℝ) ^ 2 :=
    mul_le_mul_of_nonneg_left hEsq hβ.le
  nlinarith only [hle, hsum, hMcard, hβE]

/-! ### The residual and the target theorem -/

/-- **The residual.**  At the Dross density threshold `9|V| ≤ 10 δ(G)` the edge-type triangle
hypergraph of `G` has a matching whose uncovered set meets the star of every graph vertex in at
most `β|V|` hypergraph vertices.

This is the known approximate triangle decomposition of dense graphs, in the form with a
degree-bounded leftover; it needs two inputs beyond the present library, see the file header: a
near-perfect *fractional* triangle decomposition at `δ(G) ≥ (9/10)|V|` (the current dense
near-regularity data only gives band `1/5`, which no nibble can consume), and per-star control of
the nibble's leftover, which `Nibble.NibbleTheoremMostCeil` does not expose. -/
def DenseTriangleNibbleDeg : Prop :=
  ∀ β : ℝ, 0 < β → ∃ n₀ : ℕ,
    ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      n₀ ≤ Fintype.card V → 9 * Fintype.card V ≤ 10 * G.minDegree →
      ∃ M : Finset (Finset (EdgeV G)), IsMatching (triangleHypergraphSub G) M ∧
        ∀ v : V, ((uncoveredAt G M v).card : ℝ) ≤ β * (Fintype.card V : ℝ)

/-- **A degree-bounded near-perfect integral triangle packing for dense graphs.**  For every
`β > 0` there is an `n₀` such that every graph `G` on at least `n₀` vertices with
`9|V| ≤ 10 δ(G)` has an edge-disjoint family `P` of triangles whose uncovered edge set
`L = E(G) ∖ ⋃_{t ∈ P} E(t)` satisfies both `|L| ≤ β|V|²` and `deg_L(v) ≤ ⌈β|V|⌉` for every vertex
`v`.

Proved from the single residual `Nibble.DenseTriangleNibbleDeg`; everything else — the translation
of the hypergraph matching into an edge-disjoint triangle family, the identification of the
uncovered edge set, the per-vertex bound and the global bound derived from it — is proved here. -/
theorem dense_approx_deg_bounded (hres : DenseTriangleNibbleDeg) (β : ℝ) (hβ : 0 < β) :
    ∃ n₀ : ℕ, ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      n₀ ≤ Fintype.card V → 9 * Fintype.card V ≤ 10 * G.minDegree →
      ∃ (P : Finset (Finset V)) (L : Finset (Sym2 V)),
        (∀ t ∈ P, G.IsNClique 3 t) ∧
        (P : Set (Finset V)).Pairwise (fun s t => Disjoint (edgesOf s) (edgesOf t)) ∧
        L = G.edgeFinset \ (P.biUnion edgesOf) ∧
        (L.card : ℝ) ≤ β * (Fintype.card V : ℝ) ^ 2 ∧
        (∀ v : V, (L.filter (fun e => v ∈ e)).card ≤ ⌈β * (Fintype.card V : ℝ)⌉₊) := by
  classical
  obtain ⟨n₀, hmain⟩ := hres β hβ
  refine ⟨n₀, ?_⟩
  intro V _ _ G _ hV hdense
  obtain ⟨M, hM, hdeg⟩ := hmain G hV hdense
  -- the per-vertex leftover bound, transported from the hypergraph side
  have hkey : ∀ v : V,
      (((leftover G M).filter (fun e => v ∈ e)).card : ℝ) ≤ β * (Fintype.card V : ℝ) := by
    intro v
    refine le_trans ?_ (hdeg v)
    exact_mod_cast card_leftover_filter_le G (M := M) v
  refine ⟨pack G M, leftover G M, pack_triangles G hM, pack_pairwise_edge_disjoint G hM, rfl,
    ?_, ?_⟩
  · -- the global bound follows from the per-vertex bound
    have hcover : leftover G M ⊆
        Finset.univ.biUnion (fun v : V => (leftover G M).filter (fun e => v ∈ e)) := by
      intro e he
      obtain ⟨v, hv⟩ := sym2_exists_mem e
      exact Finset.mem_biUnion.mpr ⟨v, Finset.mem_univ _, Finset.mem_filter.mpr ⟨he, hv⟩⟩
    have hcard : (leftover G M).card ≤
        ∑ v : V, ((leftover G M).filter (fun e => v ∈ e)).card :=
      le_trans (Finset.card_le_card hcover) Finset.card_biUnion_le
    calc ((leftover G M).card : ℝ)
        ≤ ∑ v : V, (((leftover G M).filter (fun e => v ∈ e)).card : ℝ) := by exact_mod_cast hcard
      _ ≤ ∑ _v : V, β * (Fintype.card V : ℝ) := Finset.sum_le_sum (fun v _ => hkey v)
      _ = β * (Fintype.card V : ℝ) ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
  · -- the per-vertex bound, rounded up
    intro v
    have h1 := hkey v
    have h2 : β * (Fintype.card V : ℝ) ≤ (⌈β * (Fintype.card V : ℝ)⌉₊ : ℝ) := Nat.le_ceil _
    exact_mod_cast le_trans h1 h2

/-- **The trivial range.**  For `β ≥ 1` the conclusion of `Nibble.dense_approx_deg_bounded` holds
unconditionally with the empty packing, so the residual is only about `β < 1`. -/
theorem dense_approx_deg_bounded_trivial {β : ℝ} (hβ : 1 ≤ β) (G : SimpleGraph V)
    [DecidableRel G.Adj] :
    ∃ (P : Finset (Finset V)) (L : Finset (Sym2 V)),
      (∀ t ∈ P, G.IsNClique 3 t) ∧
      (P : Set (Finset V)).Pairwise (fun s t => Disjoint (edgesOf s) (edgesOf t)) ∧
      L = G.edgeFinset \ (P.biUnion edgesOf) ∧
      (L.card : ℝ) ≤ β * (Fintype.card V : ℝ) ^ 2 ∧
      (∀ v : V, (L.filter (fun e => v ∈ e)).card ≤ ⌈β * (Fintype.card V : ℝ)⌉₊) := by
  classical
  have hM : IsMatching (triangleHypergraphSub G) (∅ : Finset (Finset (EdgeV G))) :=
    ⟨Finset.empty_subset _, fun e he => absurd he (Finset.notMem_empty e)⟩
  have hn : (0 : ℝ) ≤ (Fintype.card V : ℝ) := Nat.cast_nonneg _
  refine ⟨pack G ∅, leftover G ∅, pack_triangles G hM, pack_pairwise_edge_disjoint G hM, rfl,
    ?_, ?_⟩
  · have h1 : ((leftover G ∅).card : ℝ) ≤ ((uncovered G ∅).card : ℝ) := by
      exact_mod_cast card_leftover_le G (M := (∅ : Finset (Finset (EdgeV G))))
    have h2 : ((uncovered G ∅).card : ℝ) = ((G.cliqueFinset 2).card : ℝ) := by
      have := card_uncovered_add G hM
      simp only [Finset.card_empty, Nat.mul_zero, Nat.add_zero] at this
      rw [this]
      exact_mod_cast card_EdgeV G
    have h3 : ((G.cliqueFinset 2).card : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 := edge_card_le_card_sq G
    nlinarith [sq_nonneg (Fintype.card V : ℝ)]
  · intro v
    have h1 : ((leftover G ∅).filter (fun e => v ∈ e)).card ≤ Fintype.card V :=
      le_trans (card_leftover_filter_le G (M := (∅ : Finset (Finset (EdgeV G)))) v)
        (card_uncoveredAt_le G ∅ v)
    have h2 : (Fintype.card V : ℝ) ≤ (⌈β * (Fintype.card V : ℝ)⌉₊ : ℝ) := by
      refine le_trans ?_ (Nat.le_ceil _)
      nlinarith only [hβ]
    have h3 : Fintype.card V ≤ ⌈β * (Fintype.card V : ℝ)⌉₊ := by exact_mod_cast h2
    exact le_trans h1 h3

end Nibble
