/-
# Covering a bounded-degree leftover by reserved apex triangles.

This file develops the *distributed absorber* mechanism for the cover-down interface
`BKLO.BoundedLeftoverCoverDown` (see `BKLO/BoundedLeftover.lean`).

The idea: given a leftover `H` (even, of bounded maximum degree `D`) we cover every edge
`e = xy ∈ H` by a triangle `xyz`, where the **apex** `z` is a vertex joined to both `x` and `y`
by *reserved* edges.  If the triangles chosen for different edges of `H` are pairwise
edge-disjoint, then `H` together with the used reserved edges (`apexCover H f`) is
triangle-decomposable, and what remains of the reservoir is `R \ (apexCover H f \ H)`.

Contents (all `sorry`-free):

* `apexTri`, `apexFam`, `apexCover`, `apexEdges` — the triangles, their family and their edges;
* `IsApexAssignment` — the property that the chosen triangles are genuine and pairwise
  edge-disjoint, and `triDecomp_apexCover` — the resulting triangle decomposition;
* `triDecomp_union_of_apexAssignment`, `triDecomp_sdiff_of_apexAssignment` — the reduction of
  `TriDecomp (R ∪ H)` (respectively of the cover-down conclusion) to the decomposability of the
  **unused** part of the reservoir;
* `isApexAssignment_of_fresh` — pairwise edge-disjointness from two simple conditions: the apexes
  are *fresh* (not incident to `H`) and *conflict-free* (edges of `H` sharing a vertex receive
  different apexes);
* `exists_apex_fun` — **the greedy/list-colouring existence theorem**: if every edge of `H` has
  more than `2D` candidate apexes then a conflict-free choice exists.  (`Δ(H) ≤ D` bounds the
  load: an edge conflicts with at most `2D` others.)
* `exists_injective_apex_fun` — **the Hall variant**, from Mathlib's
  `Finset.all_card_le_biUnion_card_iff_exists_injective`: under Hall's condition on the bipartite
  "edges of `H` versus candidate apexes" graph, all apexes can be chosen *distinct*.
* `card_common_nbhd_dense` — **the load bound coming from the density hypothesis**: in a host of
  minimum degree `(9/10 + γ)|S|` every pair of vertices has at least `(4/5 + 2γ)|S| − |W|`
  common neighbours outside any excluded set `W`.

What is *not* provided here — and is the precise remaining gap — is a reservoir `R` of maximum
degree `≤ γ|S|/2` in which *every* pair of vertices already has `2D + 1` common neighbours
(`ApexReservoir` below), together with the decomposability of the unused part; see
`BOUNDED_LEFTOVER_STATUS.md`.
-/
import BKLO.BoundedLeftover
import Mathlib.Combinatorics.Hall.Basic

open Finset

namespace BKLO

variable {V : Type*} [DecidableEq V]

/-! ### Triangles on an edge and an apex -/

/-- The triangle spanned by the edge `e` and the apex `z`. -/
def apexTri (e : Sym2 V) (z : V) : Finset V := insert z e.toFinset

/-- The triangle family covering `H` given by the apex function `f`. -/
def apexFam (H : Finset (Sym2 V)) (f : Sym2 V → V) : Finset (Finset V) :=
  H.image (fun e => apexTri e (f e))

/-- All edges used by the covering triangles: the edges of `H` together with the reserved apex
edges. -/
def apexCover (H : Finset (Sym2 V)) (f : Sym2 V → V) : Finset (Sym2 V) := famEdges (apexFam H f)

/-- The reserved edges used by the covering triangles. -/
def apexEdges (H : Finset (Sym2 V)) (f : Sym2 V → V) : Finset (Sym2 V) := apexCover H f \ H

theorem cliqueEdgesV_triple {a b c : V} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    cliqueEdges ({a, b, c} : Finset V) = ({s(a, b), s(b, c), s(a, c)} : Finset (Sym2 V)) := by
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

theorem apexTri_eq {x y : V} {z : V} : apexTri s(x, y) z = ({z, x, y} : Finset V) := by
  ext w; simp [apexTri, Sym2.mem_iff]

theorem cliqueEdges_apexTri {x y z : V} (hxy : x ≠ y) (hzx : z ≠ x) (hzy : z ≠ y) :
    cliqueEdges (apexTri s(x, y) z) = ({s(z, x), s(x, y), s(z, y)} : Finset (Sym2 V)) := by
  rw [apexTri_eq, cliqueEdgesV_triple hzx hxy hzy]

theorem card_apexTri {e : Sym2 V} {z : V} (hnd : ¬ e.IsDiag) (hz : z ∉ e) :
    (apexTri e z).card = 3 := by
  induction e using Sym2.ind with
  | _ x y =>
    have hxy : x ≠ y := by simpa [Sym2.isDiag_iff_proj_eq] using hnd
    have hzx : z ≠ x := by rintro rfl; exact hz (by simp)
    have hzy : z ≠ y := by rintro rfl; exact hz (by simp)
    rw [apexTri_eq, Finset.card_insert_of_notMem (by simp [hzx, hzy]),
      Finset.card_insert_of_notMem (by simp [hxy])]
    simp

theorem mem_cliqueEdges_apexTri {e : Sym2 V} {z : V} (hnd : ¬ e.IsDiag) :
    e ∈ cliqueEdges (apexTri e z) := by
  rw [mem_cliqueEdgesV]
  exact ⟨fun w hw => by simp [apexTri, hw], hnd⟩

theorem mem_cliqueEdges_apexTri_iff {e : Sym2 V} {z : V} (hnd : ¬ e.IsDiag) (hz : z ∉ e)
    {g : Sym2 V} : g ∈ cliqueEdges (apexTri e z) ↔ (g = e ∨ ∃ u ∈ e, g = s(u, z)) := by
  induction e using Sym2.ind with
  | _ x y =>
    have hxy : x ≠ y := by simpa [Sym2.isDiag_iff_proj_eq] using hnd
    have hzx : z ≠ x := by rintro rfl; exact hz (by simp)
    have hzy : z ≠ y := by rintro rfl; exact hz (by simp)
    rw [cliqueEdges_apexTri hxy hzx hzy]
    simp only [Finset.mem_insert, Finset.mem_singleton, Sym2.mem_iff]
    constructor
    · rintro (rfl | rfl | rfl)
      · exact Or.inr ⟨x, Or.inl rfl, Sym2.eq_swap⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨y, Or.inr rfl, Sym2.eq_swap⟩
    · rintro (rfl | ⟨u, (rfl | rfl), rfl⟩)
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl Sym2.eq_swap
      · exact Or.inr (Or.inr Sym2.eq_swap)

/-! ### Apex assignments -/

/-- `f` is an **apex assignment** for `H`: every edge of `H` is a genuine edge, its apex is not one
of its endpoints, and the resulting triangles are pairwise edge-disjoint. -/
structure IsApexAssignment (H : Finset (Sym2 V)) (f : Sym2 V → V) : Prop where
  nondiag : ∀ e ∈ H, ¬ e.IsDiag
  apex_notMem : ∀ e ∈ H, f e ∉ e
  edge_disjoint : ∀ e ∈ H, ∀ e' ∈ H, e ≠ e' →
    Disjoint (cliqueEdges (apexTri e (f e))) (cliqueEdges (apexTri e' (f e')))

/-- The edges covered by an apex assignment form a triangle-decomposable set. -/
theorem triDecomp_apexCover {H : Finset (Sym2 V)} {f : Sym2 V → V}
    (h : IsApexAssignment H f) : TriDecomp (apexCover H f) := by
  classical
  refine ⟨apexFam H f, ?_, ?_, rfl⟩
  · intro t ht
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 ht
    exact card_apexTri (h.nondiag e he) (h.apex_notMem e he)
  · intro t ht t' ht' hne
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 ht
    obtain ⟨e', he', rfl⟩ := Finset.mem_image.1 ht'
    exact h.edge_disjoint e he e' he' (fun hc => hne (by rw [hc]))

theorem subset_apexCover {H : Finset (Sym2 V)} {f : Sym2 V → V}
    (hnd : ∀ e ∈ H, ¬ e.IsDiag) : H ⊆ apexCover H f := by
  intro e he
  refine Finset.mem_biUnion.2 ⟨apexTri e (f e), Finset.mem_image.2 ⟨e, he, rfl⟩, ?_⟩
  exact mem_cliqueEdges_apexTri (hnd e he)

theorem apexCover_eq_union {H : Finset (Sym2 V)} {f : Sym2 V → V}
    (hnd : ∀ e ∈ H, ¬ e.IsDiag) : apexCover H f = H ∪ apexEdges H f := by
  rw [apexEdges, Finset.union_sdiff_self_eq_union]
  exact (Finset.union_eq_right.2 (subset_apexCover hnd)).symm

/-! ### The reduction: only the *unused* reservoir remains -/

/-- **The covering step.**  If `f` is an apex assignment for `H` whose apex edges are reserved
(contained in `R`), then `R ∪ H` is triangle-decomposable as soon as the unused part of the
reservoir is. -/
theorem triDecomp_union_of_apexAssignment {R H : Finset (Sym2 V)} {f : Sym2 V → V}
    (hass : IsApexAssignment H f) (hd : Disjoint R H)
    (hAR : apexEdges H f ⊆ R) (hrest : TriDecomp (R \ apexEdges H f)) :
    TriDecomp (R ∪ H) := by
  classical
  have hsplit : R ∪ H = apexCover H f ∪ (R \ apexEdges H f) := by
    rw [apexCover_eq_union hass.nondiag]
    ext e
    simp only [Finset.mem_union, Finset.mem_sdiff]
    constructor
    · rintro (hR | hH)
      · by_cases hA : e ∈ apexEdges H f
        · exact Or.inl (Or.inr hA)
        · exact Or.inr ⟨hR, hA⟩
      · exact Or.inl (Or.inl hH)
    · rintro ((hH | hA) | ⟨hR, _⟩)
      · exact Or.inr hH
      · exact Or.inl (hAR hA)
      · exact Or.inl hR
  have hdisj : Disjoint (apexCover H f) (R \ apexEdges H f) := by
    rw [apexCover_eq_union hass.nondiag]
    refine Finset.disjoint_union_left.2 ⟨?_, ?_⟩
    · exact Finset.disjoint_of_subset_right Finset.sdiff_subset hd.symm
    · exact Finset.disjoint_sdiff
  rw [hsplit]
  exact TriDecomp.union hdisj (triDecomp_apexCover hass) hrest

/-- **The cover-down step.**  Same as `triDecomp_union_of_apexAssignment`, but only the unused
reservoir *minus a remainder `X`* has to be triangle-decomposable; the conclusion is then the
cover-down conclusion `TriDecomp ((R ∪ H) \ X)`. -/
theorem triDecomp_sdiff_of_apexAssignment {R H X : Finset (Sym2 V)} {f : Sym2 V → V}
    (hass : IsApexAssignment H f) (hd : Disjoint R H)
    (hAR : apexEdges H f ⊆ R) (hXsub : X ⊆ R \ apexEdges H f)
    (hrest : TriDecomp ((R \ apexEdges H f) \ X)) :
    TriDecomp ((R ∪ H) \ X) := by
  classical
  have hXH : Disjoint X H :=
    Finset.disjoint_of_subset_left (hXsub.trans Finset.sdiff_subset) hd
  have hXA : Disjoint X (apexEdges H f) :=
    Finset.disjoint_of_subset_left hXsub Finset.sdiff_disjoint
  have hsplit : (R ∪ H) \ X = apexCover H f ∪ ((R \ apexEdges H f) \ X) := by
    rw [apexCover_eq_union hass.nondiag]
    ext e
    simp only [Finset.mem_union, Finset.mem_sdiff]
    constructor
    · rintro ⟨hRH, hX⟩
      rcases hRH with hR | hH
      · by_cases hA : e ∈ apexEdges H f
        · exact Or.inl (Or.inr hA)
        · exact Or.inr ⟨⟨hR, hA⟩, hX⟩
      · exact Or.inl (Or.inl hH)
    · rintro ((hH | hA) | ⟨⟨hR, _⟩, hX⟩)
      · exact ⟨Or.inr hH, fun hc => (Finset.disjoint_left.1 hXH hc) hH⟩
      · exact ⟨Or.inl (hAR hA), fun hc => (Finset.disjoint_left.1 hXA hc) hA⟩
      · exact ⟨Or.inl hR, hX⟩
  have hdisj : Disjoint (apexCover H f) ((R \ apexEdges H f) \ X) := by
    rw [apexCover_eq_union hass.nondiag]
    refine Finset.disjoint_union_left.2 ⟨?_, ?_⟩
    · exact Finset.disjoint_of_subset_right (Finset.sdiff_subset.trans Finset.sdiff_subset) hd.symm
    · exact Finset.disjoint_of_subset_right Finset.sdiff_subset Finset.disjoint_sdiff
  rw [hsplit]
  exact TriDecomp.union hdisj (triDecomp_apexCover hass) hrest

/-! ### Edge-disjointness from an asymmetric role relation -/

/-- **Edge-disjointness of the covering triangles, general criterion.**

Let `P u v` be read as "`u` may serve as an endpoint and `v` as the apex of the reserved edge
`uv`".  If

* every endpoint `u` of an edge `e ∈ H` is allowed to use `f e` as apex (`hrole`),
* the relation is asymmetric at the vertices of `H` (`hasymm`) — this is what a *typed* reservoir
  (`apexRel`, below: a splitting of the reserved edges into two parts, one for each role) or a
  ranking of the apexes above the endpoints provides,
* apex edges are never edges of `H` (`hnotH`), and
* edges of `H` sharing a vertex get different apexes (`hconf`),

then the covering triangles are pairwise edge-disjoint.

The asymmetry hypothesis is exactly what rules out the "chain" collision, in which the apex `z` of
an edge `xy` is an endpoint of another edge `zy'` whose apex is `x`: those two triangles would
share the edge `xz`. -/
theorem isApexAssignment_of_asymm {H : Finset (Sym2 V)} {f : Sym2 V → V} {P : V → V → Prop}
    (hnd : ∀ e ∈ H, ¬ e.IsDiag)
    (hrole : ∀ e ∈ H, ∀ u ∈ e, P u (f e))
    (hasymm : ∀ e ∈ H, ∀ u ∈ e, ∀ v : V, P u v → ¬ P v u)
    (hnotH : ∀ e ∈ H, ∀ u ∈ e, s(u, f e) ∉ H)
    (hconf : ∀ e ∈ H, ∀ e' ∈ H, e ≠ e' → (∃ v, v ∈ e ∧ v ∈ e') → f e ≠ f e') :
    IsApexAssignment H f := by
  have hnotMem : ∀ e ∈ H, f e ∉ e := fun e he hmem =>
    hasymm e he (f e) hmem (f e) (hrole e he _ hmem) (hrole e he _ hmem)
  refine ⟨hnd, hnotMem, ?_⟩
  intro e he e' he' hne
  induction e using Sym2.ind with
  | _ x y =>
    induction e' using Sym2.ind with
    | _ a b =>
      have hxy : x ≠ y := by simpa [Sym2.isDiag_iff_proj_eq] using hnd _ he
      have hab : a ≠ b := by simpa [Sym2.isDiag_iff_proj_eq] using hnd _ he'
      set z := f s(x, y) with hz
      set w := f s(a, b) with hw
      have hzx : z ≠ x := fun h => hnotMem _ he (by rw [← hz, h]; simp)
      have hzy : z ≠ y := fun h => hnotMem _ he (by rw [← hz, h]; simp)
      have hwa : w ≠ a := fun h => hnotMem _ he' (by rw [← hw, h]; simp)
      have hwb : w ≠ b := fun h => hnotMem _ he' (by rw [← hw, h]; simp)
      have hzw : (∃ v, v ∈ (s(x, y) : Sym2 V) ∧ v ∈ (s(a, b) : Sym2 V)) → z ≠ w :=
        fun hmeet => hconf _ he _ he' hne hmeet
      -- the apex edges of the two triangles are not edges of `H`
      have hzedge : ∀ u : V, u ∈ (s(x, y) : Sym2 V) → (s(z, u) : Sym2 V) ∉ H := by
        intro u hu
        rw [Sym2.eq_swap]
        exact hnotH _ he u hu
      have hwedge : ∀ v : V, v ∈ (s(a, b) : Sym2 V) → (s(w, v) : Sym2 V) ∉ H := by
        intro v hv
        rw [Sym2.eq_swap]
        exact hnotH _ he' v hv
      -- the chain collision is impossible
      have hchain : ∀ u : V, u ∈ (s(x, y) : Sym2 V) → ∀ v : V, v ∈ (s(a, b) : Sym2 V) →
          ¬ (z = v ∧ u = w) := by
        rintro u hu v hv ⟨h1, h2⟩
        have hPvw : P v w := hrole _ he' v hv
        rw [← h1, ← h2] at hPvw
        exact hasymm _ he u hu z (hrole _ he u hu) hPvw
      rw [cliqueEdges_apexTri hxy hzx hzy, cliqueEdges_apexTri hab hwa hwb, Finset.disjoint_left]
      intro g hmem hmem'
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem hmem'
      have main : ∀ u : V, u ∈ (s(x, y) : Sym2 V) → ∀ v : V, v ∈ (s(a, b) : Sym2 V) →
          (s(z, u) : Sym2 V) ≠ s(w, v) := by
        intro u hu v hv heq
        rcases Sym2.eq_iff.1 heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact hzw ⟨u, hu, h2 ▸ hv⟩ h1
        · exact hchain u hu v hv ⟨h1, h2⟩
      rcases hmem with rfl | rfl | rfl
      · rcases hmem' with h | h | h
        · exact main x (by simp) a (by simp) h
        · exact hzedge x (by simp) (h ▸ he')
        · exact main x (by simp) b (by simp) h
      · rcases hmem' with h | h | h
        · exact hwedge a (by simp) (h ▸ he)
        · exact hne h
        · exact hwedge b (by simp) (h ▸ he)
      · rcases hmem' with h | h | h
        · exact main y (by simp) a (by simp) h
        · exact hzedge y (by simp) (h ▸ he')
        · exact main y (by simp) b (by simp) h

/-! ### Edge-disjointness from freshness and conflict-freeness -/

/-- **Fresh, conflict-free apexes give edge-disjoint triangles.**

*Freshness*: no apex is incident to an edge of `H` (so an apex edge is never an edge of `H`, and
an apex is never an endpoint of an edge of `H`).
*Conflict-freeness*: two edges of `H` sharing a vertex get different apexes.

These two conditions are exactly what a greedy choice can guarantee, and they imply that the
triangles are pairwise edge-disjoint. -/
theorem isApexAssignment_of_fresh {H : Finset (Sym2 V)} {f : Sym2 V → V}
    (hnd : ∀ e ∈ H, ¬ e.IsDiag)
    (hfresh : ∀ e ∈ H, ∀ e' ∈ H, f e ∉ e')
    (hconf : ∀ e ∈ H, ∀ e' ∈ H, e ≠ e' → (∃ v, v ∈ e ∧ v ∈ e') → f e ≠ f e') :
    IsApexAssignment H f := by
  refine isApexAssignment_of_asymm (P := fun _ v => ∀ e ∈ H, v ∉ e) hnd
    (fun e he u _ e'' he'' => hfresh e he e'' he'') (fun e he u hu v _ hvu => hvu _ he hu)
    (fun e he u hu hmem => hfresh e he _ hmem (by simp)) hconf

/-! ### Existence of a conflict-free apex choice: the greedy bound -/

/-- The edges of `H` meeting a given edge. -/
private def meeting (H : Finset (Sym2 V)) (e : Sym2 V) : Finset (Sym2 V) :=
  H.filter (fun e' => ¬ Disjoint (Sym2.toFinset e) (Sym2.toFinset e'))

private theorem mem_meeting {H : Finset (Sym2 V)} {e e' : Sym2 V} :
    e' ∈ meeting H e ↔ e' ∈ H ∧ ∃ v, v ∈ e ∧ v ∈ e' := by
  rw [meeting, Finset.mem_filter, Finset.not_disjoint_iff]
  simp

private theorem card_meeting_le {H : Finset (Sym2 V)} {x y : V} {D : ℕ}
    (hdeg : ∀ v : V, edeg H v ≤ D) : (meeting H s(x, y)).card ≤ 2 * D := by
  classical
  have hsub : meeting H s(x, y) ⊆ H.filter (fun e' => x ∈ e') ∪ H.filter (fun e' => y ∈ e') := by
    intro e' he'
    rw [mem_meeting] at he'
    obtain ⟨heH, v, hv, hv'⟩ := he'
    simp only [Sym2.mem_iff] at hv
    rcases hv with rfl | rfl
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨heH, hv'⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨heH, hv'⟩)
  calc (meeting H s(x, y)).card ≤ _ := Finset.card_le_card hsub
    _ ≤ (H.filter (fun e' => x ∈ e')).card + (H.filter (fun e' => y ∈ e')).card :=
        Finset.card_union_le _ _
    _ ≤ D + D := Nat.add_le_add (hdeg x) (hdeg y)
    _ = 2 * D := by ring

/-- **Greedy existence of a conflict-free apex choice.**  If every edge of `H` has more than `2D`
candidate apexes and `Δ(H) ≤ D`, then one can choose, for each edge of `H`, a candidate apex so
that edges of `H` sharing a vertex receive different apexes.

The bound `2D` is precisely the "load" of an edge: an edge `xy` of `H` meets at most
`deg(x) + deg(y) ≤ 2D` other edges of `H`. -/
theorem exists_apex_fun (D : ℕ) (N : Sym2 V → Finset V) :
    ∀ H : Finset (Sym2 V), (∀ v : V, edeg H v ≤ D) → (∀ e ∈ H, 2 * D < (N e).card) →
      ∃ f : Sym2 V → V, (∀ e ∈ H, f e ∈ N e) ∧
        ∀ e ∈ H, ∀ e' ∈ H, e ≠ e' → (∃ v, v ∈ e ∧ v ∈ e') → f e ≠ f e' := by
  classical
  intro H
  induction H using Finset.strongInduction with
  | _ H ih =>
    intro hdeg hN
    rcases Finset.eq_empty_or_nonempty H with rfl | ⟨e₀, he₀⟩
    · exact ⟨fun e => (Quot.out e).1, by simp, by simp⟩
    -- peel off one edge
    set H' := H.erase e₀ with hH'
    have hH'sub : H' ⊂ H := Finset.erase_ssubset he₀
    have hdeg' : ∀ v : V, edeg H' v ≤ D := fun v =>
      le_trans (edeg_mono (Finset.erase_subset _ _) v) (hdeg v)
    obtain ⟨f, hfN, hfconf⟩ := ih H' hH'sub hdeg' (fun e he => hN e (Finset.mem_of_mem_erase he))
    -- the forbidden apexes for `e₀`
    set F : Finset V := (meeting H' e₀).image f with hF
    have hFcard : F.card ≤ 2 * D := by
      refine le_trans (Finset.card_image_le) ?_
      induction e₀ using Sym2.ind with
      | _ x y => exact card_meeting_le hdeg'
    have hlt : F.card < (N e₀).card := lt_of_le_of_lt hFcard (hN e₀ he₀)
    obtain ⟨z, hzN, hzF⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    refine ⟨Function.update f e₀ z, ?_, ?_⟩
    · intro e he
      by_cases hee : e = e₀
      · subst hee; simpa using hzN
      · rw [Function.update_of_ne hee]
        exact hfN e (Finset.mem_erase.2 ⟨hee, he⟩)
    · intro e he e' he' hne hmeet
      have key : ∀ a ∈ H, a ≠ e₀ → (∃ v, v ∈ e₀ ∧ v ∈ a) → z ≠ f a := by
        intro a ha hane hmeeta hcon
        refine hzF ?_
        rw [hF]
        exact Finset.mem_image.2
          ⟨a, mem_meeting.2 ⟨Finset.mem_erase.2 ⟨hane, ha⟩, hmeeta⟩, hcon.symm⟩
      by_cases h1 : e = e₀ <;> by_cases h2 : e' = e₀
      · exact absurd (h1.trans h2.symm) hne
      · subst h1
        rw [Function.update_self, Function.update_of_ne h2]
        exact key e' he' h2 hmeet
      · subst h2
        rw [Function.update_self, Function.update_of_ne h1]
        refine fun hcon => key e he h1 ?_ hcon.symm
        obtain ⟨v, hv, hv'⟩ := hmeet
        exact ⟨v, hv', hv⟩
      · rw [Function.update_of_ne h1, Function.update_of_ne h2]
        exact hfconf e (Finset.mem_erase.2 ⟨h1, he⟩) e' (Finset.mem_erase.2 ⟨h2, he'⟩) hne hmeet

/-! ### The Hall variant -/

/-- **Hall's theorem for apexes.**  If the bipartite auxiliary graph between the edges of `H` and
the candidate apexes satisfies Hall's condition, then all apexes can be chosen *distinct*.  This is
Mathlib's `Finset.all_card_le_biUnion_card_iff_exists_injective` applied to the candidate family.

Distinct apexes are of course conflict-free, so this feeds `isApexAssignment_of_fresh` as well. -/
theorem exists_injective_apex_fun {H : Finset (Sym2 V)} {N : Sym2 V → Finset V}
    (hall : ∀ F ⊆ H, F.card ≤ (F.biUnion N).card) :
    ∃ f : Sym2 V → V, (∀ e ∈ H, f e ∈ N e) ∧
      ∀ e ∈ H, ∀ e' ∈ H, e ≠ e' → f e ≠ f e' := by
  classical
  set t : {e // e ∈ H} → Finset V := fun e => N (e : Sym2 V) with ht
  have hcond : ∀ s : Finset {e // e ∈ H}, s.card ≤ (s.biUnion t).card := by
    intro s
    have himg : (s.image (Subtype.val : {e // e ∈ H} → Sym2 V)) ⊆ H := by
      intro e he
      obtain ⟨e', _, rfl⟩ := Finset.mem_image.1 he
      exact e'.2
    have hcard : s.card = (s.image (Subtype.val : {e // e ∈ H} → Sym2 V)).card :=
      (Finset.card_image_of_injective _ Subtype.val_injective).symm
    have hbi : (s.image (Subtype.val : {e // e ∈ H} → Sym2 V)).biUnion N = s.biUnion t := by
      ext v
      simp only [Finset.mem_biUnion, Finset.mem_image, ht]
      constructor
      · rintro ⟨e, ⟨e', he', rfl⟩, hv⟩; exact ⟨e', he', hv⟩
      · rintro ⟨e, he, hv⟩; exact ⟨(e : Sym2 V), ⟨e, he, rfl⟩, hv⟩
    rw [hcard, ← hbi]
    exact hall _ himg
  obtain ⟨g, hginj, hgmem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_exists_injective t).1 hcond
  refine ⟨fun e => if h : e ∈ H then g ⟨e, h⟩ else (Quot.out e).1, ?_, ?_⟩
  · intro e he
    simpa [he] using hgmem ⟨e, he⟩
  · intro e he e' he' hne
    simp only [he, he', dif_pos]
    intro hcon
    exact hne (congrArg Subtype.val (hginj hcon))

/-! ### The load bound coming from the density hypothesis -/

/-- Each edge at `x` gives a neighbour of `x` inside `S`. -/
theorem edeg_le_degTo {E : Finset (Sym2 V)} {S : Finset V} (hES : E ⊆ cliqueEdges S) (x : V) :
    edeg E x ≤ degTo E x S := by
  classical
  set g : Sym2 V → V := fun e => if h : x ∈ e then Sym2.Mem.other' h else x with hg
  have hspec : ∀ e ∈ E.filter (fun e => x ∈ e), s(x, g e) = e ∧ g e ∈ S := by
    intro e he
    obtain ⟨heE, hxe⟩ := Finset.mem_filter.1 he
    have hgdef : g e = Sym2.Mem.other' hxe := by simp [hg, dif_pos hxe]
    have hs : s(x, g e) = e := by rw [hgdef]; exact Sym2.other_spec' hxe
    have hmem : g e ∈ e := by rw [hgdef]; exact Sym2.other_mem' hxe
    exact ⟨hs, (mem_cliqueEdgesV.1 (hES heE)).1 _ hmem⟩
  have himg : (E.filter (fun e => x ∈ e)).image g ⊆ nbhdIn E x S := by
    intro w hw
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hw
    obtain ⟨hs, hS⟩ := hspec e he
    exact mem_nbhdIn.2 ⟨hS, by rw [hs]; exact (Finset.mem_filter.1 he).1⟩
  have hinj : Set.InjOn g (E.filter (fun e => x ∈ e)) := by
    intro e he e' he' heq
    rw [← (hspec e he).1, ← (hspec e' he').1, heq]
  calc edeg E x = ((E.filter (fun e => x ∈ e)).image g).card :=
        (Finset.card_image_of_injOn hinj).symm
    _ ≤ degTo E x S := Finset.card_le_card himg

/-- Two neighbourhoods inside `S` have many common elements. -/
theorem card_common_nbhd_ge (E : Finset (Sym2 V)) (S : Finset V) (x y : V) (W : Finset V) :
    degTo E x S + degTo E y S ≤
      S.card + W.card + ((nbhdIn E x S ∩ nbhdIn E y S) \ W).card := by
  classical
  have hunion : (nbhdIn E x S ∪ nbhdIn E y S).card ≤ S.card :=
    Finset.card_le_card (Finset.union_subset (nbhdIn_subset _ _ _) (nbhdIn_subset _ _ _))
  have hinter : (nbhdIn E x S ∩ nbhdIn E y S).card
      ≤ W.card + ((nbhdIn E x S ∩ nbhdIn E y S) \ W).card := by
    calc (nbhdIn E x S ∩ nbhdIn E y S).card
        ≤ (W ∪ ((nbhdIn E x S ∩ nbhdIn E y S) \ W)).card := by
          refine Finset.card_le_card ?_
          intro v hv
          by_cases hW : v ∈ W
          · exact Finset.mem_union_left _ hW
          · exact Finset.mem_union_right _ (Finset.mem_sdiff.2 ⟨hv, hW⟩)
      _ ≤ _ := Finset.card_union_le _ _
  have := Finset.card_union_add_card_inter (nbhdIn E x S) (nbhdIn E y S)
  unfold degTo
  omega

/-- **The load bound from the density hypothesis.**  In a host of minimum degree
`(9/10 + γ)|S|`, every pair of vertices has at least `(4/5 + 2γ)|S| − |W|` common neighbours
outside an arbitrary excluded set `W`.  This is what guarantees, in the covering-matching argument,
that every edge of the leftover has many candidate apexes. -/
theorem card_common_nbhd_dense {E : Finset (Sym2 V)} {S : Finset V} {γ : ℝ}
    (hES : E ⊆ cliqueEdges S)
    (hdeg : ∀ v ∈ S, (9 / 10 + γ) * (S.card : ℝ) ≤ (edeg E v : ℝ))
    {x y : V} (hx : x ∈ S) (hy : y ∈ S) (W : Finset V) :
    (4 / 5 + 2 * γ) * (S.card : ℝ) - (W.card : ℝ) ≤
      (((nbhdIn E x S ∩ nbhdIn E y S) \ W).card : ℝ) := by
  have h1 : (edeg E x : ℝ) ≤ (degTo E x S : ℝ) := by
    exact_mod_cast edeg_le_degTo hES x
  have h2 : (edeg E y : ℝ) ≤ (degTo E y S : ℝ) := by
    exact_mod_cast edeg_le_degTo hES y
  have h3 := hdeg x hx
  have h4 := hdeg y hy
  have h5 : (degTo E x S : ℝ) + (degTo E y S : ℝ) ≤
      (S.card : ℝ) + (W.card : ℝ) + (((nbhdIn E x S ∩ nbhdIn E y S) \ W).card : ℝ) := by
    exact_mod_cast card_common_nbhd_ge E S x y W
  linarith only [h1, h2, h3, h4, h5]

/-- **Every pair has more than `2D` common neighbours in a large dense host.**  This is the form
in which the density hypothesis feeds the greedy apex choice: the candidate sets are large, while
`Δ(H) ≤ D` keeps the load at most `2D`.  (For the covering argument the candidates must moreover
be joined to both endpoints by *reserved* edges; that is the content of the remaining gap.) -/
theorem card_common_nbhd_gt {E : Finset (Sym2 V)} {S : Finset V} {γ : ℝ} {D : ℕ}
    (hES : E ⊆ cliqueEdges S) (hγ : 0 ≤ γ)
    (hdeg : ∀ v ∈ S, (9 / 10 + γ) * (S.card : ℝ) ≤ (edeg E v : ℝ))
    (hn : (2 * D : ℝ) < 4 / 5 * (S.card : ℝ)) {x y : V} (hx : x ∈ S) (hy : y ∈ S) :
    2 * D < (nbhdIn E x S ∩ nbhdIn E y S).card := by
  have h := card_common_nbhd_dense hES hdeg hx hy ∅
  simp only [Finset.card_empty, Nat.cast_zero, sub_zero, Finset.sdiff_empty] at h
  have hS : (0 : ℝ) ≤ (S.card : ℝ) := Nat.cast_nonneg _
  have : (2 * D : ℝ) < ((nbhdIn E x S ∩ nbhdIn E y S).card : ℝ) := by nlinarith only [hγ, hn, h]
  exact_mod_cast this

end BKLO
