/-
# Nibble — routing the Dross deficiency through the links

`Nibble.DrossScaledCorrection` (see `Nibble/DrossResidual.lean`) is an exact reformulation of the
spread Dross input `Nibble.DrossFractionalQuantSpread`: a **signed** triangle weighting whose
coverage at every edge `e` is the deficiency `1 - K·codeg(e)/(|V|-2)` of the uniform base weighting
`K/(|V|-2)`, with all weights bounded by `K/(|V|-2)`.

This file reduces that *edge*-prescription problem to a family of **local vertex-prescription**
problems, one for each vertex, via the `K₄` exchange gadget of `Nibble/DrossGadget.lean`.

The idea: a gadget with apex `u` and core `{x, y, z} ⊆ N(u)` shifts the coverage by `+2` on the
three edges `ux`, `uy`, `uz` and by `0` everywhere else.  So a weighting `b u ·` of the triangles
of the *link* of `u` delivers, at the edge `uv`, exactly twice the total weight `b u` puts on the
link triangles **through `v`** — a condition on the *vertex degrees* of `b u` inside the link, not
on its edge degrees.  Summing the gadgets over all apices, the cores cancel against the apex
triangles and only the star deliveries survive.

* `Nibble.linkVertexSum` — the vertex degree of `b u` at `v`: the total weight `b u` puts on
  triangles through `v`.
* `Nibble.IsLinkCore` — the support condition: `b u` is carried by triangles inside the link of `u`.
* `Nibble.linkCorrection` — the assembled signed triangle weighting.
* `Nibble.sum_linkCorrection_eq` — **the coverage identity**: the coverage of `linkCorrection` at
  an edge `{v₁, v₂}` is `2·(linkVertexSum b v₁ v₂ + linkVertexSum b v₂ v₁)`, with all the cores
  cancelling.  This is the heart of the file and is unconditional.
* `Nibble.abs_linkCorrection_le` — **the weight bound**: weights of size `B/|V|²` in the links
  assemble to a correction of size `4B/|V|`.
* `Nibble.IsLinkDeficiencyRouting`, `Nibble.isScaledDeficiencyCorrection_of_linkRouting` — the
  local problem and the reduction.
* `Nibble.DrossLinkRouting`, `Nibble.drossFractionalQuantSpread_of_linkRouting`,
  `Nibble.denseTriangleNibbleDeg_of_linkRouting` — the global statement and the machine-checked
  chain down to the per-vertex nibble bound.

Sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.DrossResidual
import Nibble.DrossGadget
import Nibble.DrossSplitGraph

open Finset SimpleGraph Hypergraph Nibble.YusterE

namespace Nibble

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ### Link weightings -/

/-- **The vertex degree of the link weighting `b u` at `v`**: the total weight that `b u` puts on
triangles through `v`. -/
noncomputable def linkVertexSum (G : SimpleGraph V) [DecidableRel G.Adj]
    (b : V → Finset V → ℝ) (u v : V) : ℝ :=
  ∑ t ∈ (G.cliqueFinset 3).filter (fun t => v ∈ t), b u t

/-- **The support condition**: `b u` is carried by triangles of `G` lying inside the link of `u`. -/
def IsLinkCore (G : SimpleGraph V) [DecidableRel G.Adj] (b : V → Finset V → ℝ) : Prop :=
  ∀ u t, b u t ≠ 0 → t ∈ G.cliqueFinset 3 ∧ ∀ x ∈ t, G.Adj u x

/-- **The assembled correction.**  Superposing, over all apices `u`, the `K₄` gadgets with apex `u`
and core weights `b u`, the triangle `s` picks up `+b p t` for every apex `p ∈ s` and every core
`t` containing the opposite edge `s \ {p}`, and `-b u s` for every apex `u` using `s` as a core. -/
noncomputable def linkCorrection (G : SimpleGraph V) [DecidableRel G.Adj]
    (b : V → Finset V → ℝ) (T : Finset (EdgeV G)) : ℝ :=
  (∑ p ∈ triOf G T,
      ∑ t ∈ (G.cliqueFinset 3).filter (fun t => (triOf G T).erase p ⊆ t), b p t)
    - ∑ u : V, b u (triOf G T)

/-! ### Reindexing dictionaries -/

/-- Summing over the `3`-cliques containing an edge is summing over its common neighbourhood. -/
theorem sum_cliqueFinset3_supset_eq (G : SimpleGraph V) [DecidableRel G.Adj] (e : EdgeV G)
    (f : Finset V → ℝ) :
    ∑ t ∈ (G.cliqueFinset 3).filter (fun t => e.val ⊆ t), f t
      = ∑ z ∈ commonNbrs G e, f (insert z e.val) := by
  classical
  rw [cliqueFinset3_filter_supset_eq_image G e, Finset.sum_image]
  intro z hz z' hz' heq
  exact insert_commonNbrs_injOn G e (by simpa using hz) (by simpa using hz') heq

/-- **Membership in the common neighbourhood**, unfolded. -/
theorem mem_commonNbrs_iff (G : SimpleGraph V) [DecidableRel G.Adj] {e : EdgeV G} {v₁ v₂ : V}
    (hval : e.val = ({v₁, v₂} : Finset V)) (z : V) :
    z ∈ commonNbrs G e ↔ (G.Adj v₁ z ∧ G.Adj v₂ z) := by
  simp [commonNbrs, hval]

/-- **The counting identity.**  Summing, over all `z`, the weight `b u` puts on the triangles
containing both `z` and `v` counts every triangle through `v` exactly three times. -/
theorem sum_univ_sum_filter_pair (G : SimpleGraph V) [DecidableRel G.Adj]
    (b : V → Finset V → ℝ) (u v : V) :
    ∑ z : V, ∑ t ∈ (G.cliqueFinset 3).filter (fun t => (insert z {v} : Finset V) ⊆ t), b u t
      = 3 * linkVertexSum G b u v := by
  classical
  have key : ∀ t ∈ G.cliqueFinset 3,
      (∑ _z : V, if (insert _z {v} : Finset V) ⊆ t then b u t else 0)
        = if v ∈ t then 3 * b u t else 0 := by
    intro t ht
    have htc : t.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp ht).card_eq
    by_cases hv : v ∈ t
    · rw [if_pos hv]
      have hcond : ∀ z : V, (if (insert z {v} : Finset V) ⊆ t then b u t else 0)
          = if z ∈ t then b u t else 0 := by
        intro z
        congr 1
        simp [Finset.insert_subset_iff, hv]
      simp only [hcond]
      rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, htc, nsmul_eq_mul]
      norm_num
    · rw [if_neg hv]
      refine Finset.sum_eq_zero (fun z _ => ?_)
      rw [if_neg]
      intro hsub
      exact hv (hsub (by simp))
  calc ∑ z : V, ∑ t ∈ (G.cliqueFinset 3).filter (fun t => (insert z {v} : Finset V) ⊆ t), b u t
      = ∑ z : V, ∑ t ∈ G.cliqueFinset 3,
          (if (insert z {v} : Finset V) ⊆ t then b u t else 0) := by
        refine Finset.sum_congr rfl (fun z _ => ?_)
        rw [Finset.sum_filter]
    _ = ∑ t ∈ G.cliqueFinset 3, ∑ z : V,
          (if (insert z {v} : Finset V) ⊆ t then b u t else 0) := Finset.sum_comm
    _ = ∑ t ∈ G.cliqueFinset 3, (if v ∈ t then 3 * b u t else 0) :=
        Finset.sum_congr rfl key
    _ = 3 * linkVertexSum G b u v := by
        rw [linkVertexSum, Finset.mul_sum, Finset.sum_filter]

/-- **The star delivery.**  For an edge `e = {v₁, v₂}`, summing over the common neighbours `z` of
`e` the weight `b v₁` puts on the triangles through `z` and `v₂` gives exactly twice the vertex
degree of `b v₁` at `v₂`. -/
theorem sum_commonNbrs_sum_filter_pair (G : SimpleGraph V) [DecidableRel G.Adj]
    {b : V → Finset V → ℝ} (hb : IsLinkCore G b) {e : EdgeV G} {v₁ v₂ : V} (hne : v₁ ≠ v₂)
    (hval : e.val = ({v₁, v₂} : Finset V)) :
    ∑ z ∈ commonNbrs G e,
        ∑ t ∈ (G.cliqueFinset 3).filter (fun t => (insert z {v₂} : Finset V) ⊆ t), b v₁ t
      = 2 * linkVertexSum G b v₁ v₂ := by
  classical
  have hv₂ : v₂ ∉ commonNbrs G e := by
    rw [mem_commonNbrs_iff G hval]
    rintro ⟨-, h2⟩
    exact h2.ne rfl
  -- the terms outside `insert v₂ (commonNbrs G e)` vanish
  have hzero : ∀ z ∈ (Finset.univ : Finset V), z ∉ insert v₂ (commonNbrs G e) →
      (∑ t ∈ (G.cliqueFinset 3).filter (fun t => (insert z {v₂} : Finset V) ⊆ t), b v₁ t)
        = 0 := by
    intro z _ hz
    refine Finset.sum_eq_zero (fun t ht => ?_)
    by_contra hbt
    obtain ⟨htc, hadj⟩ := hb v₁ t hbt
    rw [Finset.mem_filter] at ht
    have hzt : z ∈ t := ht.2 (by simp)
    have hv₂t : v₂ ∈ t := ht.2 (by simp)
    have hzv₂ : z ≠ v₂ := by
      rintro rfl
      exact hz (Finset.mem_insert_self _ _)
    have h1 : G.Adj v₁ z := hadj z hzt
    have h2 : G.Adj z v₂ :=
      (SimpleGraph.mem_cliqueFinset_iff.mp htc).isClique hzt hv₂t hzv₂
    exact hz (Finset.mem_insert_of_mem ((mem_commonNbrs_iff G hval z).mpr ⟨h1, h2.symm⟩))
  have huniv :
      (∑ z : V, ∑ t ∈ (G.cliqueFinset 3).filter (fun t => (insert z {v₂} : Finset V) ⊆ t), b v₁ t)
        = ∑ z ∈ insert v₂ (commonNbrs G e),
            ∑ t ∈ (G.cliqueFinset 3).filter (fun t => (insert z {v₂} : Finset V) ⊆ t), b v₁ t :=
    (Finset.sum_subset (Finset.subset_univ _) hzero).symm
  have h3 :
      (∑ z : V, ∑ t ∈ (G.cliqueFinset 3).filter (fun t => (insert z {v₂} : Finset V) ⊆ t),
          b v₁ t) = 3 * linkVertexSum G b v₁ v₂ :=
    sum_univ_sum_filter_pair G b v₁ v₂
  have hPv₂ :
      (∑ t ∈ (G.cliqueFinset 3).filter (fun t => (insert v₂ {v₂} : Finset V) ⊆ t), b v₁ t)
        = linkVertexSum G b v₁ v₂ := by
    rw [linkVertexSum]
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    refine Finset.filter_congr (fun t _ => ?_)
    simp
  rw [Finset.sum_insert hv₂, hPv₂, h3] at huniv
  linarith only [huniv]

/-! ### The coverage identity -/

/-- **The coverage of the assembled correction.**  At the edge `e = {v₁, v₂}` the cores of all the
gadgets cancel against the apex triangles, and what survives is exactly twice the two link vertex
degrees `linkVertexSum b v₁ v₂` and `linkVertexSum b v₂ v₁`. -/
theorem sum_linkCorrection_eq (G : SimpleGraph V) [DecidableRel G.Adj]
    {b : V → Finset V → ℝ} (hb : IsLinkCore G b) (e : EdgeV G) {v₁ v₂ : V} (hne : v₁ ≠ v₂)
    (hval : e.val = ({v₁, v₂} : Finset V)) :
    ∑ T ∈ trianglesThrough G e, linkCorrection G b T
      = 2 * (linkVertexSum G b v₁ v₂ + linkVertexSum G b v₂ v₁) := by
  classical
  -- pass to a sum over the common neighbourhood
  have hdict := sum_trianglesThrough_eq_commonNbrs G e
    (fun s => (∑ p ∈ s, ∑ t ∈ (G.cliqueFinset 3).filter (fun t => s.erase p ⊆ t), b p t)
      - ∑ u : V, b u s)
  have hLHS : ∑ T ∈ trianglesThrough G e, linkCorrection G b T
      = ∑ z ∈ commonNbrs G e,
          ((∑ p ∈ insert z e.val,
              ∑ t ∈ (G.cliqueFinset 3).filter (fun t => (insert z e.val).erase p ⊆ t), b p t)
            - ∑ u : V, b u (insert z e.val)) := hdict
  rw [hLHS, Finset.sum_sub_distrib]
  -- expand the apex sum of each triangle `{z, v₁, v₂}`
  have hexp : ∀ z ∈ commonNbrs G e,
      (∑ p ∈ insert z e.val,
          ∑ t ∈ (G.cliqueFinset 3).filter (fun t => (insert z e.val).erase p ⊆ t), b p t)
        = (∑ t ∈ (G.cliqueFinset 3).filter (fun t => e.val ⊆ t), b z t)
          + (∑ t ∈ (G.cliqueFinset 3).filter
              (fun t => (insert z {v₂} : Finset V) ⊆ t), b v₁ t)
          + ∑ t ∈ (G.cliqueFinset 3).filter
              (fun t => (insert z {v₁} : Finset V) ⊆ t), b v₂ t := by
    intro z hz
    rw [mem_commonNbrs_iff G hval] at hz
    have hzv₁ : z ≠ v₁ := hz.1.ne'
    have hzv₂ : z ≠ v₂ := hz.2.ne'
    have hznot : z ∉ e.val := by
      rw [hval]
      simp [hzv₁, hzv₂]
    have hv₁not : v₁ ∉ ({v₂} : Finset V) := by simp [hne]
    -- the three erasures
    have he_z : (insert z ({v₁, v₂} : Finset V)).erase z = ({v₁, v₂} : Finset V) :=
      Finset.erase_insert (by simp [hzv₁, hzv₂])
    have he_v₁ : (insert z ({v₁, v₂} : Finset V)).erase v₁ = insert z {v₂} := by
      ext a
      simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨ha, rfl | rfl | rfl⟩
        · exact Or.inl rfl
        · exact absurd rfl ha
        · exact Or.inr rfl
      · rintro (rfl | rfl)
        · exact ⟨hzv₁, Or.inl rfl⟩
        · exact ⟨Ne.symm hne, Or.inr (Or.inr rfl)⟩
    have he_v₂ : (insert z ({v₁, v₂} : Finset V)).erase v₂ = insert z {v₁} := by
      ext a
      simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨ha, rfl | rfl | rfl⟩
        · exact Or.inl rfl
        · exact Or.inr rfl
        · exact absurd rfl ha
      · rintro (rfl | rfl)
        · exact ⟨hzv₂, Or.inl rfl⟩
        · exact ⟨hne, Or.inr (Or.inl rfl)⟩
    rw [hval, Finset.sum_insert (by simp [hzv₁, hzv₂]), Finset.sum_insert (by simp [hne]),
      Finset.sum_singleton, he_z, he_v₁, he_v₂]
    ring
  rw [Finset.sum_congr rfl hexp]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  -- the cores cancel against the apex triangles at the apex `z`
  have hcancel : ∑ z ∈ commonNbrs G e,
      (∑ t ∈ (G.cliqueFinset 3).filter (fun t => e.val ⊆ t), b z t)
        = ∑ z ∈ commonNbrs G e, ∑ u : V, b u (insert z e.val) := by
    have hleft : ∀ z ∈ commonNbrs G e,
        (∑ t ∈ (G.cliqueFinset 3).filter (fun t => e.val ⊆ t), b z t)
          = ∑ z' ∈ commonNbrs G e, b z (insert z' e.val) := fun z _ =>
      sum_cliqueFinset3_supset_eq G e (fun t => b z t)
    rw [Finset.sum_congr rfl hleft]
    have hright : ∑ z ∈ commonNbrs G e, ∑ u : V, b u (insert z e.val)
        = ∑ u : V, ∑ z ∈ commonNbrs G e, b u (insert z e.val) := Finset.sum_comm
    rw [hright]
    refine Finset.sum_subset (Finset.subset_univ (commonNbrs G e)) ?_
    intro u _ hu
    refine Finset.sum_eq_zero (fun z hz => ?_)
    by_contra hbu
    obtain ⟨-, hadj⟩ := hb u (insert z e.val) hbu
    have h1 : G.Adj u v₁ := hadj v₁ (by rw [hval]; simp)
    have h2 : G.Adj u v₂ := hadj v₂ (by rw [hval]; simp)
    exact hu ((mem_commonNbrs_iff G hval u).mpr ⟨h1.symm, h2.symm⟩)
  rw [hcancel]
  -- the two star deliveries
  have hstar₁ := sum_commonNbrs_sum_filter_pair G hb hne hval
  have hval' : e.val = ({v₂, v₁} : Finset V) := by
    rw [hval]
    exact Finset.pair_comm v₁ v₂
  have hstar₂ := sum_commonNbrs_sum_filter_pair G hb (Ne.symm hne) hval'
  rw [hstar₁, hstar₂]
  ring

/-! ### The weight bound -/

/-- There are at most `|V|` triangles through a given pair of vertices. -/
theorem card_cliqueFinset3_filter_supset_le (G : SimpleGraph V) [DecidableRel G.Adj]
    {q : Finset V} (hq : q.card = 2) :
    (((G.cliqueFinset 3).filter (fun t => q ⊆ t)).card : ℝ) ≤ (Fintype.card V : ℝ) := by
  classical
  have hsub : (G.cliqueFinset 3).filter (fun t => q ⊆ t)
      ⊆ (Finset.univ : Finset V).image (fun z : V => insert z q) := by
    intro t ht
    rw [Finset.mem_filter, SimpleGraph.mem_cliqueFinset_iff] at ht
    have hcard : (t \ q).card = 1 := by
      rw [Finset.card_sdiff_of_subset ht.2, ht.1.card_eq, hq]
    obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hcard
    have hzt : z ∈ t \ q := by rw [hz]; exact Finset.mem_singleton_self z
    rw [Finset.mem_sdiff] at hzt
    refine Finset.mem_image.mpr ⟨z, Finset.mem_univ _, ?_⟩
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hzt.1
      · exact ht.2 hx
    · rw [ht.1.card_eq, Finset.card_insert_of_notMem hzt.2, hq]
  have h1 : ((G.cliqueFinset 3).filter (fun t => q ⊆ t)).card ≤ Fintype.card V := by
    calc ((G.cliqueFinset 3).filter (fun t => q ⊆ t)).card
        ≤ ((Finset.univ : Finset V).image (fun z : V => insert z q)).card :=
          Finset.card_le_card hsub
      _ ≤ (Finset.univ : Finset V).card := Finset.card_image_le
      _ = Fintype.card V := Finset.card_univ
  exact_mod_cast h1

/-- **The assembled correction is small.**  Link weights of size `B/|V|²` assemble to a correction
of size at most `4B/|V|`: each triangle is used as a core by at most `|V|` apices, and as an apex
triangle for at most `3|V|` cores. -/
theorem abs_linkCorrection_le (G : SimpleGraph V) [DecidableRel G.Adj]
    {b : V → Finset V → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hbnd : ∀ u t, |b u t| ≤ B / (Fintype.card V : ℝ) ^ 2)
    {T : Finset (EdgeV G)} (hT : T ∈ triangleHypergraphSub G) :
    |linkCorrection G b T| ≤ 4 * B / (Fintype.card V : ℝ) := by
  classical
  obtain ⟨t, ht, rfl⟩ := (mem_triangleHypergraphSub_iff G).mp hT
  have hs : triOf G ((t.powersetCard 2).subtype (· ∈ G.cliqueFinset 2)) = t := triOf_subtype G ht
  rw [linkCorrection, hs]
  have htc : t.card = 3 := ht.card_eq
  have hVpos : (0 : ℝ) < (Fintype.card V : ℝ) := by
    have : 0 < Fintype.card V := by
      have : t.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨x, -⟩ := this
      exact Fintype.card_pos_iff.mpr ⟨x⟩
    exact_mod_cast this
  -- the apex part
  have hapex : |∑ p ∈ t, ∑ t' ∈ (G.cliqueFinset 3).filter (fun t' => t.erase p ⊆ t'), b p t'|
      ≤ 3 * B / (Fintype.card V : ℝ) := by
    have hinner : ∀ p ∈ t,
        |∑ t' ∈ (G.cliqueFinset 3).filter (fun t' => t.erase p ⊆ t'), b p t'|
          ≤ B / (Fintype.card V : ℝ) := by
      intro p hp
      have hq : (t.erase p).card = 2 := by rw [Finset.card_erase_of_mem hp, htc]
      calc |∑ t' ∈ (G.cliqueFinset 3).filter (fun t' => t.erase p ⊆ t'), b p t'|
          ≤ ∑ t' ∈ (G.cliqueFinset 3).filter (fun t' => t.erase p ⊆ t'), |b p t'| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _t' ∈ (G.cliqueFinset 3).filter (fun t' => t.erase p ⊆ t'),
              B / (Fintype.card V : ℝ) ^ 2 :=
            Finset.sum_le_sum (fun t' _ => hbnd p t')
        _ = (((G.cliqueFinset 3).filter (fun t' => t.erase p ⊆ t')).card : ℝ)
              * (B / (Fintype.card V : ℝ) ^ 2) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (Fintype.card V : ℝ) * (B / (Fintype.card V : ℝ) ^ 2) := by
            refine mul_le_mul_of_nonneg_right (card_cliqueFinset3_filter_supset_le G hq) ?_
            positivity
        _ = B / (Fintype.card V : ℝ) := by field_simp
    calc |∑ p ∈ t, ∑ t' ∈ (G.cliqueFinset 3).filter (fun t' => t.erase p ⊆ t'), b p t'|
        ≤ ∑ p ∈ t, |∑ t' ∈ (G.cliqueFinset 3).filter (fun t' => t.erase p ⊆ t'), b p t'| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _p ∈ t, B / (Fintype.card V : ℝ) := Finset.sum_le_sum hinner
      _ = 3 * B / (Fintype.card V : ℝ) := by
          rw [Finset.sum_const, htc, nsmul_eq_mul]; ring
  -- the core part
  have hcore : |∑ u : V, b u t| ≤ B / (Fintype.card V : ℝ) := by
    calc |∑ u : V, b u t| ≤ ∑ u : V, |b u t| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _u : V, B / (Fintype.card V : ℝ) ^ 2 := Finset.sum_le_sum (fun u _ => hbnd u t)
      _ = (Fintype.card V : ℝ) * (B / (Fintype.card V : ℝ) ^ 2) := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
      _ = B / (Fintype.card V : ℝ) := by field_simp
  calc |(∑ p ∈ t, ∑ t' ∈ (G.cliqueFinset 3).filter (fun t' => t.erase p ⊆ t'), b p t')
        - ∑ u : V, b u t|
      ≤ |∑ p ∈ t, ∑ t' ∈ (G.cliqueFinset 3).filter (fun t' => t.erase p ⊆ t'), b p t'|
        + |∑ u : V, b u t| := abs_sub _ _
    _ ≤ 3 * B / (Fintype.card V : ℝ) + B / (Fintype.card V : ℝ) := by
        exact add_le_add hapex hcore
    _ = 4 * B / (Fintype.card V : ℝ) := by ring

/-! ### The local problem -/

/-- **A link routing of the Dross deficiency.**  Link weightings `b u`, of size at most `B/|V|²`,
carried by the triangles inside the link of `u`, whose *vertex degrees* at the two endpoints of each
edge `e` add up to half the deficiency `1 - K·codeg(e)/(|V|-2)` of the base weighting
`K/(|V|-2)`. -/
def IsLinkDeficiencyRouting (G : SimpleGraph V) [DecidableRel G.Adj] (K B : ℝ)
    (b : V → Finset V → ℝ) : Prop :=
  IsLinkCore G b ∧
  (∀ u t, |b u t| ≤ B / (Fintype.card V : ℝ) ^ 2) ∧
  (∀ (e : EdgeV G) (u v : V), u ≠ v → e.val = ({u, v} : Finset V) →
    linkVertexSum G b u v + linkVertexSum G b v u
      = (1 - K * ((commonNbrs G e).card : ℝ) / ((Fintype.card V : ℝ) - 2)) / 2)

/-- **The reduction.**  A link routing assembles into a bounded scaled deficiency correction. -/
theorem isScaledDeficiencyCorrection_of_linkRouting (G : SimpleGraph V) [DecidableRel G.Adj]
    {K B : ℝ} {b : V → Finset V → ℝ} (hB : 0 ≤ B) (hKB : 4 * B ≤ K)
    (hV : 3 ≤ Fintype.card V) (h : IsLinkDeficiencyRouting G K B b) :
    IsScaledDeficiencyCorrection G K (linkCorrection G b) := by
  obtain ⟨hcore, hbnd, hdem⟩ := h
  have hV3 : (3 : ℝ) ≤ (Fintype.card V : ℝ) := by exact_mod_cast hV
  have hVpos : (0 : ℝ) < (Fintype.card V : ℝ) := by linarith
  have hV2 : (0 : ℝ) < (Fintype.card V : ℝ) - 2 := by linarith
  constructor
  · intro T hT
    refine le_trans (abs_linkCorrection_le G hB hbnd hT) ?_
    rw [div_le_div_iff₀ hVpos hV2]
    nlinarith
  · intro e
    obtain ⟨v₁, v₂, hne, -, hval⟩ := exists_pair_of_edgeV G e
    rw [sum_linkCorrection_eq G hcore e hne hval, hdem e v₁ v₂ hne hval]
    ring

/-! ### The global statement and the chain -/

/-- **The Dross link-routing statement.**  At the Dross density the deficiency of the uniform base
weighting `K/(|V|-2)` can be routed through the links: for every vertex `u` a weighting of the
triangles of the link of `u`, of size `O(1/|V|²)`, whose vertex degrees prescribe half the
deficiency at each edge. -/
def DrossLinkRouting : Prop :=
  ∃ K B : ℝ, 0 < K ∧ 0 ≤ B ∧ 4 * B ≤ K ∧
    ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      9 * Fintype.card V ≤ 10 * G.minDegree →
      ∃ b : V → Finset V → ℝ, IsLinkDeficiencyRouting G K B b

/-- **Link routing gives the scaled correction.** -/
theorem drossScaledCorrection_of_linkRouting (h : DrossLinkRouting) : DrossScaledCorrection := by
  obtain ⟨K, B, hK, hB, hKB, hmain⟩ := h
  refine ⟨K, hK, ?_⟩
  intro V _ _ G _ hdense
  by_cases hne : Nonempty V
  · obtain ⟨v⟩ := hne
    have hten : 10 ≤ Fintype.card V := ten_le_card_of_dense G hdense v
    obtain ⟨b, hb⟩ := hmain G hdense
    exact ⟨linkCorrection G b,
      isScaledDeficiencyCorrection_of_linkRouting G hB hKB (by omega) hb⟩
  · exact exists_scaledCorrection_of_not_nonempty G hne K

/-- **Link routing gives the quantitatively spread Dross theorem.** -/
theorem drossFractionalQuantSpread_of_linkRouting (h : DrossLinkRouting) :
    DrossFractionalQuantSpread :=
  drossFractionalQuantSpread_iff_scaledCorrection.mpr (drossScaledCorrection_of_linkRouting h)

/-- **Link routing gives the `o(|V|²)` residual.** -/
theorem denseGlobalSmallLeftover_of_linkRouting (h : DrossLinkRouting) :
    DenseGlobalSmallLeftover :=
  denseGlobalSmallLeftover_of_drossSpread
    (drossFractionalSpread_of_quant (drossFractionalQuantSpread_of_linkRouting h))

/-- **Link routing gives the full `1/10` per-vertex nibble bound.** -/
theorem denseTriangleNibbleDeg_of_linkRouting (h : DrossLinkRouting) {β : ℝ} (hβ : 1 / 10 < β) :
    ∃ n₀ : ℕ, ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      n₀ ≤ Fintype.card V → 9 * Fintype.card V ≤ 10 * G.minDegree →
      ∃ M : Finset (Finset (EdgeV G)), IsMatching (triangleHypergraphSub G) M ∧
        ∀ v : V, ((uncoveredAt G M v).card : ℝ) ≤ β * (Fintype.card V : ℝ) :=
  denseTriangleNibbleDeg_of_drossSpread
    (drossFractionalSpread_of_quant (drossFractionalQuantSpread_of_linkRouting h)) hβ

/-! ### Non-vacuity -/

/-- **Non-vacuity.**  On the complete graph the uniform weighting `1/(|V|-2)` is already exact, so
the zero link routing works with `K = 1`. -/
theorem isLinkDeficiencyRouting_zero_top (hV : 3 ≤ Fintype.card V) :
    IsLinkDeficiencyRouting (⊤ : SimpleGraph V) 1 0 (fun _ _ => (0 : ℝ)) := by
  classical
  have h3 : (3 : ℝ) ≤ (Fintype.card V : ℝ) := by exact_mod_cast hV
  have h2 : (0 : ℝ) < (Fintype.card V : ℝ) - 2 := by linarith
  refine ⟨fun u t ht => absurd rfl ht, fun u t => by simp, fun e u v huv hval => ?_⟩
  have hcod : ((commonNbrs (⊤ : SimpleGraph V) e).card : ℝ) = (Fintype.card V : ℝ) - 2 := by
    have h := card_triangles_through_edge_top e
    rw [card_trianglesThrough_eq_commonNbrs] at h
    have hc : ((commonNbrs (⊤ : SimpleGraph V) e).card : ℝ) = ((Fintype.card V - 2 : ℕ) : ℝ) := by
      exact_mod_cast congrArg (fun k : ℕ => (k : ℝ)) h
    rw [hc, Nat.cast_sub (by omega)]
    norm_num
  simp only [linkVertexSum, Finset.sum_const_zero, add_zero, hcod, one_mul]
  rw [div_self (ne_of_gt h2)]
  norm_num

end Nibble
