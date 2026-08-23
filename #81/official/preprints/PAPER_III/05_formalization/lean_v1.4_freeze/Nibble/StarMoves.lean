/-
# Nibble — the two star-augmenting moves

Two exchange moves on a triangle packing `M`, both *gaining* two uncovered star edges at a vertex
`v` while touching only vertices whose own uncovered stars are small (`≤ |uncoveredAt v| / 64`):

* `Nibble.exchange_short` — `v` has two uncovered star neighbours `a₀, a₁` with `a₀a₁ ∈ E(G)`:
  delete the packing triangle covering `a₀a₁` (if any) and insert `{v, a₀, a₁}`;
* `Nibble.exchange_long` — `v` has two uncovered star neighbours `a₀, a₁` and a packing triangle
  `{v, x, y}` with `a₀x, ya₁ ∈ E(G)`: delete `{v, x, y}` together with the packing triangles
  covering `a₀x` and `ya₁` (if any) and insert `{v, a₀, x}` and `{v, y, a₁}`.  This is the
  length-three augmenting path in the link of `v`.

Both conclude that the potential `Nibble.uncoveredPot` strictly decreases, which is what
potential-minimality forbids.

Sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.StarExchange

open Finset SimpleGraph Hypergraph Nibble.YusterE

namespace Nibble

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ### The covering triangle of an edge -/

/-- The members of `M` covering the edge `E` — at most one. -/
def covM (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset (EdgeV G)))
    (E : EdgeV G) : Finset (Finset (EdgeV G)) :=
  M.filter (fun T => E ∈ T)

theorem covM_subset (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset (EdgeV G)))
    (E : EdgeV G) : covM G M E ⊆ M := Finset.filter_subset _ _

theorem mem_covM (G : SimpleGraph V) [DecidableRel G.Adj] {M : Finset (Finset (EdgeV G))}
    {E : EdgeV G} {T : Finset (EdgeV G)} : T ∈ covM G M E ↔ T ∈ M ∧ E ∈ T := by
  simp [covM]

/-- Two members of a matching sharing an edge are equal. -/
theorem eq_of_mem_of_mem (G : SimpleGraph V) [DecidableRel G.Adj]
    {M : Finset (Finset (EdgeV G))} (hM : IsMatching (triangleHypergraphSub G) M)
    {T T' : Finset (EdgeV G)} (hT : T ∈ M) (hT' : T' ∈ M) {E : EdgeV G} (hE : E ∈ T)
    (hE' : E ∈ T') : T = T' := by
  by_contra hne
  exact Finset.disjoint_left.mp (hM.disjoint T hT T' hT' hne) hE hE'

theorem card_covM_le_one (G : SimpleGraph V) [DecidableRel G.Adj]
    {M : Finset (Finset (EdgeV G))} (hM : IsMatching (triangleHypergraphSub G) M)
    (E : EdgeV G) : (covM G M E).card ≤ 1 := by
  refine Finset.card_le_one.mpr (fun T hT T' hT' => ?_)
  rw [mem_covM] at hT hT'
  exact eq_of_mem_of_mem G hM hT.1 hT'.1 hT.2 hT'.2

/-- An edge is uncovered once its covering triangles have been deleted. -/
theorem uncE_sdiff_covM (G : SimpleGraph V) [DecidableRel G.Adj]
    {M R : Finset (Finset (EdgeV G))} {E : EdgeV G} (hsub : covM G M E ⊆ R) :
    UncE G (M \ R) E := by
  intro T hT hET
  rw [Finset.mem_sdiff] at hT
  exact hT.2 (hsub (mem_covM G |>.mpr ⟨hT.1, hET⟩))

/-! ### The vertex set of an explicit triangle -/

theorem triOf_triE (G : SimpleGraph V) [DecidableRel G.Adj] {x y z : V} (hxy : G.Adj x y)
    (hyz : G.Adj y z) (hxz : G.Adj x z) :
    triOf G (triE G hxy hyz hxz) = ({x, y, z} : Finset V) := by
  classical
  ext u
  constructor
  · intro hu
    rw [triOf, Finset.mem_biUnion] at hu
    obtain ⟨E, hE, huE⟩ := hu
    rw [mem_triE] at hE
    rcases hE with rfl | rfl | rfl <;> rw [mem_edgeE_val] at huE <;>
      rcases huE with rfl | rfl <;> simp
  · intro hu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rw [triOf, Finset.mem_biUnion]
    rcases hu with rfl | rfl | rfl
    · exact ⟨edgeE G hxy, by rw [mem_triE]; exact Or.inl rfl, by rw [mem_edgeE_val]; exact Or.inl rfl⟩
    · exact ⟨edgeE G hxy, by rw [mem_triE]; exact Or.inl rfl, by rw [mem_edgeE_val]; exact Or.inr rfl⟩
    · exact ⟨edgeE G hyz, by rw [mem_triE]; exact Or.inr (Or.inl rfl), by rw [mem_edgeE_val]; exact Or.inr rfl⟩

theorem val_subset_triOf (G : SimpleGraph V) [DecidableRel G.Adj] {T : Finset (EdgeV G)}
    {E : EdgeV G} (hE : E ∈ T) : E.val ⊆ triOf G T :=
  Finset.subset_biUnion_of_mem (fun E : EdgeV G => E.val) hE

/-! ### Good edges -/

/-- The edge `E` is **good at level `dd`**: every packing triangle covering it has all its vertices
either on `E` itself or with an uncovered star of size at most `dd / 64`. -/
def GoodEdgeAt (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset (Finset (EdgeV G)))
    (dd : ℕ) (E : EdgeV G) : Prop :=
  ∀ T ∈ M, E ∈ T → ∀ z ∈ triOf G T, z ∈ E.val ∨ 64 * unDeg G M z ≤ dd

/-! ### The short move -/

/-- **The short move.**  If `v` has two uncovered star neighbours `a₀ ≠ a₁` spanning an edge of `G`
which is good, and both `a₀`, `a₁` have small uncovered stars, then the packing can be improved:
delete the triangle covering `a₀a₁` and insert `{v, a₀, a₁}`. -/
theorem exchange_short (G : SimpleGraph V) [DecidableRel G.Adj]
    {M : Finset (Finset (EdgeV G))} (hM : IsMatching (triangleHypergraphSub G) M)
    {v a₀ a₁ : V} (hva₀ : G.Adj v a₀) (hva₁ : G.Adj v a₁) (ha : G.Adj a₀ a₁)
    (hu0 : UncE G M (edgeE G hva₀)) (hu1 : UncE G M (edgeE G hva₁))
    (hg : GoodEdgeAt G M (unDeg G M v) (edgeE G ha))
    (hca₀ : 64 * unDeg G M a₀ ≤ unDeg G M v) (hca₁ : 64 * unDeg G M a₁ ≤ unDeg G M v)
    (hbig : 4000 ≤ unDeg G M v) :
    ∃ M' : Finset (Finset (EdgeV G)), IsMatching (triangleHypergraphSub G) M' ∧
      uncoveredPot G M' < uncoveredPot G M := by
  classical
  have hva : v ≠ a₀ := hva₀.ne
  have hvb : v ≠ a₁ := hva₁.ne
  have hab : a₀ ≠ a₁ := ha.ne
  set R : Finset (Finset (EdgeV G)) := covM G M (edgeE G ha) with hRdef
  have hRM : R ⊆ M := covM_subset G M _
  have hRcard : R.card ≤ 1 := card_covM_le_one G hM _
  set P : Finset (EdgeV G) := triE G hva₀ ha hva₁ with hPdef
  have hPH : P ∈ triangleHypergraphSub G := triE_mem_hypergraph G hva₀ ha hva₁
  -- no triangle of `R` has an edge at `v`
  have hnov : ∀ T ∈ R, ∀ E ∈ T, v ∉ E.val := by
    intro T hT E hE hv
    rw [hRdef, mem_covM] at hT
    obtain ⟨z, hbz, haz, hza, hzb, hTeq⟩ :=
      exists_third_vertex G ha (hM.subset hT.1) hT.2
    have hvmem : v ∈ triOf G T := val_subset_triOf G hE hv
    rw [hTeq, triOf_triE] at hvmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hvmem
    rcases hvmem with rfl | rfl | rfl
    · exact hva rfl
    · exact hvb rfl
    · -- `v` is the third vertex: then `T` covers the uncovered edge `v a₀`
      have hmem : edgeE G haz ∈ T := by rw [hTeq, mem_triE]; exact Or.inr (Or.inr rfl)
      have heq : edgeE G haz = edgeE G hva₀ := by
        rw [edgeE_eq_iff]; exact Finset.pair_comm a₀ v
      exact hu0 T hT.1 (heq ▸ hmem)
  -- the new matching
  have hfree : ∀ E ∈ P, UncE G (M \ R) E := by
    intro E hE
    rw [hPdef, mem_triE] at hE
    rcases hE with rfl | rfl | rfl
    · exact fun T hT hmem => hu0 T (Finset.mem_sdiff.mp hT).1 hmem
    · exact uncE_sdiff_covM G (Finset.Subset.refl _)
    · exact fun T hT hmem => hu1 T (Finset.mem_sdiff.mp hT).1 hmem
  set M' : Finset (Finset (EdgeV G)) := insert P (M \ R) with hM'def
  have hM'match : IsMatching (triangleHypergraphSub G) M' :=
    isMatching_insert G (isMatching_sdiff G hM R) hPH hfree
  refine ⟨M', hM'match, ?_⟩
  -- the affected vertex set
  set S : Finset V := ((R.biUnion (fun T => triOf G T)) ∪ ({a₀, a₁} : Finset V)).erase v with hSdef
  have hvS : v ∉ S := Finset.notMem_erase _ _
  have hScard : S.card ≤ 13 := by
    have h1 : (R.biUnion (fun T => triOf G T)).card ≤ ∑ T ∈ R, (triOf G T).card :=
      Finset.card_biUnion_le
    have h2 : ∀ T ∈ R, (triOf G T).card = 3 := by
      intro T hT
      exact (triOf_isNClique G (hM.subset (hRM hT))).card_eq
    have h3 : ∑ T ∈ R, (triOf G T).card = 3 * R.card := by
      rw [Finset.sum_congr rfl h2, Finset.sum_const, smul_eq_mul, mul_comm]
    have h4 : ({a₀, a₁} : Finset V).card ≤ 2 := Finset.card_insert_le _ _ |>.trans (by simp)
    have h5 := Finset.card_union_le (R.biUnion (fun T => triOf G T)) ({a₀, a₁} : Finset V)
    have h6 : S.card ≤ ((R.biUnion (fun T => triOf G T)) ∪ ({a₀, a₁} : Finset V)).card := by
      rw [hSdef]; exact Finset.card_erase_le
    omega
  -- everything in `S` is cheap
  have hcheap : ∀ u ∈ S, 64 * unDeg G M u ≤ unDeg G M v := by
    intro u hu
    rw [hSdef, Finset.mem_erase, Finset.mem_union, Finset.mem_biUnion] at hu
    obtain ⟨huv, hcase⟩ := hu
    rcases hcase with ⟨T, hT, huT⟩ | hu2
    · rw [hRdef, mem_covM] at hT
      rcases hg T hT.1 hT.2 u huT with hmem | hch
      · rw [edgeE_val] at hmem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
        rcases hmem with rfl | rfl
        · exact hca₀
        · exact hca₁
      · exact hch
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hu2
      rcases hu2 with rfl | rfl
      · exact hca₀
      · exact hca₁
  -- the star at `v` gains two
  have hPfilterv : (P.filter (fun E => v ∈ E.val)).card = 2 := by
    have hne : edgeE G hva₀ ≠ edgeE G hva₁ :=
      edgeE_ne_of_notMem' G hva₀ hva₁ (by simp [Ne.symm hva, hab])
    have h1 : P.filter (fun E => v ∈ E.val)
        = ({edgeE G hva₀, edgeE G hva₁} : Finset (EdgeV G)) := by
      ext E
      simp only [hPdef, Finset.mem_filter, mem_triE, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨(rfl | rfl | rfl), hv⟩
        · exact Or.inl rfl
        · rw [edgeE_val] at hv
          simp only [Finset.mem_insert, Finset.mem_singleton] at hv
          rcases hv with rfl | rfl
          · exact absurd rfl hva
          · exact absurd rfl hvb
        · exact Or.inr rfl
      · rintro (rfl | rfl)
        · exact ⟨Or.inl rfl, by simp⟩
        · exact ⟨Or.inr (Or.inr rfl), by simp⟩
    rw [h1, Finset.card_insert_of_notMem (by simpa using hne), Finset.card_singleton]
  have hvstep : unDeg G M' v + 2 = unDeg G M v := by
    have h1 := unDeg_insert_add G (M \ R) hfree v
    have h2 : unDeg G (M \ R) v = unDeg G M v := unDeg_sdiff_eq G hM hRM hnov
    rw [hPfilterv] at h1
    rw [hM'def]
    omega
  -- outside `S ∪ {v}` nothing changes
  have hPval : ∀ E ∈ P, E.val ⊆ ({v, a₀, a₁} : Finset V) := by
    intro E hE
    have := val_subset_triOf G hE
    rwa [hPdef, triOf_triE] at this
  have hout : ∀ u : V, u ≠ v → u ∉ S → unDeg G M' u = unDeg G M u := by
    intro u huv huS
    have hnoR : ∀ T ∈ R, ∀ E ∈ T, u ∉ E.val := by
      intro T hT E hE hu
      refine huS ?_
      rw [hSdef, Finset.mem_erase]
      exact ⟨huv, Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨T, hT, val_subset_triOf G hE hu⟩)⟩
    have h2 : unDeg G (M \ R) u = unDeg G M u := unDeg_sdiff_eq G hM hRM hnoR
    have h1 := unDeg_insert_add G (M \ R) hfree u
    have h3 : (P.filter (fun E => u ∈ E.val)).card = 0 := by
      rw [Finset.card_eq_zero]
      refine Finset.filter_eq_empty_iff.mpr (fun E hE hu => ?_)
      have := hPval E hE hu
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      refine huS ?_
      rw [hSdef, Finset.mem_erase]
      rcases this with rfl | rfl | rfl
      · exact absurd rfl huv
      · exact ⟨huv, Finset.mem_union_right _ (by simp)⟩
      · exact ⟨huv, Finset.mem_union_right _ (by simp)⟩
    rw [hM'def]
    omega
  -- inside `S` the loss is bounded
  have hin : ∀ u ∈ S, unDeg G M' u ≤ unDeg G M u + 9 := by
    intro u _
    have h1 := unDeg_insert_add G (M \ R) hfree u
    have h2 := unDeg_sdiff_le G hM hRM u
    rw [hM'def]
    omega
  exact pot_lt_of_exchange G hvS hScard hvstep hout hin hcheap hbig

/-! ### The long move -/

/-- **The long move.**  If `v` has two uncovered star neighbours `a₀ ≠ a₁`, `{v, x, y}` is a
packing triangle and `a₀x`, `ya₁` are good edges of `G`, and all four of `a₀, a₁, x, y` have small
uncovered stars, then the packing can be improved: delete `{v, x, y}` and the triangles covering
`a₀x` and `ya₁`, and insert `{v, a₀, x}` and `{v, y, a₁}`. -/
theorem exchange_long (G : SimpleGraph V) [DecidableRel G.Adj]
    {M : Finset (Finset (EdgeV G))} (hM : IsMatching (triangleHypergraphSub G) M)
    {v a₀ a₁ x y : V}
    (hva₀ : G.Adj v a₀) (hva₁ : G.Adj v a₁) (hvx : G.Adj v x) (hvy : G.Adj v y)
    (hax : G.Adj a₀ x) (hya : G.Adj y a₁) (hxy : G.Adj x y)
    (ha₀a₁ : a₀ ≠ a₁) (ha₀y : a₀ ≠ y) (ha₁x : a₁ ≠ x)
    (hu0 : UncE G M (edgeE G hva₀)) (hu1 : UncE G M (edgeE G hva₁))
    (hT0 : triE G hvx hxy hvy ∈ M)
    (hg1 : GoodEdgeAt G M (unDeg G M v) (edgeE G hax))
    (hg2 : GoodEdgeAt G M (unDeg G M v) (edgeE G hya))
    (hca₀ : 64 * unDeg G M a₀ ≤ unDeg G M v) (hca₁ : 64 * unDeg G M a₁ ≤ unDeg G M v)
    (hcx : 64 * unDeg G M x ≤ unDeg G M v) (hcy : 64 * unDeg G M y ≤ unDeg G M v)
    (hbig : 4000 ≤ unDeg G M v) :
    ∃ M' : Finset (Finset (EdgeV G)), IsMatching (triangleHypergraphSub G) M' ∧
      uncoveredPot G M' < uncoveredPot G M := by
  classical
  have hva : v ≠ a₀ := hva₀.ne
  have hvb : v ≠ a₁ := hva₁.ne
  have hvxne : v ≠ x := hvx.ne
  have hvyne : v ≠ y := hvy.ne
  have hxyne : x ≠ y := hxy.ne
  have ha₀x : a₀ ≠ x := hax.ne
  have ha₁y : a₁ ≠ y := (hya.ne).symm
  set T₀ : Finset (EdgeV G) := triE G hvx hxy hvy with hT₀def
  set R : Finset (Finset (EdgeV G)) :=
    covM G M (edgeE G hvx) ∪ covM G M (edgeE G hax) ∪ covM G M (edgeE G hya) with hRdef
  have hRM : R ⊆ M := by
    rw [hRdef]
    exact Finset.union_subset (Finset.union_subset (covM_subset G M _) (covM_subset G M _))
      (covM_subset G M _)
  have hRcard : R.card ≤ 3 := by
    have h1 := Finset.card_union_le (covM G M (edgeE G hvx) ∪ covM G M (edgeE G hax))
      (covM G M (edgeE G hya))
    have h2 := Finset.card_union_le (covM G M (edgeE G hvx)) (covM G M (edgeE G hax))
    have h3 := card_covM_le_one G hM (edgeE G hvx)
    have h4 := card_covM_le_one G hM (edgeE G hax)
    have h5 := card_covM_le_one G hM (edgeE G hya)
    rw [hRdef]
    omega
  have hT₀R : T₀ ∈ R := by
    rw [hRdef]
    refine Finset.mem_union_left _ (Finset.mem_union_left _ ?_)
    exact (mem_covM G).mpr ⟨hT0, by rw [hT₀def, mem_triE]; exact Or.inl rfl⟩
  -- the four edges are free after the deletion
  have hfree_vx : UncE G (M \ R) (edgeE G hvx) := by
    refine uncE_sdiff_covM G ?_
    rw [hRdef]
    exact (Finset.subset_union_left).trans Finset.subset_union_left
  have hfree_ax : UncE G (M \ R) (edgeE G hax) := by
    refine uncE_sdiff_covM G ?_
    rw [hRdef]
    exact (Finset.subset_union_right).trans Finset.subset_union_left
  have hfree_ya : UncE G (M \ R) (edgeE G hya) := by
    refine uncE_sdiff_covM G ?_
    rw [hRdef]
    exact Finset.subset_union_right
  have hfree_vy : UncE G (M \ R) (edgeE G hvy) := by
    intro T hT hmem
    rw [Finset.mem_sdiff] at hT
    have hET₀ : edgeE G hvy ∈ T₀ := by rw [hT₀def, mem_triE]; exact Or.inr (Or.inr rfl)
    have := eq_of_mem_of_mem G hM hT.1 hT0 hmem hET₀
    exact hT.2 (this ▸ hT₀R)
  -- the two new triangles
  set P₂ : Finset (EdgeV G) := triE G hvy hya hva₁ with hP₂def
  set P₁ : Finset (EdgeV G) := triE G hva₀ hax hvx with hP₁def
  have hP₂H : P₂ ∈ triangleHypergraphSub G := triE_mem_hypergraph G hvy hya hva₁
  have hP₁H : P₁ ∈ triangleHypergraphSub G := triE_mem_hypergraph G hva₀ hax hvx
  have hfree₂ : ∀ E ∈ P₂, UncE G (M \ R) E := by
    intro E hE
    rw [hP₂def, mem_triE] at hE
    rcases hE with rfl | rfl | rfl
    · exact hfree_vy
    · exact hfree_ya
    · exact fun T hT hmem => hu1 T (Finset.mem_sdiff.mp hT).1 hmem
  set M₂ : Finset (Finset (EdgeV G)) := insert P₂ (M \ R) with hM₂def
  have hM₂match : IsMatching (triangleHypergraphSub G) M₂ :=
    isMatching_insert G (isMatching_sdiff G hM R) hP₂H hfree₂
  -- the edges of `P₁` are not edges of `P₂`
  have hP₁P₂ : ∀ E ∈ P₁, E ∉ P₂ := by
    intro E hE hE2
    rw [hP₁def, mem_triE] at hE
    rw [hP₂def, mem_triE] at hE2
    rcases hE with rfl | rfl | rfl <;> rcases hE2 with h | h | h <;>
      · rw [edgeE_eq_iff] at h
        have h1 : a₀ ∈ ({v, a₀} : Finset V) := by simp
        have h2 : x ∈ ({a₀, x} : Finset V) := by simp
        have h3 : x ∈ ({v, x} : Finset V) := by simp
        simp only [Finset.ext_iff, Finset.mem_insert, Finset.mem_singleton] at h
        first
          | (have := (h a₀).mp (by simp)
             rcases this with rfl | rfl <;> simp_all)
          | (have := (h x).mp (by simp)
             rcases this with rfl | rfl <;> simp_all)
  have hfree₁ : ∀ E ∈ P₁, UncE G M₂ E := by
    intro E hE T hT hmem
    rw [hM₂def, Finset.mem_insert] at hT
    rcases hT with rfl | hT
    · exact hP₁P₂ E hE hmem
    · rw [hP₁def, mem_triE] at hE
      rcases hE with rfl | rfl | rfl
      · exact hu0 T (Finset.mem_sdiff.mp hT).1 hmem
      · exact hfree_ax T hT hmem
      · exact hfree_vx T hT hmem
  set M' : Finset (Finset (EdgeV G)) := insert P₁ M₂ with hM'def
  have hM'match : IsMatching (triangleHypergraphSub G) M' :=
    isMatching_insert G hM₂match hP₁H hfree₁
  refine ⟨M', hM'match, ?_⟩
  -- the affected vertex set
  set S : Finset V :=
    ((R.biUnion (fun T => triOf G T)) ∪ ({a₀, a₁, x, y} : Finset V)).erase v with hSdef
  have hvS : v ∉ S := Finset.notMem_erase _ _
  have hScard : S.card ≤ 13 := by
    have h1 : (R.biUnion (fun T => triOf G T)).card ≤ ∑ T ∈ R, (triOf G T).card :=
      Finset.card_biUnion_le
    have h2 : ∀ T ∈ R, (triOf G T).card = 3 := by
      intro T hT
      exact (triOf_isNClique G (hM.subset (hRM hT))).card_eq
    have h3 : ∑ T ∈ R, (triOf G T).card = 3 * R.card := by
      rw [Finset.sum_congr rfl h2, Finset.sum_const, smul_eq_mul, mul_comm]
    have h4 : ({a₀, a₁, x, y} : Finset V).card ≤ 4 := by
      refine le_trans (Finset.card_insert_le _ _) ?_
      have := Finset.card_insert_le a₁ ({x, y} : Finset V)
      have h5 : ({x, y} : Finset V).card ≤ 2 :=
        le_trans (Finset.card_insert_le _ _) (by simp)
      omega
    have h5 := Finset.card_union_le (R.biUnion (fun T => triOf G T)) ({a₀, a₁, x, y} : Finset V)
    have h6 : S.card ≤ ((R.biUnion (fun T => triOf G T)) ∪ ({a₀, a₁, x, y} : Finset V)).card := by
      rw [hSdef]; exact Finset.card_erase_le
    omega
  -- every vertex of `S` is cheap
  have hcheap : ∀ u ∈ S, 64 * unDeg G M u ≤ unDeg G M v := by
    intro u hu
    rw [hSdef, Finset.mem_erase, Finset.mem_union, Finset.mem_biUnion] at hu
    obtain ⟨huv, hcase⟩ := hu
    rcases hcase with ⟨T, hT, huT⟩ | hu2
    · rw [hRdef, Finset.mem_union, Finset.mem_union] at hT
      rcases hT with (hT | hT) | hT
      · -- `T` covers `vx`, so `T = T₀` and `u ∈ {v, x, y}`
        rw [mem_covM] at hT
        have hTeq : T = T₀ :=
          eq_of_mem_of_mem G hM hT.1 hT0 hT.2 (by rw [hT₀def, mem_triE]; exact Or.inl rfl)
        rw [hTeq, hT₀def, triOf_triE] at huT
        simp only [Finset.mem_insert, Finset.mem_singleton] at huT
        rcases huT with rfl | rfl | rfl
        · exact absurd rfl huv
        · exact hcx
        · exact hcy
      · rw [mem_covM] at hT
        rcases hg1 T hT.1 hT.2 u huT with hmem | hch
        · rw [edgeE_val] at hmem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
          rcases hmem with rfl | rfl
          · exact hca₀
          · exact hcx
        · exact hch
      · rw [mem_covM] at hT
        rcases hg2 T hT.1 hT.2 u huT with hmem | hch
        · rw [edgeE_val] at hmem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
          rcases hmem with rfl | rfl
          · exact hcy
          · exact hca₁
        · exact hch
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hu2
      rcases hu2 with rfl | rfl | rfl | rfl
      · exact hca₀
      · exact hca₁
      · exact hcx
      · exact hcy
  -- the edges of `⋃ R` at `v` are exactly `vx` and `vy`
  have hRv : (R.biUnion id).filter (fun E => v ∈ E.val)
      = ({edgeE G hvx, edgeE G hvy} : Finset (EdgeV G)) := by
    ext E
    simp only [Finset.mem_filter, Finset.mem_biUnion, id_eq, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro ⟨⟨T, hT, hET⟩, hvE⟩
      rw [hRdef, Finset.mem_union, Finset.mem_union] at hT
      rcases hT with (hT | hT) | hT
      · rw [mem_covM] at hT
        have hTeq : T = T₀ :=
          eq_of_mem_of_mem G hM hT.1 hT0 hT.2 (by rw [hT₀def, mem_triE]; exact Or.inl rfl)
        rw [hTeq, hT₀def, mem_triE] at hET
        rcases hET with rfl | rfl | rfl
        · exact Or.inl rfl
        · rw [edgeE_val] at hvE
          simp only [Finset.mem_insert, Finset.mem_singleton] at hvE
          rcases hvE with rfl | rfl
          · exact absurd rfl hvxne
          · exact absurd rfl hvyne
        · exact Or.inr rfl
      · -- `T` covers `a₀x`; it cannot have an edge at `v`
        exfalso
        rw [mem_covM] at hT
        obtain ⟨z, hbz, haz, hza, hzb, hTeq⟩ :=
          exists_third_vertex G hax (hM.subset hT.1) hT.2
        have hvmem : v ∈ triOf G T := val_subset_triOf G hET hvE
        rw [hTeq, triOf_triE] at hvmem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hvmem
        rcases hvmem with rfl | rfl | rfl
        · exact hva rfl
        · exact hvxne rfl
        · have hmem : edgeE G haz ∈ T := by rw [hTeq, mem_triE]; exact Or.inr (Or.inr rfl)
          have heq : edgeE G haz = edgeE G hva₀ := by
            rw [edgeE_eq_iff]; exact Finset.pair_comm a₀ v
          exact hu0 T hT.1 (heq ▸ hmem)
      · exfalso
        rw [mem_covM] at hT
        obtain ⟨z, hbz, haz, hza, hzb, hTeq⟩ :=
          exists_third_vertex G hya (hM.subset hT.1) hT.2
        have hvmem : v ∈ triOf G T := val_subset_triOf G hET hvE
        rw [hTeq, triOf_triE] at hvmem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hvmem
        rcases hvmem with rfl | rfl | rfl
        · exact hvyne rfl
        · exact hvb rfl
        · have hmem : edgeE G hbz ∈ T := by rw [hTeq, mem_triE]; exact Or.inr (Or.inl rfl)
          have heq : edgeE G hbz = edgeE G hva₁ := by
            rw [edgeE_eq_iff]; exact Finset.pair_comm a₁ v
          exact hu1 T hT.1 (heq ▸ hmem)
    · rintro (rfl | rfl)
      · exact ⟨⟨T₀, hT₀R, by rw [hT₀def, mem_triE]; exact Or.inl rfl⟩, by simp⟩
      · exact ⟨⟨T₀, hT₀R, by rw [hT₀def, mem_triE]; exact Or.inr (Or.inr rfl)⟩, by simp⟩
  -- the star at `v`
  have hP₂v : (P₂.filter (fun E => v ∈ E.val)).card = 2 := by
    have hne : edgeE G hvy ≠ edgeE G hva₁ :=
      edgeE_ne_of_notMem' G hvy hva₁ (by simp [Ne.symm hvyne, Ne.symm ha₁y])
    have h1 : P₂.filter (fun E => v ∈ E.val)
        = ({edgeE G hvy, edgeE G hva₁} : Finset (EdgeV G)) := by
      ext E
      simp only [hP₂def, Finset.mem_filter, mem_triE, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨(rfl | rfl | rfl), hv⟩
        · exact Or.inl rfl
        · rw [edgeE_val] at hv
          simp only [Finset.mem_insert, Finset.mem_singleton] at hv
          rcases hv with rfl | rfl
          · exact absurd rfl hvyne
          · exact absurd rfl hvb
        · exact Or.inr rfl
      · rintro (rfl | rfl)
        · exact ⟨Or.inl rfl, by simp⟩
        · exact ⟨Or.inr (Or.inr rfl), by simp⟩
    rw [h1, Finset.card_insert_of_notMem (by simpa using hne), Finset.card_singleton]
  have hP₁v : (P₁.filter (fun E => v ∈ E.val)).card = 2 := by
    have hne : edgeE G hva₀ ≠ edgeE G hvx :=
      edgeE_ne_of_notMem' G hva₀ hvx (by simp [Ne.symm hva, ha₀x])
    have h1 : P₁.filter (fun E => v ∈ E.val)
        = ({edgeE G hva₀, edgeE G hvx} : Finset (EdgeV G)) := by
      ext E
      simp only [hP₁def, Finset.mem_filter, mem_triE, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨(rfl | rfl | rfl), hv⟩
        · exact Or.inl rfl
        · rw [edgeE_val] at hv
          simp only [Finset.mem_insert, Finset.mem_singleton] at hv
          rcases hv with rfl | rfl
          · exact absurd rfl hva
          · exact absurd rfl hvxne
        · exact Or.inr rfl
      · rintro (rfl | rfl)
        · exact ⟨Or.inl rfl, by simp⟩
        · exact ⟨Or.inr (Or.inr rfl), by simp⟩
    rw [h1, Finset.card_insert_of_notMem (by simpa using hne), Finset.card_singleton]
  have hvstep : unDeg G M' v + 2 = unDeg G M v := by
    have h0 : unDeg G (M \ R) v = unDeg G M v + 2 := by
      rw [unDeg_sdiff G hM hRM v, hRv]
      have hne : edgeE G hvx ≠ edgeE G hvy :=
        edgeE_ne_of_notMem' G hvx hvy (by simp [Ne.symm hvxne, hxyne])
      rw [Finset.card_insert_of_notMem (by simpa using hne), Finset.card_singleton]
    have h1 := unDeg_insert_add G (M \ R) hfree₂ v
    have h2 := unDeg_insert_add G M₂ hfree₁ v
    rw [hP₂v] at h1
    rw [hP₁v] at h2
    rw [← hM₂def] at h1
    rw [← hM'def] at h2
    omega
  -- outside `S ∪ {v}` nothing changes
  have hP₁val : ∀ E ∈ P₁, E.val ⊆ ({v, a₀, x} : Finset V) := by
    intro E hE
    have := val_subset_triOf G hE
    rwa [hP₁def, triOf_triE] at this
  have hP₂val : ∀ E ∈ P₂, E.val ⊆ ({v, y, a₁} : Finset V) := by
    intro E hE
    have := val_subset_triOf G hE
    rwa [hP₂def, triOf_triE] at this
  have hout : ∀ u : V, u ≠ v → u ∉ S → unDeg G M' u = unDeg G M u := by
    intro u huv huS
    have hmemS : ∀ w : V, w ≠ v → (w = a₀ ∨ w = a₁ ∨ w = x ∨ w = y) → w ∈ S := by
      intro w hwv hw
      rw [hSdef, Finset.mem_erase]
      refine ⟨hwv, Finset.mem_union_right _ ?_⟩
      simp only [Finset.mem_insert, Finset.mem_singleton]
      exact hw
    have hnoR : ∀ T ∈ R, ∀ E ∈ T, u ∉ E.val := by
      intro T hT E hE hu
      refine huS ?_
      rw [hSdef, Finset.mem_erase]
      exact ⟨huv, Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨T, hT, val_subset_triOf G hE hu⟩)⟩
    have h2 : unDeg G (M \ R) u = unDeg G M u := unDeg_sdiff_eq G hM hRM hnoR
    have h1 := unDeg_insert_add G (M \ R) hfree₂ u
    have h3 := unDeg_insert_add G M₂ hfree₁ u
    have hz2 : (P₂.filter (fun E => u ∈ E.val)).card = 0 := by
      rw [Finset.card_eq_zero]
      refine Finset.filter_eq_empty_iff.mpr (fun E hE hu => ?_)
      have := hP₂val E hE hu
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with rfl | rfl | rfl
      · exact huv rfl
      · exact huS (hmemS u huv (Or.inr (Or.inr (Or.inr rfl))))
      · exact huS (hmemS u huv (Or.inr (Or.inl rfl)))
    have hz1 : (P₁.filter (fun E => u ∈ E.val)).card = 0 := by
      rw [Finset.card_eq_zero]
      refine Finset.filter_eq_empty_iff.mpr (fun E hE hu => ?_)
      have := hP₁val E hE hu
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with rfl | rfl | rfl
      · exact huv rfl
      · exact huS (hmemS u huv (Or.inl rfl))
      · exact huS (hmemS u huv (Or.inr (Or.inr (Or.inl rfl))))
    rw [hz2] at h1
    rw [hz1] at h3
    rw [← hM₂def] at h1
    rw [← hM'def] at h3
    omega
  -- inside `S` the loss is bounded
  have hin : ∀ u ∈ S, unDeg G M' u ≤ unDeg G M u + 9 := by
    intro u _
    have h1 := unDeg_insert_add G (M \ R) hfree₂ u
    have h3 := unDeg_insert_add G M₂ hfree₁ u
    have h2 := unDeg_sdiff_le G hM hRM u
    rw [← hM₂def] at h1
    rw [← hM'def] at h3
    omega
  exact pot_lt_of_exchange G hvS hScard hvstep hout hin hcheap hbig

end Nibble
