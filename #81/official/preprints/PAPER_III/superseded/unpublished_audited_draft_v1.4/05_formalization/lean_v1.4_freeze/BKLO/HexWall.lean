/-
# The hexagon reservoir is unattainable: the chain wall

`BKLO/HexagonWeb.lean` closes the *local* half of the six-cycle case: a cluster reservoir carrying
the overlap structure `BKLO.HexWebData` absorbs a six-cycle leftover outright
(`BKLO.triDecomp_hex_absorb`), and `BKLO.HexWebReservoir` isolates exactly what the reservoir must
supply.  This file settles the remaining question — whether a *sparse* reservoir can supply it —
in the negative.

The obstruction is not the "triple coincidence" `D ∋ a 0, a 2, a 4` but the **chain** itself:
`C i ∋ x i, a (i-1), a i`.  Reading the demand as a closed walk in the cluster-intersection graph,
a hexagon `x 0 … x 5` needs six clusters `C 0 … C 5` with `x i ∈ C i` and consecutive clusters
meeting in the apex `a i`.  Counting such closed walks:

* a vertex lies in at most `d / 6` clusters, where `d` bounds the reserved degree;
* a cluster has seven vertices, so at most `7 d / 6` clusters meet a given one;
* **two distinct vertices lie in at most one common cluster** (the clusters are edge-disjoint), so
  the *closing* cluster `C 5`, which meets `C 4` in `a 4` and `C 0` in `a 5 ≠ a 4`, is determined
  by that pair of apexes: only `49` choices, not `7 d / 6`.

That last point is where the count is lost.  Choosing `x 0` (`n` ways), then `C 0, …, C 4`
(`d / 6` and four times `7 d / 6`), then the pair of closing apexes (`49`), and finally the six
leftover vertices inside their clusters (`7⁶`), every hexagon that the reservoir can serve is
reached, so at most `O(n d⁵)` of the `n⁶` hexagons are served.  With `d ≤ γ n` and `γ` small this
is a vanishing fraction, while only `O(γ n⁶)` hexagons meet the reservoir and are therefore exempt.
Hence some hexagon of unreserved edges is not served at all.

Precisely: a reservoir of maximum degree `d = γn` serves at most `7¹¹ n d⁵ = 7¹¹ γ⁵ n⁶` of the
`n(n-1)⋯(n-5)` six-cycles, and at most `6 n⁵ d = 6γn⁶` of them meet it; for `γ = 1/1000` and
`n ≥ 4000` the two together are fewer than `(n-5)⁶`.

The demand refuted is only `BKLO.HexChain` — six clusters `C i ∈ x i, a (i-1), a i` with the two
apexes of the closing cluster distinct.  The chord cluster `D` of the octahedron trade, the
distinctness of the seven clusters and the distinctness of the remaining apexes are never used, so
the wall applies to *any* gadget that pairs the two legs at each leftover vertex inside one
cluster, not just to the octahedron trade.

The results are `BKLO.card_hexCovered_le` (the counting), `BKLO.not_hexChainReservoir` (a sparse
cluster family never satisfies `BKLO.HexChainReservoir`) and its corollary
`BKLO.not_hexWebReservoir`, with the packaged form `BKLO.not_clusterReservoirHexWeb`:
`BKLO.ClusterReservoirExistence` cannot be strengthened to produce a hexagon-web reservoir.
Everything in this file is `sorry`-free.
-/
import BKLO.HexagonWeb
import Mathlib.Data.Fintype.CardEmbedding

open Finset

namespace BKLO

/-! ### A generic counting lemma for six nested choices -/

/-- If every fibre of a `biUnion` has at most `k` elements, the union has at most `|s| · k`. -/
theorem card_biUnion_le_mul {α β : Type*} [DecidableEq β] {s : Finset α} {t : α → Finset β} {k : ℕ}
    (h : ∀ a ∈ s, (t a).card ≤ k) : (s.biUnion t).card ≤ s.card * k := by
  classical
  calc (s.biUnion t).card ≤ ∑ a ∈ s, (t a).card := Finset.card_biUnion_le
    _ ≤ ∑ _a ∈ s, k := Finset.sum_le_sum h
    _ = s.card * k := by rw [Finset.sum_const, smul_eq_mul]

/-- **Six nested choices.**  A set of six-tuples in which each coordinate ranges, given the
previous ones, over a set of at most `kᵢ` elements has at most `k₁ ⋯ k₆` elements. -/
theorem card_sixtuple_le {α : Type*} [DecidableEq α] {T : Finset (α × α × α × α × α × α)}
    {A1 : Finset α} {A2 : α → Finset α} {A3 : α → α → Finset α} {A4 : α → α → α → Finset α}
    {A5 : α → α → α → α → Finset α} {A6 : α → α → α → α → α → Finset α}
    {k1 k2 k3 k4 k5 k6 : ℕ}
    (hsub : ∀ p ∈ T, p.1 ∈ A1 ∧ p.2.1 ∈ A2 p.1 ∧ p.2.2.1 ∈ A3 p.1 p.2.1 ∧
      p.2.2.2.1 ∈ A4 p.1 p.2.1 p.2.2.1 ∧
      p.2.2.2.2.1 ∈ A5 p.1 p.2.1 p.2.2.1 p.2.2.2.1 ∧
      p.2.2.2.2.2 ∈ A6 p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1)
    (h1 : A1.card ≤ k1) (h2 : ∀ a ∈ A1, (A2 a).card ≤ k2)
    (h3 : ∀ a ∈ A1, ∀ b ∈ A2 a, (A3 a b).card ≤ k3)
    (h4 : ∀ a ∈ A1, ∀ b ∈ A2 a, ∀ c ∈ A3 a b, (A4 a b c).card ≤ k4)
    (h5 : ∀ a ∈ A1, ∀ b ∈ A2 a, ∀ c ∈ A3 a b, ∀ d ∈ A4 a b c, (A5 a b c d).card ≤ k5)
    (h6 : ∀ a ∈ A1, ∀ b ∈ A2 a, ∀ c ∈ A3 a b, ∀ d ∈ A4 a b c, ∀ e ∈ A5 a b c d,
      (A6 a b c d e).card ≤ k6) :
    T.card ≤ k1 * k2 * k3 * k4 * k5 * k6 := by
  classical
  have hsub' : T ⊆ A1.biUnion (fun a => (A2 a).biUnion (fun b => (A3 a b).biUnion (fun c =>
      (A4 a b c).biUnion (fun d => (A5 a b c d).biUnion (fun e =>
        (A6 a b c d e).image (fun f => (a, b, c, d, e, f))))))) := by
    intro p hp
    obtain ⟨q1, q2, q3, q4, q5, q6⟩ := hsub p hp
    simp only [Finset.mem_biUnion, Finset.mem_image]
    exact ⟨p.1, q1, p.2.1, q2, p.2.2.1, q3, p.2.2.2.1, q4, p.2.2.2.2.1, q5, p.2.2.2.2.2, q6, rfl⟩
  refine (Finset.card_le_card hsub').trans ?_
  have B6 : ∀ a ∈ A1, ∀ b ∈ A2 a, ∀ c ∈ A3 a b, ∀ d ∈ A4 a b c, ∀ e ∈ A5 a b c d,
      ((A6 a b c d e).image (fun f => (a, b, c, d, e, f))).card ≤ k6 := by
    intro a ha b hb c hc d hd e he
    exact Finset.card_image_le.trans (h6 a ha b hb c hc d hd e he)
  have B5 : ∀ a ∈ A1, ∀ b ∈ A2 a, ∀ c ∈ A3 a b, ∀ d ∈ A4 a b c,
      ((A5 a b c d).biUnion (fun e => (A6 a b c d e).image (fun f => (a, b, c, d, e, f)))).card
        ≤ k5 * k6 := by
    intro a ha b hb c hc d hd
    exact (card_biUnion_le_mul (B6 a ha b hb c hc d hd)).trans
      (Nat.mul_le_mul_right _ (h5 a ha b hb c hc d hd))
  have B4 : ∀ a ∈ A1, ∀ b ∈ A2 a, ∀ c ∈ A3 a b,
      ((A4 a b c).biUnion (fun d => (A5 a b c d).biUnion (fun e =>
        (A6 a b c d e).image (fun f => (a, b, c, d, e, f))))).card ≤ k4 * (k5 * k6) := by
    intro a ha b hb c hc
    exact (card_biUnion_le_mul (B5 a ha b hb c hc)).trans
      (Nat.mul_le_mul_right _ (h4 a ha b hb c hc))
  have B3 : ∀ a ∈ A1, ∀ b ∈ A2 a,
      ((A3 a b).biUnion (fun c => (A4 a b c).biUnion (fun d => (A5 a b c d).biUnion (fun e =>
        (A6 a b c d e).image (fun f => (a, b, c, d, e, f)))))).card ≤ k3 * (k4 * (k5 * k6)) := by
    intro a ha b hb
    exact (card_biUnion_le_mul (B4 a ha b hb)).trans (Nat.mul_le_mul_right _ (h3 a ha b hb))
  have B2 : ∀ a ∈ A1,
      ((A2 a).biUnion (fun b => (A3 a b).biUnion (fun c => (A4 a b c).biUnion (fun d =>
        (A5 a b c d).biUnion (fun e => (A6 a b c d e).image (fun f => (a, b, c, d, e, f))))))).card
        ≤ k2 * (k3 * (k4 * (k5 * k6))) := by
    intro a ha
    exact (card_biUnion_le_mul (B3 a ha)).trans (Nat.mul_le_mul_right _ (h2 a ha))
  refine (card_biUnion_le_mul B2).trans ?_
  calc A1.card * (k2 * (k3 * (k4 * (k5 * k6)))) ≤ k1 * (k2 * (k3 * (k4 * (k5 * k6)))) :=
        Nat.mul_le_mul_right _ h1
    _ = k1 * k2 * k3 * k4 * k5 * k6 := by ring

/-! ### Local resources of a cluster family -/

variable {V : Type*} [DecidableEq V]

/-- The clusters of the family through a given vertex. -/
def clustersAt (𝒞 : Finset (Finset V)) (v : V) : Finset (Finset V) :=
  𝒞.filter (fun C => v ∈ C)

theorem mem_clustersAt {𝒞 : Finset (Finset V)} {v : V} {C : Finset V} :
    C ∈ clustersAt 𝒞 v ↔ C ∈ 𝒞 ∧ v ∈ C := by
  simp [clustersAt]

/-- **A vertex lies in few clusters.**  The clusters through `v` are edge-disjoint and each
contributes six reserved edges at `v`. -/
theorem six_mul_card_clustersAt_le {E : Finset (Sym2 V)} {𝒞 : Finset (Finset V)}
    (h𝒞 : ClusterFamilyIn E 𝒞) (v : V) :
    6 * (clustersAt 𝒞 v).card ≤ edeg (famEdges 𝒞) v := by
  classical
  set F : Finset V → Finset (Sym2 V) := fun C => (cliqueEdges C).filter (fun e => v ∈ e) with hF
  have hcardF : ∀ C ∈ clustersAt 𝒞 v, (F C).card = 6 := by
    intro C hC
    obtain ⟨hC𝒞, hvC⟩ := mem_clustersAt.1 hC
    have := edeg_cliqueEdges_seven (h𝒞.1 C hC𝒞) v
    rw [if_pos hvC] at this
    exact this
  have hdisj : ∀ C ∈ clustersAt 𝒞 v, ∀ C' ∈ clustersAt 𝒞 v, C ≠ C' → Disjoint (F C) (F C') := by
    intro C hC C' hC' hne
    exact Finset.disjoint_of_subset_left (Finset.filter_subset _ _)
      (Finset.disjoint_of_subset_right (Finset.filter_subset _ _)
        (h𝒞.2.2 C (mem_clustersAt.1 hC).1 C' (mem_clustersAt.1 hC').1 hne))
  have hcard : ((clustersAt 𝒞 v).biUnion F).card = 6 * (clustersAt 𝒞 v).card := by
    rw [Finset.card_biUnion hdisj, Finset.sum_congr rfl hcardF, Finset.sum_const, smul_eq_mul,
      Nat.mul_comm]
  have hsub : (clustersAt 𝒞 v).biUnion F ⊆ (famEdges 𝒞).filter (fun e => v ∈ e) := by
    intro e he
    obtain ⟨C, hC, heC⟩ := Finset.mem_biUnion.1 he
    rw [hF] at heC
    simp only [Finset.mem_filter] at heC ⊢
    exact ⟨Finset.mem_biUnion.2 ⟨C, (mem_clustersAt.1 hC).1, heC.1⟩, heC.2⟩
  rw [← hcard, edeg]
  exact Finset.card_le_card hsub

/-- Two distinct vertices lie in at most one common cluster. -/
theorem cluster_unique_of_two {E : Finset (Sym2 V)} {𝒞 : Finset (Finset V)}
    (h𝒞 : ClusterFamilyIn E 𝒞) {C C' : Finset V} (hC : C ∈ 𝒞) (hC' : C' ∈ 𝒞) {u w : V}
    (huw : u ≠ w) (hu : u ∈ C) (hw : w ∈ C) (hu' : u ∈ C') (hw' : w ∈ C') : C = C' := by
  have hmem : ∀ A : Finset V, u ∈ A → w ∈ A → s(u, w) ∈ cliqueEdges A := by
    intro A hA1 hA2
    refine mem_cliqueEdgesV.2 ⟨?_, ?_⟩
    · intro z hz
      rcases Sym2.mem_iff.1 hz with rfl | rfl
      exacts [hA1, hA2]
    · simpa [Sym2.isDiag_iff_proj_eq] using huw
  exact cluster_unique_of_mem h𝒞 hC hC' (hmem C hu hw) (hmem C' hu' hw')

/-- The clusters meeting a given cluster. -/
def meetsCl (𝒞 : Finset (Finset V)) (C : Finset V) : Finset (Finset V) :=
  C.biUnion (clustersAt 𝒞)

theorem card_meetsCl_le {𝒞 : Finset (Finset V)} {m : ℕ}
    (hm : ∀ v : V, (clustersAt 𝒞 v).card ≤ m) {C : Finset V} (hC : C.card ≤ 7) :
    (meetsCl 𝒞 C).card ≤ 7 * m :=
  (card_biUnion_le_mul (fun v _ => hm v)).trans (Nat.mul_le_mul_right _ hC)

/-- The clusters meeting `C` and `C'` in two *distinct* vertices: there are at most `49`, since
each such cluster is determined by the pair of meeting points. -/
def dblMeets (𝒞 : Finset (Finset V)) (C C' : Finset V) : Finset (Finset V) :=
  (C ×ˢ C').biUnion
    (fun q => if q.1 = q.2 then ∅ else 𝒞.filter (fun A => q.1 ∈ A ∧ q.2 ∈ A))

theorem card_dblMeets_le {E : Finset (Sym2 V)} {𝒞 : Finset (Finset V)}
    (h𝒞 : ClusterFamilyIn E 𝒞) {C C' : Finset V} (hC : C.card ≤ 7) (hC' : C'.card ≤ 7) :
    (dblMeets 𝒞 C C').card ≤ 49 := by
  classical
  refine (card_biUnion_le_mul (k := 1) ?_).trans ?_
  · intro q _
    by_cases hq : q.1 = q.2
    · simp [hq]
    · rw [if_neg hq]
      refine Finset.card_le_one.2 ?_
      intro A hA B hB
      simp only [Finset.mem_filter] at hA hB
      exact cluster_unique_of_two h𝒞 hA.1 hB.1 hq hA.2.1 hA.2.2 hB.2.1 hB.2.2
  · rw [Finset.card_product, Nat.mul_one]
    calc C.card * C'.card ≤ 7 * 7 := Nat.mul_le_mul hC hC'
      _ = 49 := by norm_num

theorem meetsCl_subset {𝒞 : Finset (Finset V)} {C : Finset V} : meetsCl 𝒞 C ⊆ 𝒞 := by
  intro A hA
  obtain ⟨v, _, hv⟩ := Finset.mem_biUnion.1 hA
  exact (mem_clustersAt.1 hv).1

theorem dblMeets_subset {𝒞 : Finset (Finset V)} {C C' : Finset V} : dblMeets 𝒞 C C' ⊆ 𝒞 := by
  intro A hA
  obtain ⟨q, _, hq⟩ := Finset.mem_biUnion.1 hA
  by_cases h : q.1 = q.2
  · simp [h] at hq
  · rw [if_neg h] at hq
    exact (Finset.mem_filter.1 hq).1

/-- **The family has few clusters.**  Summing the seven vertices of each cluster. -/
theorem seven_mul_card_le [Fintype V] {E : Finset (Sym2 V)} {𝒞 : Finset (Finset V)} {m : ℕ}
    (h𝒞 : ClusterFamilyIn E 𝒞) (hm : ∀ v : V, (clustersAt 𝒞 v).card ≤ m) :
    7 * 𝒞.card ≤ Fintype.card V * m := by
  classical
  have hcount : ∑ v : V, (clustersAt 𝒞 v).card = ∑ C ∈ 𝒞, C.card := by
    have h1 : ∀ v : V, (clustersAt 𝒞 v).card = ∑ C ∈ 𝒞, if v ∈ C then 1 else 0 := by
      intro v; rw [clustersAt, Finset.card_filter]
    have h2 : ∀ C : Finset V, (∑ v : V, if v ∈ C then 1 else 0) = C.card := by
      intro C; simp
    rw [Finset.sum_congr rfl (fun v _ => h1 v), Finset.sum_comm]
    exact Finset.sum_congr rfl (fun C _ => h2 C)
  have hleft : ∑ C ∈ 𝒞, C.card = 7 * 𝒞.card := by
    rw [Finset.sum_congr rfl (fun C hC => h𝒞.1 C hC), Finset.sum_const, smul_eq_mul,
      Nat.mul_comm]
  have hright : ∑ v : V, (clustersAt 𝒞 v).card ≤ Fintype.card V * m := by
    calc ∑ v : V, (clustersAt 𝒞 v).card ≤ ∑ _v : V, m := Finset.sum_le_sum (fun v _ => hm v)
      _ = Fintype.card V * m := by rw [Finset.sum_const, smul_eq_mul, Finset.card_univ]
  rw [← hleft, ← hcount]
  exact hright

/-! ### Counting the hexagons a cluster family can serve -/

variable [Fintype V]

/-- The six-cycle attached to a six-tuple of vertices. -/
def hexTup (p : V × V × V × V × V × V) : Fin 6 → V :=
  ![p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2]

/-- **The chain**: the part of the hexagon gadget's demand that the wall already refutes.  The two
legs at the leftover vertex `x i` are paired inside a single cluster `C i ∈ x i, a (i-1), a i`, and
the two apexes of the closing cluster are distinct.  No chord cluster `D`, no distinctness of the
clusters and no distinctness of the remaining apexes is asked for: `BKLO.HexWebData` implies it. -/
structure HexChain (𝒞 : Finset (Finset V)) (x a : Fin 6 → V) (C : Fin 6 → Finset V) : Prop where
  /-- the clusters belong to the family -/
  Cmem : ∀ i, C i ∈ 𝒞
  /-- `C i` holds the leftover vertex `x i` -/
  xC : ∀ i, x i ∈ C i
  /-- ... and the apex `a i` of the leftover edge `x i x (i+1)` -/
  aC : ∀ i, a i ∈ C i
  /-- ... which `C (i+1)` holds as well -/
  aC' : ∀ i, a i ∈ C (i + 1)
  /-- the two apexes of the closing cluster are distinct -/
  a45 : a 4 ≠ a 5

omit [DecidableEq V] [Fintype V] in
/-- The hexagon gadget demands the chain. -/
theorem HexWebData.hexChain {𝒞 : Finset (Finset V)} {x a : Fin 6 → V} {C : Fin 6 → Finset V}
    {D : Finset V} (hd : HexWebData 𝒞 x a C D) : HexChain 𝒞 x a C where
  Cmem := hd.Cmem
  xC := hd.xC
  aC := hd.aC
  aC' := hd.aC'
  a45 := hd.aa 4 5 (by decide)

/-- The six-tuples of clusters that can carry the hexagon gadget: consecutive clusters meet, and
the closing cluster meets the fourth and the first in two *distinct* vertices. -/
noncomputable def clusterCycles (𝒞 : Finset (Finset V)) :
    Finset (Finset V × Finset V × Finset V × Finset V × Finset V × Finset V) :=
  open Classical in
  Finset.univ.filter (fun c => c.1 ∈ 𝒞 ∧ c.2.1 ∈ meetsCl 𝒞 c.1 ∧ c.2.2.1 ∈ meetsCl 𝒞 c.2.1 ∧
    c.2.2.2.1 ∈ meetsCl 𝒞 c.2.2.1 ∧ c.2.2.2.2.1 ∈ meetsCl 𝒞 c.2.2.2.1 ∧
    c.2.2.2.2.2 ∈ dblMeets 𝒞 c.2.2.2.2.1 c.1)

/-- The hexagons the reservoir can serve: those carrying the chain. -/
noncomputable def hexCovered (𝒞 : Finset (Finset V)) : Finset (V × V × V × V × V × V) :=
  open Classical in
  Finset.univ.filter
    (fun p => ∃ (a : Fin 6 → V) (C : Fin 6 → Finset V), HexChain 𝒞 (hexTup p) a C)

theorem card_clusterCycles_le {E : Finset (Sym2 V)} {𝒞 : Finset (Finset V)} {m : ℕ}
    (h𝒞 : ClusterFamilyIn E 𝒞) (hm : ∀ v : V, (clustersAt 𝒞 v).card ≤ m) :
    (clusterCycles 𝒞).card ≤ 𝒞.card * (7 * m) * (7 * m) * (7 * m) * (7 * m) * 49 := by
  classical
  have hcard7 : ∀ C ∈ 𝒞, C.card ≤ 7 := fun C hC => le_of_eq (h𝒞.1 C hC)
  refine card_sixtuple_le (A1 := 𝒞) (A2 := fun a => meetsCl 𝒞 a)
    (A3 := fun _ b => meetsCl 𝒞 b) (A4 := fun _ _ c => meetsCl 𝒞 c)
    (A5 := fun _ _ _ d => meetsCl 𝒞 d) (A6 := fun a _ _ _ e => dblMeets 𝒞 e a) ?_ le_rfl ?_ ?_ ?_
    ?_ ?_
  · intro p hp
    rw [clusterCycles, Finset.mem_filter] at hp
    exact ⟨hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1, hp.2.2.2.2.2.1, hp.2.2.2.2.2.2⟩
  · exact fun a ha => card_meetsCl_le hm (hcard7 a ha)
  · exact fun _ _ b hb => card_meetsCl_le hm (hcard7 b (meetsCl_subset hb))
  · exact fun _ _ b hb c hc => card_meetsCl_le hm (hcard7 c (meetsCl_subset hc))
  · exact fun _ _ b hb c hc d hd => card_meetsCl_le hm (hcard7 d (meetsCl_subset hd))
  · exact fun a ha b hb c hc d hd e he =>
      card_dblMeets_le h𝒞 (hcard7 e (meetsCl_subset he)) (hcard7 a ha)

/-- **Every served hexagon lies inside a cluster cycle.**  Its six vertices lie in the six
clusters of the gadget, which form a closed cluster walk. -/
theorem hexCovered_subset {𝒞 : Finset (Finset V)} :
    hexCovered 𝒞 ⊆ (clusterCycles 𝒞).biUnion (fun c =>
      c.1 ×ˢ (c.2.1 ×ˢ (c.2.2.1 ×ˢ (c.2.2.2.1 ×ˢ (c.2.2.2.2.1 ×ˢ c.2.2.2.2.2))))) := by
  classical
  intro p hp
  rw [hexCovered, Finset.mem_filter] at hp
  obtain ⟨a, C, hd⟩ := hp.2
  refine Finset.mem_biUnion.2 ⟨(C 0, C 1, C 2, C 3, C 4, C 5), ?_, ?_⟩
  · rw [clusterCycles, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, hd.Cmem 0, ?_, ?_, ?_, ?_, ?_⟩
    · exact Finset.mem_biUnion.2 ⟨a 0, hd.aC 0, mem_clustersAt.2 ⟨hd.Cmem 1, hd.aC' 0⟩⟩
    · exact Finset.mem_biUnion.2 ⟨a 1, hd.aC 1, mem_clustersAt.2 ⟨hd.Cmem 2, hd.aC' 1⟩⟩
    · exact Finset.mem_biUnion.2 ⟨a 2, hd.aC 2, mem_clustersAt.2 ⟨hd.Cmem 3, hd.aC' 2⟩⟩
    · exact Finset.mem_biUnion.2 ⟨a 3, hd.aC 3, mem_clustersAt.2 ⟨hd.Cmem 4, hd.aC' 3⟩⟩
    · refine Finset.mem_biUnion.2 ⟨(a 4, a 5), Finset.mem_product.2 ⟨hd.aC 4, hd.aC' 5⟩, ?_⟩
      rw [if_neg hd.a45]
      exact Finset.mem_filter.2 ⟨hd.Cmem 5, hd.aC' 4, hd.aC 5⟩
  · exact Finset.mem_product.2 ⟨hd.xC 0, Finset.mem_product.2 ⟨hd.xC 1,
      Finset.mem_product.2 ⟨hd.xC 2, Finset.mem_product.2 ⟨hd.xC 3,
        Finset.mem_product.2 ⟨hd.xC 4, hd.xC 5⟩⟩⟩⟩⟩

/-- **The reservoir serves few hexagons.**  Each cluster cycle serves at most `7⁶` of them. -/
theorem card_hexCovered_le_cycles {E : Finset (Sym2 V)} {𝒞 : Finset (Finset V)}
    (h𝒞 : ClusterFamilyIn E 𝒞) :
    (hexCovered 𝒞).card ≤ (clusterCycles 𝒞).card * 7 ^ 6 := by
  classical
  refine (Finset.card_le_card hexCovered_subset).trans (card_biUnion_le_mul ?_)
  intro c hc
  rw [clusterCycles, Finset.mem_filter] at hc
  obtain ⟨-, h0, h1, h2, h3, h4, h5⟩ := hc
  have hc7 : ∀ C ∈ 𝒞, C.card ≤ 7 := fun C hC => le_of_eq (h𝒞.1 C hC)
  have e0 := hc7 _ h0
  have e1 := hc7 _ (meetsCl_subset h1)
  have e2 := hc7 _ (meetsCl_subset h2)
  have e3 := hc7 _ (meetsCl_subset h3)
  have e4 := hc7 _ (meetsCl_subset h4)
  have e5 := hc7 _ (dblMeets_subset h5)
  rw [Finset.card_product, Finset.card_product, Finset.card_product, Finset.card_product,
    Finset.card_product]
  calc c.1.card * (c.2.1.card * (c.2.2.1.card * (c.2.2.2.1.card *
        (c.2.2.2.2.1.card * c.2.2.2.2.2.card))))
      ≤ 7 * (7 * (7 * (7 * (7 * 7)))) :=
        Nat.mul_le_mul e0 (Nat.mul_le_mul e1 (Nat.mul_le_mul e2
          (Nat.mul_le_mul e3 (Nat.mul_le_mul e4 e5))))
    _ = 7 ^ 6 := by norm_num

/-- **The counting.**  A cluster family in which every vertex lies in at most `m` clusters serves
at most `7¹² |V| m⁵ / 7` hexagons. -/
theorem card_hexCovered_le {E : Finset (Sym2 V)} {𝒞 : Finset (Finset V)} {m : ℕ}
    (h𝒞 : ClusterFamilyIn E 𝒞) (hm : ∀ v : V, (clustersAt 𝒞 v).card ≤ m) :
    7 * (hexCovered 𝒞).card ≤ 7 ^ 12 * (Fintype.card V * m ^ 5) := by
  have h1 := card_hexCovered_le_cycles h𝒞 (𝒞 := 𝒞)
  have h2 := card_clusterCycles_le h𝒞 hm
  have h3 := seven_mul_card_le h𝒞 hm
  calc 7 * (hexCovered 𝒞).card
      ≤ 7 * ((clusterCycles 𝒞).card * 7 ^ 6) := Nat.mul_le_mul_left _ h1
    _ ≤ 7 * ((𝒞.card * (7 * m) * (7 * m) * (7 * m) * (7 * m) * 49) * 7 ^ 6) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ h2)
    _ = (7 * 𝒞.card) * (7 ^ 12 * m ^ 4) := by ring
    _ ≤ (Fintype.card V * m) * (7 ^ 12 * m ^ 4) := Nat.mul_le_mul_right _ h3
    _ = 7 ^ 12 * (Fintype.card V * m ^ 5) := by ring

/-! ### Hexagons that meet the reservoir -/

/-- The six-tuples whose `i`-th hexagon edge is reserved. -/
noncomputable def resEdgeSet (R : Finset (Sym2 V)) (i : Fin 6) : Finset (V × V × V × V × V × V) :=
  open Classical in
  Finset.univ.filter (fun p => s(hexTup p i, hexTup p (i + 1)) ∈ R)

theorem card_resEdgeSet_le {R : Finset (Sym2 V)} {d : ℕ} (hd : ∀ v : V, edeg R v ≤ d)
    (i : Fin 6) : (resEdgeSet R i).card ≤ Fintype.card V ^ 5 * d := by
  classical
  have hres : ∀ a : V, (resNbr R a).card ≤ d := fun a => (card_resNbr_le a).trans (hd a)
  have hswap : ∀ u w : V, s(u, w) ∈ R → w ∈ resNbr R u := by
    intro u w h
    simpa [resNbr] using h
  fin_cases i
  · refine (card_sixtuple_le (A1 := Finset.univ) (A2 := fun a => resNbr R a)
      (A3 := fun _ _ => Finset.univ) (A4 := fun _ _ _ => Finset.univ)
      (A5 := fun _ _ _ _ => Finset.univ) (A6 := fun _ _ _ _ _ => Finset.univ)
      (k1 := Fintype.card V) (k2 := d) (k3 := Fintype.card V) (k4 := Fintype.card V)
      (k5 := Fintype.card V) (k6 := Fintype.card V) ?_ (by simp [Finset.card_univ])
      (fun a _ => hres a) (fun _ _ _ _ => by simp [Finset.card_univ])
      (fun _ _ _ _ _ _ => by simp [Finset.card_univ])
      (fun _ _ _ _ _ _ _ _ => by simp [Finset.card_univ])
      (fun _ _ _ _ _ _ _ _ _ _ => by simp [Finset.card_univ])).trans (by ring_nf; exact le_rfl)
    intro p hp
    rw [resEdgeSet, Finset.mem_filter] at hp
    exact ⟨Finset.mem_univ _, hswap _ _ hp.2, Finset.mem_univ _, Finset.mem_univ _,
      Finset.mem_univ _, Finset.mem_univ _⟩
  · refine (card_sixtuple_le (A1 := Finset.univ) (A2 := fun _ => Finset.univ)
      (A3 := fun _ b => resNbr R b) (A4 := fun _ _ _ => Finset.univ)
      (A5 := fun _ _ _ _ => Finset.univ) (A6 := fun _ _ _ _ _ => Finset.univ)
      (k1 := Fintype.card V) (k2 := Fintype.card V) (k3 := d) (k4 := Fintype.card V)
      (k5 := Fintype.card V) (k6 := Fintype.card V) ?_ (by simp [Finset.card_univ])
      (fun _ _ => by simp [Finset.card_univ]) (fun _ _ b _ => hres b)
      (fun _ _ _ _ _ _ => by simp [Finset.card_univ])
      (fun _ _ _ _ _ _ _ _ => by simp [Finset.card_univ])
      (fun _ _ _ _ _ _ _ _ _ _ => by simp [Finset.card_univ])).trans (by ring_nf; exact le_rfl)
    intro p hp
    rw [resEdgeSet, Finset.mem_filter] at hp
    exact ⟨Finset.mem_univ _, Finset.mem_univ _, hswap _ _ hp.2, Finset.mem_univ _,
      Finset.mem_univ _, Finset.mem_univ _⟩
  · refine (card_sixtuple_le (A1 := Finset.univ) (A2 := fun _ => Finset.univ)
      (A3 := fun _ _ => Finset.univ) (A4 := fun _ _ c => resNbr R c)
      (A5 := fun _ _ _ _ => Finset.univ) (A6 := fun _ _ _ _ _ => Finset.univ)
      (k1 := Fintype.card V) (k2 := Fintype.card V) (k3 := Fintype.card V) (k4 := d)
      (k5 := Fintype.card V) (k6 := Fintype.card V) ?_ (by simp [Finset.card_univ])
      (fun _ _ => by simp [Finset.card_univ]) (fun _ _ _ _ => by simp [Finset.card_univ])
      (fun _ _ _ _ c _ => hres c)
      (fun _ _ _ _ _ _ _ _ => by simp [Finset.card_univ])
      (fun _ _ _ _ _ _ _ _ _ _ => by simp [Finset.card_univ])).trans (by ring_nf; exact le_rfl)
    intro p hp
    rw [resEdgeSet, Finset.mem_filter] at hp
    exact ⟨Finset.mem_univ _, Finset.mem_univ _, Finset.mem_univ _, hswap _ _ hp.2,
      Finset.mem_univ _, Finset.mem_univ _⟩
  · refine (card_sixtuple_le (A1 := Finset.univ) (A2 := fun _ => Finset.univ)
      (A3 := fun _ _ => Finset.univ) (A4 := fun _ _ _ => Finset.univ)
      (A5 := fun _ _ _ d' => resNbr R d') (A6 := fun _ _ _ _ _ => Finset.univ)
      (k1 := Fintype.card V) (k2 := Fintype.card V) (k3 := Fintype.card V)
      (k4 := Fintype.card V) (k5 := d) (k6 := Fintype.card V) ?_ (by simp [Finset.card_univ])
      (fun _ _ => by simp [Finset.card_univ]) (fun _ _ _ _ => by simp [Finset.card_univ])
      (fun _ _ _ _ _ _ => by simp [Finset.card_univ]) (fun _ _ _ _ _ _ d' _ => hres d')
      (fun _ _ _ _ _ _ _ _ _ _ => by simp [Finset.card_univ])).trans (by ring_nf; exact le_rfl)
    intro p hp
    rw [resEdgeSet, Finset.mem_filter] at hp
    exact ⟨Finset.mem_univ _, Finset.mem_univ _, Finset.mem_univ _, Finset.mem_univ _,
      hswap _ _ hp.2, Finset.mem_univ _⟩
  · refine (card_sixtuple_le (A1 := Finset.univ) (A2 := fun _ => Finset.univ)
      (A3 := fun _ _ => Finset.univ) (A4 := fun _ _ _ => Finset.univ)
      (A5 := fun _ _ _ _ => Finset.univ) (A6 := fun _ _ _ _ e => resNbr R e)
      (k1 := Fintype.card V) (k2 := Fintype.card V) (k3 := Fintype.card V)
      (k4 := Fintype.card V) (k5 := Fintype.card V) (k6 := d) ?_ (by simp [Finset.card_univ])
      (fun _ _ => by simp [Finset.card_univ]) (fun _ _ _ _ => by simp [Finset.card_univ])
      (fun _ _ _ _ _ _ => by simp [Finset.card_univ])
      (fun _ _ _ _ _ _ _ _ => by simp [Finset.card_univ])
      (fun _ _ _ _ _ _ _ _ e _ => hres e)).trans (by ring_nf; exact le_rfl)
    intro p hp
    rw [resEdgeSet, Finset.mem_filter] at hp
    exact ⟨Finset.mem_univ _, Finset.mem_univ _, Finset.mem_univ _, Finset.mem_univ _,
      Finset.mem_univ _, hswap _ _ hp.2⟩
  · refine (card_sixtuple_le (A1 := Finset.univ) (A2 := fun _ => Finset.univ)
      (A3 := fun _ _ => Finset.univ) (A4 := fun _ _ _ => Finset.univ)
      (A5 := fun _ _ _ _ => Finset.univ) (A6 := fun a _ _ _ _ => resNbr R a)
      (k1 := Fintype.card V) (k2 := Fintype.card V) (k3 := Fintype.card V)
      (k4 := Fintype.card V) (k5 := Fintype.card V) (k6 := d) ?_ (by simp [Finset.card_univ])
      (fun _ _ => by simp [Finset.card_univ]) (fun _ _ _ _ => by simp [Finset.card_univ])
      (fun _ _ _ _ _ _ => by simp [Finset.card_univ])
      (fun _ _ _ _ _ _ _ _ => by simp [Finset.card_univ])
      (fun a _ _ _ _ _ _ _ _ _ => hres a)).trans (by ring_nf; exact le_rfl)
    intro p hp
    rw [resEdgeSet, Finset.mem_filter] at hp
    refine ⟨Finset.mem_univ _, Finset.mem_univ _, Finset.mem_univ _, Finset.mem_univ _,
      Finset.mem_univ _, hswap _ _ ?_⟩
    rw [Sym2.eq_swap]
    exact hp.2

/-! ### The arithmetic -/

/-- The numerical heart of the wall: with `1000 d ≤ n` the hexagons a reservoir of maximum degree
`d` can serve, together with those meeting it, are fewer than the injective six-tuples. -/
theorem hexwall_arith {n d B : ℕ} (hB : 7 * B ≤ 7 ^ 12 * (n * d ^ 5))
    (hdn : 1000 * d ≤ n) (hn : 4000 ≤ n) : B + 6 * (n ^ 5 * d) < n.descFactorial 6 := by
  set N := n - 5 with hN
  have hnN : n ≤ 2 * N := by omega
  have hNpos : 0 < N := by omega
  have hdesc : N ^ 6 ≤ n.descFactorial 6 := by
    have hexp : n.descFactorial 6 = n * ((n - 1) * ((n - 2) * ((n - 3) * ((n - 4) * (n - 5))))) := by
      simp [Nat.descFactorial]; ring
    have h6 : N ^ 6 = N * (N * (N * (N * (N * N)))) := by ring
    rw [hexp, h6]
    exact Nat.mul_le_mul (by omega) (Nat.mul_le_mul (by omega) (Nat.mul_le_mul (by omega)
      (Nat.mul_le_mul (by omega) (Nat.mul_le_mul (by omega) (by omega)))))
  have hd5 : 10 ^ 15 * d ^ 5 ≤ n ^ 5 := by
    calc 10 ^ 15 * d ^ 5 = (1000 * d) ^ 5 := by ring
      _ ≤ n ^ 5 := Nat.pow_le_pow_left hdn 5
  have hn6 : n ^ 6 ≤ 64 * N ^ 6 := by
    calc n ^ 6 ≤ (2 * N) ^ 6 := Nat.pow_le_pow_left hnN 6
      _ = 64 * N ^ 6 := by ring
  have hb1 : 7 * 10 ^ 15 * (4 * B) ≤ 4 * (7 ^ 12 * 64) * N ^ 6 := by
    have hkey : 10 ^ 15 * (7 * B) ≤ 7 ^ 12 * (64 * N ^ 6) := by
      calc 10 ^ 15 * (7 * B) ≤ 10 ^ 15 * (7 ^ 12 * (n * d ^ 5)) := Nat.mul_le_mul_left _ hB
        _ = 7 ^ 12 * (n * (10 ^ 15 * d ^ 5)) := by ring
        _ ≤ 7 ^ 12 * (n * n ^ 5) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hd5)
        _ = 7 ^ 12 * n ^ 6 := by ring
        _ ≤ 7 ^ 12 * (64 * N ^ 6) := Nat.mul_le_mul_left _ hn6
    nlinarith only [hkey]
  have hb2 : 4 * B ≤ N ^ 6 := by
    refine Nat.le_of_mul_le_mul_left (hb1.trans ?_) (show 0 < 7 * 10 ^ 15 by norm_num)
    exact Nat.mul_le_mul_right _ (by norm_num)
  have hb3 : 24 * (n ^ 5 * d) ≤ 2 * N ^ 6 := by
    refine Nat.le_of_mul_le_mul_left ?_ (show 0 < 1000 by norm_num)
    calc 1000 * (24 * (n ^ 5 * d)) = 24 * (n ^ 5 * (1000 * d)) := by ring
      _ ≤ 24 * (n ^ 5 * n) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hdn)
      _ = 24 * n ^ 6 := by ring
      _ ≤ 24 * (64 * N ^ 6) := Nat.mul_le_mul_left _ hn6
      _ ≤ 1000 * (2 * N ^ 6) := by linarith only [hb2]
  have hpos : 0 < N ^ 6 := by positivity
  have hsum : 4 * (B + 6 * (n ^ 5 * d)) = 4 * B + 24 * (n ^ 5 * d) := by ring
  exact lt_of_lt_of_le (by omega) hdesc

/-! ### The wall -/

/-- The six-tuple of values of an embedding. -/
def embTup (f : Fin 6 ↪ V) : V × V × V × V × V × V := (f 0, f 1, f 2, f 3, f 4, f 5)

omit [DecidableEq V] [Fintype V] in
theorem hexTup_embTup (f : Fin 6 ↪ V) : hexTup (embTup f) = ⇑f := by
  funext i; fin_cases i <;> rfl

omit [DecidableEq V] [Fintype V] in
theorem embTup_injective : Function.Injective (embTup (V := V)) := by
  intro f g h
  rw [embTup, embTup, Prod.mk.injEq, Prod.mk.injEq, Prod.mk.injEq, Prod.mk.injEq,
    Prod.mk.injEq] at h
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := h
  refine Function.Embedding.ext ?_
  intro i
  fin_cases i
  exacts [h0, h1, h2, h3, h4, h5]

/-- **What a reservoir would have to supply for the chain**: for every six-cycle on `S` it does not
already meet, apexes and six clusters pairing the two legs at each leftover vertex.  This is weaker
than `BKLO.HexWebReservoir`, and already impossible. -/
def HexChainReservoir (𝒞 : Finset (Finset V)) (S : Finset V) : Prop :=
  ∀ x : Fin 6 → V, (∀ i j : Fin 6, i ≠ j → x i ≠ x j) → (∀ i, x i ∈ S) →
    Disjoint (famEdges 𝒞) (hexEdges x) →
      ∃ (a : Fin 6 → V) (C : Fin 6 → Finset V), HexChain 𝒞 x a C

/-- **The chain reservoir does not exist.**  A cluster family whose reserved degree is at most `d`,
with `1000 d ≤ |V|` and `|V| ≥ 4000`, fails `BKLO.HexChainReservoir`: some six-cycle of unreserved
edges is not served.

The six clusters of the gadget form a closed walk in the cluster-intersection graph, and its
closing step is free of choice, because two distinct apexes lie in at most one common cluster. -/
theorem not_hexChainReservoir {E : Finset (Sym2 V)} {𝒞 : Finset (Finset V)} {d : ℕ}
    (h𝒞 : ClusterFamilyIn E 𝒞) (hd : ∀ v : V, edeg (famEdges 𝒞) v ≤ d)
    (hdn : 1000 * d ≤ Fintype.card V) (hn : 4000 ≤ Fintype.card V) :
    ¬ HexChainReservoir 𝒞 (Finset.univ : Finset V) := by
  classical
  intro hres
  have hm : ∀ v : V, (clustersAt 𝒞 v).card ≤ d := by
    intro v
    have h1 := six_mul_card_clustersAt_le h𝒞 v
    have h2 := hd v
    omega
  have hcov := card_hexCovered_le h𝒞 hm
  set Bad : Finset (V × V × V × V × V × V) :=
    hexCovered 𝒞 ∪ (Finset.univ : Finset (Fin 6)).biUnion (resEdgeSet (famEdges 𝒞)) with hBad
  have hBadcard : Bad.card ≤ (hexCovered 𝒞).card + 6 * (Fintype.card V ^ 5 * d) := by
    refine (Finset.card_union_le _ _).trans (Nat.add_le_add_left ?_ _)
    refine (card_biUnion_le_mul (fun i _ => card_resEdgeSet_le hd i)).trans ?_
    simp [Finset.card_univ]
  have hlt : Bad.card < (Fintype.card V).descFactorial 6 :=
    lt_of_le_of_lt hBadcard (hexwall_arith hcov hdn hn)
  have hcardEmb : (Finset.univ : Finset (Fin 6 ↪ V)).card = (Fintype.card V).descFactorial 6 := by
    rw [Finset.card_univ, Fintype.card_embedding_eq]
    simp
  obtain ⟨f, hf⟩ : ∃ f : Fin 6 ↪ V, embTup f ∉ Bad := by
    by_contra hcon
    push_neg at hcon
    have hle : (Finset.univ : Finset (Fin 6 ↪ V)).card ≤ Bad.card :=
      Finset.card_le_card_of_injOn embTup (fun f _ => hcon f)
        (fun a _ b _ h => embTup_injective h)
    omega
  have hx : ∀ i j : Fin 6, i ≠ j → (f : Fin 6 → V) i ≠ f j := fun i j hij h => hij (f.injective h)
  have hdisj : Disjoint (famEdges 𝒞) (hexEdges (f : Fin 6 → V)) := by
    rw [Finset.disjoint_right]
    intro e he heR
    obtain ⟨i, rfl⟩ := mem_hexEdges.1 he
    refine hf (Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, ?_⟩))
    rw [resEdgeSet, Finset.mem_filter, hexTup_embTup]
    exact ⟨Finset.mem_univ _, heR⟩
  obtain ⟨a, C, hdata⟩ := hres (f : Fin 6 → V) hx (fun i => Finset.mem_univ _) hdisj
  refine hf (Finset.mem_union_left _ ?_)
  rw [hexCovered, Finset.mem_filter, hexTup_embTup]
  exact ⟨Finset.mem_univ _, a, C, hdata⟩

/-- **The hexagon reservoir does not exist.**  A sparse cluster family fails
`BKLO.HexWebReservoir`: the octahedron trade of `BKLO/HexagonWeb.lean` closes the six-cycle case
locally, but no sparse reservoir carries its overlap structure — already its chain is too much. -/
theorem not_hexWebReservoir {E : Finset (Sym2 V)} {𝒞 : Finset (Finset V)} {d : ℕ}
    (h𝒞 : ClusterFamilyIn E 𝒞) (hd : ∀ v : V, edeg (famEdges 𝒞) v ≤ d)
    (hdn : 1000 * d ≤ Fintype.card V) (hn : 4000 ≤ Fintype.card V) :
    ¬ HexWebReservoir 𝒞 (Finset.univ : Finset V) := by
  intro hres
  refine not_hexChainReservoir h𝒞 hd hdn hn ?_
  intro x hx hxS hdisj
  obtain ⟨a, C, D, hdata⟩ := hres x hx hxS hdisj
  exact ⟨a, C, hdata.hexChain⟩

/-! ### The strengthening of the reservoir is impossible -/

/-- **The reservoir existence statement strengthened by the hexagon demand.**  This is
`BKLO.ClusterReservoirExistence` with pair covering replaced by `BKLO.HexWebReservoir`: what the
six-cycle gadget of `BKLO/HexagonWeb.lean` would need. -/
def ClusterReservoirHexWeb : Prop :=
  ∀ γ : ℝ, 0 < γ → ∃ n₀ : ℕ,
    ∀ {V : Type} [DecidableEq V] (E : Finset (Sym2 V)) (S : Finset V),
      n₀ ≤ S.card → E ⊆ cliqueEdges S →
      (∀ v ∈ S, (9 / 10 + γ) * (S.card : ℝ) ≤ (edeg E v : ℝ)) →
      ∃ 𝒞 : Finset (Finset V), ClusterFamilyIn E 𝒞 ∧
        (∀ v : V, (edeg (famEdges 𝒞) v : ℝ) ≤ γ * (S.card : ℝ)) ∧ HexWebReservoir 𝒞 S

/-- **`BKLO.ClusterReservoirHexWeb` is false.**  Take the host to be a complete graph on `n`
vertices and `γ = 1/1000`; whatever cluster reservoir of maximum degree `γ n` is reserved,
`BKLO.not_hexWebReservoir` produces a six-cycle of unreserved edges that the reservoir cannot
serve.

So the hexagon gadget, which absorbs a six-cycle leftover once the reservoir carries its overlap
structure (`BKLO.triDecomp_hex_absorb`), cannot be supplied by any sparse reservoir: the demand is
a closed six-walk of clusters through six prescribed vertices, of which a reservoir of maximum
degree `γ|S|` has only `O(γ⁵|S|⁶)` — against the `|S|⁶` six-cycles that may carry the leftover. -/
theorem not_clusterReservoirHexWeb : ¬ ClusterReservoirHexWeb := by
  classical
  intro hCR
  obtain ⟨n₀, hres⟩ := hCR (1 / 1000 : ℝ) (by norm_num)
  set n := max n₀ 4000 with hndef
  have hn4000 : 4000 ≤ n := le_max_right _ _
  have hnn₀ : n₀ ≤ n := le_max_left _ _
  have hcardfin : (Finset.univ : Finset (Fin n)).card = n := by simp
  have hdegE : ∀ v ∈ (Finset.univ : Finset (Fin n)),
      (9 / 10 + (1 / 1000 : ℝ)) * ((Finset.univ : Finset (Fin n)).card : ℝ) ≤
        (edeg (cliqueEdges (Finset.univ : Finset (Fin n))) v : ℝ) := by
    intro v _
    have hv : edeg (cliqueEdges (Finset.univ : Finset (Fin n))) v = n - 1 := by
      rw [edeg_cliqueEdges_card v, if_pos (Finset.mem_univ v), hcardfin]
    rw [hv, hcardfin]
    have h1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      have h : (1 : ℕ) ≤ n := by omega
      push_cast [Nat.cast_sub h]
      ring
    rw [h1]
    have hn : (4000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn4000
    linarith
  obtain ⟨𝒞, hfam, hdeg, hhex⟩ :=
    hres (V := Fin n) (cliqueEdges (Finset.univ : Finset (Fin n))) Finset.univ
      (by rw [hcardfin]; exact hnn₀) (Finset.Subset.refl _) hdegE
  set d := n / 1000 with hddef
  have hd : ∀ v : Fin n, edeg (famEdges 𝒞) v ≤ d := by
    intro v
    have h := hdeg v
    rw [hcardfin] at h
    have h' : (1000 : ℝ) * (edeg (famEdges 𝒞) v : ℝ) ≤ (n : ℝ) := by linarith
    have h'' : 1000 * edeg (famEdges 𝒞) v ≤ n := by exact_mod_cast h'
    rw [hddef, Nat.le_div_iff_mul_le (by norm_num : 0 < 1000)]
    omega
  have hcardV : Fintype.card (Fin n) = n := by simp
  exact not_hexWebReservoir hfam hd (by rw [hcardV, hddef]; omega) (by rw [hcardV]; exact hn4000)
    hhex

end BKLO
