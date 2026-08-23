/-
# Nibble — the **cluster-level integral-packing route** to the fine block residual is a dead end

`Nibble.AX1.BlockCoverResidualFine` (`Nibble.CoreGapBlockCover`) is the last open atom of the
deterministic route to AX1: for every accuracy `ε`, density threshold `δ ≤ ε` and (fine) relative
block size `α ≤ ε ^ 2`, every regularity-reduced graph must admit a family of block sub-triples with
pairwise disjoint vertex-pair rectangles whose density-weighted area recovers `ν₃*` up to `ε|V|²`.

A tempting way to build such a family is to work **cluster-edge-disjointly**: pick an integral
(edge-disjoint) triangle packing of the cluster graph and allocate blocks only inside the cluster
triples of that packing, so that every cluster pair carries the blocks of a single cluster triple.
This file shows, machine-checked, that this route **cannot** close the residual: the extra clause
"two members of the family have either the same cluster triple, or cluster triples meeting in at
most one cluster" already makes the statement false.

* `Nibble.AX1.BlockCoverResidualFineClusterPacking` — the fine residual with that extra clause;
* `Nibble.AX1.blockCoverResidualFine_of_clusterPacking` — it is a strengthening of the residual;
* `Nibble.AX1.not_blockCoverResidualFineClusterPacking` — and it is **false**.

The witness is the complete graph on `5N` vertices with the equipartition into five clusters of
size `N`, at `ε = δ = 1/1000`, `α = 10⁻⁷`, `T₀ = ε₁ = 1` (five clusters are admissible because
`4/ε₁ = 4 ≤ 5`).  Three `3`-subsets of a `5`-set can never pairwise meet in at most one element
(`Nibble.AX1.no_three_sparse_triples`), so a cluster-edge-disjoint family lives on at most **two**
cluster triples; the rectangles of the members sitting on one cluster triple are disjoint subsets of
the square of the union of its three clusters, of area `(3N)²`, so the whole family has covering
area at most `9N²` and covering sum at most `3N²`
(`Nibble.AX1.clusterPacking_family_bound`).  But the reduced graph is the complete `5`-partite
graph, whose fractional triangle packing number is at least `10N²/3`
(`Nibble.AX1.nu3star_fivePartite_ge`), and `10/3 > 3 + 1000⁻¹·25`.

The obstruction is not an artefact of five clusters.  For a cluster-edge-disjoint family the value
of a cluster triple is capped by the *smallest* of its three cluster-pair densities, whereas the
capacity LP that `ν₃*` of the reduced graph attains pays the *average*; already for the complete
graph the fractional triangle packing number of the cluster graph `K₅` (`10/3`) exceeds its integral
one (`2`).  A family that closes the fine residual must therefore put blocks of **several** cluster
triples inside one cluster pair — which is exactly what the global block design
(`Nibble.AX1.triPairSet_disjoint`, `Nibble.AX1.tripleRect_disjoint_of_design`) is for.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.CoreGapBlockCoverRefute

open Finset SimpleGraph Hypergraph Nibble.YusterE

namespace Nibble.AX1

/-! ### Disjoint rectangles inside a prescribed square -/

/-- **The areas of pairwise disjoint rectangles inside `Om ×ˢ Om` add up to at most `#Om ^ 2`.** -/
theorem sum_area_le_of_rect_subset {V : Type} [Fintype V] [DecidableEq V]
    (A B C : ℕ → Finset V) (F : Finset ℕ) (Om : Finset V)
    (hAB : ∀ i ∈ F, Disjoint (A i) (B i)) (hAC : ∀ i ∈ F, Disjoint (A i) (C i))
    (hBC : ∀ i ∈ F, Disjoint (B i) (C i))
    (hsub : ∀ i ∈ F, tripleRect (A i) (B i) (C i) ⊆ Om ×ˢ Om)
    (hdisj : ∀ i ∈ F, ∀ j ∈ F, i ≠ j →
      Disjoint (tripleRect (A i) (B i) (C i)) (tripleRect (A j) (B j) (C j))) :
    2 * ∑ i ∈ F, (#(A i) * #(B i) + #(A i) * #(C i) + #(B i) * #(C i)) ≤ #Om * #Om := by
  classical
  have hpair : ((F : Finset ℕ) : Set ℕ).PairwiseDisjoint
      (fun i => tripleRect (A i) (B i) (C i)) := by
    intro i hi j hj hij
    exact hdisj i hi j hj hij
  have hsum : ∑ i ∈ F, #(tripleRect (A i) (B i) (C i))
      = #(F.biUnion (fun i => tripleRect (A i) (B i) (C i))) :=
    (Finset.card_biUnion hpair).symm
  have hle : #(F.biUnion (fun i => tripleRect (A i) (B i) (C i))) ≤ #(Om ×ˢ Om) := by
    refine Finset.card_le_card ?_
    intro z hz
    rw [Finset.mem_biUnion] at hz
    obtain ⟨i, hi, hz⟩ := hz
    exact hsub i hi hz
  have hterm : ∀ i ∈ F, #(tripleRect (A i) (B i) (C i))
      = 2 * (#(A i) * #(B i) + #(A i) * #(C i) + #(B i) * #(C i)) := fun i hi =>
    card_tripleRect (hAB i hi) (hAC i hi) (hBC i hi)
  calc 2 * ∑ i ∈ F, (#(A i) * #(B i) + #(A i) * #(C i) + #(B i) * #(C i))
      = ∑ i ∈ F, #(tripleRect (A i) (B i) (C i)) := by
        rw [Finset.mul_sum]
        exact (Finset.sum_congr rfl hterm).symm
    _ = #(F.biUnion (fun i => tripleRect (A i) (B i) (C i))) := hsum
    _ ≤ #(Om ×ˢ Om) := hle
    _ = #Om * #Om := by rw [Finset.card_product]

/-! ### The value of a cluster triple is capped by each of its cluster-pair capacities

The block sizes of `Nibble.AX1.IsGridSubTriple` are tuned to the density of the *opposite* pair
(`#A ≈ τ·d(W,X)`, `#B ≈ τ·d(U,X)`, `#C ≈ τ·d(U,W)`), so each of the three summands of the covering
sum of a sub-triple equals `τ²·d(U,W)·d(U,X)·d(W,X)` up to `O(τ)`.  Consequently the covering sum of
a family living on ONE cluster triple is capped, up to a lower-order term, by `d(U,W)·#U·#W` — and
by symmetry by the analogous quantity for each of the three cluster pairs, hence by the *smallest*
of them.  This is exactly the accounting that makes a cluster-edge-disjoint family lose a constant
factor against the capacity LP that `ν₃*` of the reduced graph attains: a fixed cluster triple can
never be worth more than its sparsest pair, while the LP pays each pair separately. -/

/-- **The covering sum of a family of block sub-triples on one cluster triple is capped by the
capacity `d(U,W)·#U·#W` of any one of its cluster pairs**, up to the quantisation term
`⅔·#F·(#U + #W)`. -/
theorem cover_sum_le_pair_capacity {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (P : Finpartition (univ : Finset V))
    {ep δ α τ : ℝ} {U W X : Finset V} {A B C : ℕ → Finset V} (F : Finset ℕ)
    (hgrid : ∀ i ∈ F, IsGridSubTriple G P ep δ α τ U W X (A i) (B i) (C i))
    (hdisj : ∀ i ∈ F, ∀ j ∈ F, i ≠ j →
      Disjoint (tripleRect (A i) (B i) (C i)) (tripleRect (A j) (B j) (C j))) :
    ∑ i ∈ F, ((G.edgeDensity U W : ℝ) * (#(A i) : ℝ) * (#(B i) : ℝ)
        + (G.edgeDensity U X : ℝ) * (#(A i) : ℝ) * (#(C i) : ℝ)
        + (G.edgeDensity W X : ℝ) * (#(B i) : ℝ) * (#(C i) : ℝ)) / 3
      ≤ (G.edgeDensity U W : ℝ) * (#U : ℝ) * (#W : ℝ)
        + 2 / 3 * (#F : ℝ) * ((#U : ℝ) + (#W : ℝ)) := by
  classical
  set dUW : ℝ := (G.edgeDensity U W : ℝ) with hdUW
  set dUX : ℝ := (G.edgeDensity U X : ℝ) with hdUX
  set dWX : ℝ := (G.edgeDensity W X : ℝ) with hdWX
  have hdUW0 : 0 ≤ dUW := by rw [hdUW]; exact_mod_cast G.edgeDensity_nonneg U W
  have hdUX0 : 0 ≤ dUX := by rw [hdUX]; exact_mod_cast G.edgeDensity_nonneg U X
  have hdWX0 : 0 ≤ dWX := by rw [hdWX]; exact_mod_cast G.edgeDensity_nonneg W X
  have hdUW1 : dUW ≤ 1 := by rw [hdUW]; exact_mod_cast G.edgeDensity_le_one U W
  have hdUX1 : dUX ≤ 1 := by rw [hdUX]; exact_mod_cast G.edgeDensity_le_one U X
  have hdWX1 : dWX ≤ 1 := by rw [hdWX]; exact_mod_cast G.edgeDensity_le_one W X
  -- the per-member comparison of the three summands
  have hterm : ∀ i ∈ F, (dUW * (#(A i) : ℝ) * (#(B i) : ℝ) + dUX * (#(A i) : ℝ) * (#(C i) : ℝ)
      + dWX * (#(B i) : ℝ) * (#(C i) : ℝ)) / 3
      ≤ dUW * (#(A i) : ℝ) * (#(B i) : ℝ) + 2 / 3 * ((#U : ℝ) + (#W : ℝ)) := by
    intro i hi
    obtain ⟨-, hAU, hBW, -, -, -, -, hsA, hsB, hsC⟩ := hgrid i hi
    have hA1 : τ * dWX - 1 ≤ (#(A i) : ℝ) := by
      have := (abs_le.mp hsA).1; rw [hdWX]; linarith only [this]
    have hB1 : τ * dUX - 1 ≤ (#(B i) : ℝ) := by
      have := (abs_le.mp hsB).1; rw [hdUX]; linarith only [this]
    have hC1 : (#(C i) : ℝ) ≤ τ * dUW + 1 := by
      have := (abs_le.mp hsC).2; rw [hdUW]; linarith only [this]
    have hA0 : (0:ℝ) ≤ (#(A i) : ℝ) := Nat.cast_nonneg _
    have hB0 : (0:ℝ) ≤ (#(B i) : ℝ) := Nat.cast_nonneg _
    have hAU' : (#(A i) : ℝ) ≤ (#U : ℝ) := by exact_mod_cast Finset.card_le_card hAU
    have hBW' : (#(B i) : ℝ) ≤ (#W : ℝ) := by exact_mod_cast Finset.card_le_card hBW
    -- `dUX·#C ≤ dUW·#B + 2` and `dWX·#C ≤ dUW·#A + 2`
    have h1 : dUX * (#(C i) : ℝ) ≤ dUW * (#(B i) : ℝ) + 2 := by nlinarith only [hdUW0, hdUX0, hdUW1, hdUX1, hB1, hC1]
    have h2 : dWX * (#(C i) : ℝ) ≤ dUW * (#(A i) : ℝ) + 2 := by nlinarith
    have h3 : dUX * (#(A i) : ℝ) * (#(C i) : ℝ)
        ≤ dUW * (#(A i) : ℝ) * (#(B i) : ℝ) + 2 * (#U : ℝ) := by nlinarith
    have h4 : dWX * (#(B i) : ℝ) * (#(C i) : ℝ)
        ≤ dUW * (#(A i) : ℝ) * (#(B i) : ℝ) + 2 * (#W : ℝ) := by nlinarith
    linarith
  -- the rectangles of the pair `(U, W)` are disjoint subsets of `U ×ˢ W`
  have hrect : ∑ i ∈ F, (#(A i) : ℝ) * (#(B i) : ℝ) ≤ (#U : ℝ) * (#W : ℝ) := by
    have hpd : ((F : Finset ℕ) : Set ℕ).PairwiseDisjoint (fun i => A i ×ˢ B i) := by
      intro i hi j hj hij
      exact Finset.disjoint_of_subset_left prod_subset_tripleRect_AB
        (Finset.disjoint_of_subset_right prod_subset_tripleRect_AB (hdisj i hi j hj hij))
    have hsum : ∑ i ∈ F, #(A i ×ˢ B i) = #(F.biUnion (fun i => A i ×ˢ B i)) :=
      (Finset.card_biUnion hpd).symm
    have hsub : F.biUnion (fun i => A i ×ˢ B i) ⊆ U ×ˢ W := by
      intro z hz
      rw [Finset.mem_biUnion] at hz
      obtain ⟨i, hi, hz⟩ := hz
      obtain ⟨-, hAU, hBW, -, -, -, -, -, -, -⟩ := hgrid i hi
      rw [Finset.mem_product] at hz ⊢
      exact ⟨hAU hz.1, hBW hz.2⟩
    have hnat : ∑ i ∈ F, #(A i) * #(B i) ≤ #U * #W := by
      have h1 : ∑ i ∈ F, #(A i) * #(B i) = ∑ i ∈ F, #(A i ×ˢ B i) :=
        Finset.sum_congr rfl (fun i _ => (Finset.card_product _ _).symm)
      rw [h1, hsum, ← Finset.card_product]
      exact Finset.card_le_card hsub
    have := (Nat.cast_le (α := ℝ)).mpr hnat
    push_cast at this
    exact this
  calc ∑ i ∈ F, (dUW * (#(A i) : ℝ) * (#(B i) : ℝ) + dUX * (#(A i) : ℝ) * (#(C i) : ℝ)
        + dWX * (#(B i) : ℝ) * (#(C i) : ℝ)) / 3
      ≤ ∑ i ∈ F, (dUW * (#(A i) : ℝ) * (#(B i) : ℝ) + 2 / 3 * ((#U : ℝ) + (#W : ℝ))) :=
        Finset.sum_le_sum hterm
    _ = dUW * ∑ i ∈ F, (#(A i) : ℝ) * (#(B i) : ℝ)
          + (#F : ℝ) * (2 / 3 * ((#U : ℝ) + (#W : ℝ))) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.mul_sum]
        congr 1
        exact Finset.sum_congr rfl (fun i _ => by ring)
    _ ≤ dUW * ((#U : ℝ) * (#W : ℝ)) + (#F : ℝ) * (2 / 3 * ((#U : ℝ) + (#W : ℝ))) := by
        have := mul_le_mul_of_nonneg_left hrect hdUW0
        linarith
    _ = dUW * (#U : ℝ) * (#W : ℝ) + 2 / 3 * (#F : ℝ) * ((#U : ℝ) + (#W : ℝ)) := by ring

/-! ### Three `3`-subsets of a `5`-set always share a pair -/

set_option maxRecDepth 100000 in
/-- **Three distinct `3`-subsets of a `5`-set cannot pairwise meet in at most one element.**  In
cluster language: an edge-disjoint triangle packing of a graph on five clusters has at most two
triangles. -/
theorem no_three_sparse_triples : ∀ s t r : Finset (Fin 5),
    ¬ (#s = 3 ∧ #t = 3 ∧ #r = 3 ∧ s ≠ t ∧ s ≠ r ∧ t ≠ r ∧
      #(s ∩ t) ≤ 1 ∧ #(s ∩ r) ≤ 1 ∧ #(t ∩ r) ≤ 1) := by decide +kernel

/-! ### The clusters of a block sub-triple of the five-cluster complete graph -/

/-- The three clusters of a block sub-triple of the complete graph on the five clusters are three
different clusters, and the three blocks sit inside them. -/
theorem grid_clusters (N : ℕ) (hN : 0 < N) {δ α τ : ℝ} {U W X A B C : Finset (Fin 5 × Fin N)}
    (h : IsGridSubTriple (⊤ : SimpleGraph (Fin 5 × Fin N)) (cpartition N hN) (1 / 8) δ α τ
      U W X A B C) :
    ∃ a b c : Fin 5, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ U = cpart N a ∧ W = cpart N b ∧ X = cpart N c ∧
      A ⊆ cpart N a ∧ B ⊆ cpart N b ∧ C ⊆ cpart N c := by
  obtain ⟨hgood, hAU, hBW, hCX, -, -, -, -, -, -⟩ := h
  obtain ⟨hU, hW, hX, hUW, hUX, hWX, -, -, -, -, -, -⟩ := hgood
  rw [cpartition_parts] at hU hW hX
  obtain ⟨a, rfl⟩ := mem_cparts.mp hU
  obtain ⟨b, rfl⟩ := mem_cparts.mp hW
  obtain ⟨c, rfl⟩ := mem_cparts.mp hX
  exact ⟨a, b, c, fun h => hUW (by rw [h]), fun h => hUX (by rw [h]), fun h => hWX (by rw [h]),
    rfl, rfl, rfl, hAU, hBW, hCX⟩

/-- Every cluster pair of the complete graph has density `1`, so the density-weighted covering sum
of a family of block sub-triples is exactly its area. -/
theorem cover_sum_eq_area_gen (N : ℕ) (hN : 0 < N) {δ α τ : ℝ} {k : ℕ}
    (U W X A B C : ℕ → Finset (Fin 5 × Fin N))
    (hgrid : ∀ i < k, IsGridSubTriple (⊤ : SimpleGraph (Fin 5 × Fin N)) (cpartition N hN)
      (1 / 8) δ α τ (U i) (W i) (X i) (A i) (B i) (C i)) :
    ∑ i ∈ Finset.range k,
        (((⊤ : SimpleGraph (Fin 5 × Fin N)).edgeDensity (U i) (W i) : ℝ) * (#(A i) : ℝ)
            * (#(B i) : ℝ)
          + ((⊤ : SimpleGraph (Fin 5 × Fin N)).edgeDensity (U i) (X i) : ℝ) * (#(A i) : ℝ)
            * (#(C i) : ℝ)
          + ((⊤ : SimpleGraph (Fin 5 × Fin N)).edgeDensity (W i) (X i) : ℝ) * (#(B i) : ℝ)
            * (#(C i) : ℝ))
      = ∑ i ∈ Finset.range k,
        ((#(A i) : ℝ) * #(B i) + (#(A i) : ℝ) * #(C i) + (#(B i) : ℝ) * #(C i)) := by
  refine Finset.sum_congr rfl (fun i hi => ?_)
  obtain ⟨a, b, c, hab, hac, hbc, hU, hW, hX, -, -, -⟩ :=
    grid_clusters N hN (hgrid i (Finset.mem_range.mp hi))
  have d1 : ((⊤ : SimpleGraph (Fin 5 × Fin N)).edgeDensity (U i) (W i) : ℝ) = 1 := by
    rw [hU, hW, top_edgeDensity (cpart_disjoint hab) (cpart_nonempty hN a) (cpart_nonempty hN b)]
    norm_num
  have d2 : ((⊤ : SimpleGraph (Fin 5 × Fin N)).edgeDensity (U i) (X i) : ℝ) = 1 := by
    rw [hU, hX, top_edgeDensity (cpart_disjoint hac) (cpart_nonempty hN a) (cpart_nonempty hN c)]
    norm_num
  have d3 : ((⊤ : SimpleGraph (Fin 5 × Fin N)).edgeDensity (W i) (X i) : ℝ) = 1 := by
    rw [hW, hX, top_edgeDensity (cpart_disjoint hbc) (cpart_nonempty hN b) (cpart_nonempty hN c)]
    norm_num
  rw [d1, d2, d3]
  ring

/-! ### The residual restricted to cluster-edge-disjoint families -/

/-- **The fine block-allocation residual, restricted to cluster-edge-disjoint families.**  Same as
`Nibble.AX1.BlockCoverResidualFine`, with the extra requirement that two members of the family carry
either the same cluster triple or cluster triples meeting in at most one cluster — i.e. that the
cluster triples used form an *integral (edge-disjoint) triangle packing* of the cluster graph. -/
def BlockCoverResidualFineClusterPacking : Prop :=
  ∀ ε δ α T₀ ε₁ : ℝ, 0 < ε → 0 < δ → δ ≤ 1 → δ ≤ ε → 0 < α → α ≤ δ / 2 → α ≤ ε ^ 2 →
    0 < T₀ → 0 < ε₁ → ε₁ ≤ 1 →
  ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finpartition (univ : Finset V)),
    n₀ ≤ Fintype.card V →
    P.IsEquipartition →
    4 / ε₁ ≤ (P.parts.card : ℝ) →
    (P.parts.card : ℝ) ≤ ((SzemerediRegularity.bound (ε₁ / 8) ⌈4 / ε₁⌉₊ : ℕ) : ℝ) →
    P.IsUniform G (ε₁ / 8) →
    ∃ (τ : ℝ) (k : ℕ) (U W X A B C : ℕ → Finset V),
      T₀ ≤ τ ∧
      (∀ i < k, IsGridSubTriple G P (ε₁ / 8) δ α τ (U i) (W i) (X i) (A i) (B i) (C i)) ∧
      (∀ i < k, ∀ j < k, i ≠ j →
        Disjoint (tripleRect (A i) (B i) (C i)) (tripleRect (A j) (B j) (C j))) ∧
      (∀ i < k, ∀ j < k,
        ({U i, W i, X i} : Finset (Finset V)) = ({U j, W j, X j} : Finset (Finset V)) ∨
        #(({U i, W i, X i} : Finset (Finset V)) ∩ ({U j, W j, X j} : Finset (Finset V))) ≤ 1) ∧
      nu3star (G.regularityReduced P (ε₁ / 8) (ε₁ / 4))
        ≤ (∑ i ∈ Finset.range k,
            ((G.edgeDensity (U i) (W i) : ℝ) * (#(A i) : ℝ) * (#(B i) : ℝ)
              + (G.edgeDensity (U i) (X i) : ℝ) * (#(A i) : ℝ) * (#(C i) : ℝ)
              + (G.edgeDensity (W i) (X i) : ℝ) * (#(B i) : ℝ) * (#(C i) : ℝ))) / 3
          + ε * (Fintype.card V : ℝ) ^ 2

/-- The cluster-edge-disjoint route is a **strengthening** of the fine residual: forgetting the
extra clause gives `Nibble.AX1.BlockCoverResidualFine`. -/
theorem blockCoverResidualFine_of_clusterPacking (h : BlockCoverResidualFineClusterPacking) :
    BlockCoverResidualFine := by
  intro ε δ α T₀ ε₁ hε hδ hδ1 hδε hα hαδ hαε hT₀ hε₁ hε₁1
  obtain ⟨n₀, hn₀⟩ := h ε δ α T₀ ε₁ hε hδ hδ1 hδε hα hαδ hαε hT₀ hε₁ hε₁1
  refine ⟨n₀, ?_⟩
  intro V _ _ G _ P hcard hequi hlow hhigh huni
  obtain ⟨τ, k, U, W, X, A, B, C, hτ, hgrid, hdisj, -, hcov⟩ :=
    hn₀ V G P hcard hequi hlow hhigh huni
  exact ⟨τ, k, U, W, X, A, B, C, hτ, hgrid, hdisj, hcov⟩

/-! ### A cluster-edge-disjoint family lives on at most two cluster triples -/

set_option maxHeartbeats 1000000 in
/-- **The covering area of a cluster-edge-disjoint family of block sub-triples of the five-cluster
complete graph is at most `9N²`.**  Its members live on at most two cluster triples
(`Nibble.AX1.no_three_sparse_triples`), and the rectangles sitting on one cluster triple are
pairwise disjoint subsets of the square of the union of its three clusters. -/
theorem clusterPacking_family_bound (N : ℕ) (hN : 0 < N) {δ α τ : ℝ} {k : ℕ}
    (U W X A B C : ℕ → Finset (Fin 5 × Fin N))
    (hgrid : ∀ i < k, IsGridSubTriple (⊤ : SimpleGraph (Fin 5 × Fin N)) (cpartition N hN)
      (1 / 8) δ α τ (U i) (W i) (X i) (A i) (B i) (C i))
    (hdisj : ∀ i < k, ∀ j < k, i ≠ j →
      Disjoint (tripleRect (A i) (B i) (C i)) (tripleRect (A j) (B j) (C j)))
    (hpack : ∀ i < k, ∀ j < k,
      ({U i, W i, X i} : Finset (Finset (Fin 5 × Fin N)))
          = ({U j, W j, X j} : Finset (Finset (Fin 5 × Fin N))) ∨
      #(({U i, W i, X i} : Finset (Finset (Fin 5 × Fin N)))
          ∩ ({U j, W j, X j} : Finset (Finset (Fin 5 × Fin N)))) ≤ 1) :
    ∑ i ∈ Finset.range k,
        ((#(A i) : ℝ) * #(B i) + (#(A i) : ℝ) * #(C i) + (#(B i) : ℝ) * #(C i))
      ≤ 9 * (N : ℝ) ^ 2 := by
  classical
  have hNR : (0:ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hcpart_inj : Function.Injective (cpart N) := by
    intro a b hab
    have : (⟨a, ⟨0, hN⟩⟩ : Fin 5 × Fin N) ∈ cpart N b := hab ▸ mem_cpart.mpr rfl
    exact mem_cpart.mp this
  -- the index triple of a member
  set idx : ℕ → Finset (Fin 5) :=
    fun i => {partIdx (U i), partIdx (W i), partIdx (X i)} with hidx
  -- the data of one member
  have hdata : ∀ i < k, #(idx i) = 3 ∧
      ({U i, W i, X i} : Finset (Finset (Fin 5 × Fin N))) = (idx i).image (cpart N) ∧
      A i ⊆ (idx i).biUnion (cpart N) ∧ B i ⊆ (idx i).biUnion (cpart N) ∧
      C i ⊆ (idx i).biUnion (cpart N) ∧
      Disjoint (A i) (B i) ∧ Disjoint (A i) (C i) ∧ Disjoint (B i) (C i) := by
    intro i hi
    obtain ⟨a, b, c, hab, hac, hbc, hU, hW, hX, hA, hB, hC⟩ := grid_clusters N hN (hgrid i hi)
    have hpa : partIdx (U i) = a := by rw [hU]; exact partIdx_cpart N hN a
    have hpb : partIdx (W i) = b := by rw [hW]; exact partIdx_cpart N hN b
    have hpc : partIdx (X i) = c := by rw [hX]; exact partIdx_cpart N hN c
    have hidxi : idx i = ({a, b, c} : Finset (Fin 5)) := by
      simp only [hidx, hpa, hpb, hpc]
    have hmemA : ∀ v ∈ cpart N a, v ∈ (idx i).biUnion (cpart N) := by
      intro v hv; rw [hidxi]; exact Finset.mem_biUnion.mpr ⟨a, by simp, hv⟩
    have hmemB : ∀ v ∈ cpart N b, v ∈ (idx i).biUnion (cpart N) := by
      intro v hv; rw [hidxi]; exact Finset.mem_biUnion.mpr ⟨b, by simp, hv⟩
    have hmemC : ∀ v ∈ cpart N c, v ∈ (idx i).biUnion (cpart N) := by
      intro v hv; rw [hidxi]; exact Finset.mem_biUnion.mpr ⟨c, by simp, hv⟩
    refine ⟨?_, ?_, fun v hv => hmemA v (hA hv), fun v hv => hmemB v (hB hv),
      fun v hv => hmemC v (hC hv), ?_, ?_, ?_⟩
    · rw [hidxi, Finset.card_insert_of_notMem (by simp [hab, hac]),
        Finset.card_insert_of_notMem (by simp [hbc]), Finset.card_singleton]
    · rw [hidxi, hU, hW, hX]
      simp [Finset.image_insert]
    · exact Finset.disjoint_of_subset_left hA
        (Finset.disjoint_of_subset_right hB (cpart_disjoint hab))
    · exact Finset.disjoint_of_subset_left hA
        (Finset.disjoint_of_subset_right hC (cpart_disjoint hac))
    · exact Finset.disjoint_of_subset_left hB
        (Finset.disjoint_of_subset_right hC (cpart_disjoint hbc))
  -- the index triples of the family
  set S : Finset (Finset (Fin 5)) := (Finset.range k).image idx with hS
  have hmaps : ∀ i ∈ Finset.range k, idx i ∈ S := fun i hi => Finset.mem_image_of_mem _ hi
  have hcard3 : ∀ s ∈ S, #s = 3 := by
    intro s hs
    rw [hS, Finset.mem_image] at hs
    obtain ⟨i, hi, rfl⟩ := hs
    exact (hdata i (Finset.mem_range.mp hi)).1
  have hsparse : ∀ s ∈ S, ∀ t ∈ S, s = t ∨ #(s ∩ t) ≤ 1 := by
    intro s hs t ht
    rw [hS, Finset.mem_image] at hs ht
    obtain ⟨i, hi, rfl⟩ := hs
    obtain ⟨j, hj, rfl⟩ := ht
    have hi' := Finset.mem_range.mp hi
    have hj' := Finset.mem_range.mp hj
    have hIi := (hdata i hi').2.1
    have hIj := (hdata j hj').2.1
    rcases hpack i hi' j hj' with heq | hle
    · left
      rw [hIi, hIj] at heq
      exact Finset.image_injective hcpart_inj heq
    · right
      rw [hIi, hIj, ← Finset.image_inter _ _ hcpart_inj,
        Finset.card_image_of_injective _ hcpart_inj] at hle
      exact hle
  have hS2 : #S ≤ 2 := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨T, hTS, hT3⟩ := Finset.exists_subset_card_eq (show 3 ≤ #S by omega)
    obtain ⟨s, t, r, hst, hsr, htr, rfl⟩ := Finset.card_eq_three.mp hT3
    have hs : s ∈ S := hTS (by simp)
    have ht : t ∈ S := hTS (by simp)
    have hr : r ∈ S := hTS (by simp)
    have h1 : #(s ∩ t) ≤ 1 := (hsparse s hs t ht).resolve_left hst
    have h2 : #(s ∩ r) ≤ 1 := (hsparse s hs r hr).resolve_left hsr
    have h3 : #(t ∩ r) ≤ 1 := (hsparse t ht r hr).resolve_left htr
    exact no_three_sparse_triples s t r
      ⟨hcard3 s hs, hcard3 t ht, hcard3 r hr, hst, hsr, htr, h1, h2, h3⟩
  -- the covering area of the members living on one index triple
  have hfiber : ∀ s ∈ S,
      ∑ i ∈ (Finset.range k).filter (fun i => idx i = s),
          ((#(A i) : ℝ) * #(B i) + (#(A i) : ℝ) * #(C i) + (#(B i) : ℝ) * #(C i))
        ≤ 9 * (N : ℝ) ^ 2 / 2 := by
    intro s hs
    set F : Finset ℕ := (Finset.range k).filter (fun i => idx i = s) with hF
    have hFsub : ∀ i ∈ F, i < k ∧ idx i = s := by
      intro i hi
      rw [hF, Finset.mem_filter, Finset.mem_range] at hi
      exact hi
    set Om : Finset (Fin 5 × Fin N) := s.biUnion (cpart N) with hOm
    have hOmcard : #Om ≤ 3 * N := by
      have h1 : #Om ≤ ∑ p ∈ s, #(cpart N p) := Finset.card_biUnion_le
      have h2 : ∑ p ∈ s, #(cpart N p) = 3 * N := by
        rw [Finset.sum_congr rfl (fun p _ => card_cpart N p), Finset.sum_const, smul_eq_mul,
          hcard3 s hs]
      omega
    have hnat : 2 * ∑ i ∈ F, (#(A i) * #(B i) + #(A i) * #(C i) + #(B i) * #(C i))
        ≤ #Om * #Om := by
      refine sum_area_le_of_rect_subset A B C F Om
        (fun i hi => (hdata i (hFsub i hi).1).2.2.2.2.2.1)
        (fun i hi => (hdata i (hFsub i hi).1).2.2.2.2.2.2.1)
        (fun i hi => (hdata i (hFsub i hi).1).2.2.2.2.2.2.2)
        (fun i hi => ?_) (fun i hi j hj hij => hdisj i (hFsub i hi).1 j (hFsub j hj).1 hij)
      obtain ⟨hik, hidxs⟩ := hFsub i hi
      obtain ⟨-, -, hA, hB, hC, -, -, -⟩ := hdata i hik
      rw [hidxs] at hA hB hC
      rintro ⟨x, y⟩ hz
      rw [mem_tripleRect_iff] at hz
      have hmem : ∀ z : Fin 5 × Fin N, (z ∈ A i ∨ z ∈ B i ∨ z ∈ C i) → z ∈ Om := by
        rintro z (h | h | h)
        · exact hA h
        · exact hB h
        · exact hC h
      rw [Finset.mem_product]
      rcases hz with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨hmem x (Or.inl h1), hmem y (Or.inr (Or.inl h2))⟩
      · exact ⟨hmem x (Or.inr (Or.inl h1)), hmem y (Or.inl h2)⟩
      · exact ⟨hmem x (Or.inl h1), hmem y (Or.inr (Or.inr h2))⟩
      · exact ⟨hmem x (Or.inr (Or.inr h1)), hmem y (Or.inl h2)⟩
      · exact ⟨hmem x (Or.inr (Or.inl h1)), hmem y (Or.inr (Or.inr h2))⟩
      · exact ⟨hmem x (Or.inr (Or.inr h1)), hmem y (Or.inr (Or.inl h2))⟩
    have hnat2 : 2 * ∑ i ∈ F, (#(A i) * #(B i) + #(A i) * #(C i) + #(B i) * #(C i))
        ≤ 9 * (N * N) := by
      refine le_trans hnat ?_
      calc #Om * #Om ≤ (3 * N) * (3 * N) := Nat.mul_le_mul hOmcard hOmcard
        _ = 9 * (N * N) := by ring
    have hcast : (2 : ℝ) * ∑ i ∈ F,
        ((#(A i) : ℝ) * #(B i) + (#(A i) : ℝ) * #(C i) + (#(B i) : ℝ) * #(C i))
        ≤ 9 * ((N : ℝ) * N) := by
      have h := (Nat.cast_le (α := ℝ)).mpr hnat2
      push_cast at h
      linarith only [h]
    nlinarith only [hcast]
  -- splitting the family into its index-triple fibres
  have hsplit : ∑ s ∈ S, ∑ i ∈ (Finset.range k).filter (fun i => idx i = s),
        ((#(A i) : ℝ) * #(B i) + (#(A i) : ℝ) * #(C i) + (#(B i) : ℝ) * #(C i))
      = ∑ i ∈ Finset.range k,
        ((#(A i) : ℝ) * #(B i) + (#(A i) : ℝ) * #(C i) + (#(B i) : ℝ) * #(C i)) :=
    Finset.sum_fiberwise_of_maps_to hmaps _
  have hbound : ∑ s ∈ S, ∑ i ∈ (Finset.range k).filter (fun i => idx i = s),
        ((#(A i) : ℝ) * #(B i) + (#(A i) : ℝ) * #(C i) + (#(B i) : ℝ) * #(C i))
      ≤ (#S : ℝ) * (9 * (N : ℝ) ^ 2 / 2) := by
    calc ∑ s ∈ S, ∑ i ∈ (Finset.range k).filter (fun i => idx i = s),
            ((#(A i) : ℝ) * #(B i) + (#(A i) : ℝ) * #(C i) + (#(B i) : ℝ) * #(C i))
        ≤ ∑ _s ∈ S, (9 * (N : ℝ) ^ 2 / 2) := Finset.sum_le_sum hfiber
      _ = (#S : ℝ) * (9 * (N : ℝ) ^ 2 / 2) := by rw [Finset.sum_const, nsmul_eq_mul]
  have hSR : (#S : ℝ) ≤ 2 := by exact_mod_cast hS2
  rw [← hsplit]
  nlinarith only [hbound, hSR, sq_nonneg ((N : ℝ))]

/-! ### The refutation -/

/-- **The cluster-edge-disjoint route to the fine block residual is a dead end.**

`Nibble.AX1.BlockCoverResidualFineClusterPacking` is false: at `ε = δ = 1/1000`, `α = 10⁻⁷`,
`T₀ = ε₁ = 1`, the complete graph on `5N` vertices with the equipartition into five clusters of
size `N` admits no cluster-edge-disjoint family of block sub-triples recovering `ν₃*`.  Such a
family lives on at most two cluster triples, hence has covering sum at most `3N²`
(`Nibble.AX1.clusterPacking_family_bound`), while the reduced graph — the complete `5`-partite graph
— has `ν₃* ≥ 10N²/3` (`Nibble.AX1.nu3star_fivePartite_ge`), and
`10/3 > 3 + (1/1000)·25`. -/
theorem not_blockCoverResidualFineClusterPacking : ¬ BlockCoverResidualFineClusterPacking := by
  classical
  intro h
  obtain ⟨n₀, hn₀⟩ := h (1/1000) (1/1000) (1/10000000) 1 1 (by norm_num) (by norm_num)
    (by norm_num) le_rfl (by norm_num) (by norm_num) (by norm_num) one_pos one_pos le_rfl
  set N : ℕ := max n₀ 1 with hNdef
  have hNn₀ : n₀ ≤ N := le_max_left _ _
  have hN : 0 < N := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hNR : (0:ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hcard : n₀ ≤ Fintype.card (Fin 5 × Fin N) := by
    rw [card_univ_five]; omega
  have hparts : (4:ℝ) / 1 ≤ (((cpartition N hN).parts.card : ℕ) : ℝ) := by
    rw [cpartition_parts_card]; norm_num
  have hbound : (((cpartition N hN).parts.card : ℕ) : ℝ)
      ≤ ((SzemerediRegularity.bound ((1:ℝ) / 8) ⌈(4:ℝ) / 1⌉₊ : ℕ) : ℝ) := by
    rw [cpartition_parts_card]
    have h1 := SzemerediRegularity.seven_le_initialBound ((1:ℝ)/8) ⌈(4:ℝ)/1⌉₊
    have h2 := SzemerediRegularity.initialBound_le_bound ((1:ℝ)/8) ⌈(4:ℝ)/1⌉₊
    have h3 : (7:ℕ) ≤ SzemerediRegularity.bound ((1:ℝ)/8) ⌈(4:ℝ)/1⌉₊ := le_trans h1 h2
    have h5 : (5:ℕ) ≤ SzemerediRegularity.bound ((1:ℝ)/8) ⌈(4:ℝ)/1⌉₊ := by omega
    exact_mod_cast h5
  obtain ⟨τ, k, U, W, X, A, B, C, -, hgrid, hdisj, hpack, hcov⟩ :=
    hn₀ (Fin 5 × Fin N) (⊤ : SimpleGraph (Fin 5 × Fin N)) (cpartition N hN) hcard
      (cpartition_isEquipartition N hN) hparts hbound
      (cpartition_isUniform N hN (by norm_num))
  rw [cover_sum_eq_area_gen N hN U W X A B C hgrid] at hcov
  have harea := clusterPacking_family_bound N hN U W X A B C hgrid hdisj hpack
  have hlow := nu3star_fivePartite_ge N hN (ep := (1:ℝ)/8) (de := (1:ℝ)/4) (by norm_num)
    (by norm_num)
  rw [card_univ_five] at hcov
  have hVR : (((5 * N : ℕ)) : ℝ) = 5 * (N : ℝ) := by push_cast; ring
  rw [hVR] at hcov
  nlinarith [hlow, hcov, harea, sq_nonneg ((N:ℝ))]

end Nibble.AX1
