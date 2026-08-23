/-
# Nibble — an UNCONDITIONAL fractional triangle packing at the Dross density

`Nibble.DrossFractional` isolates the target `∃ c < 1/5, DenseGlobalLeftoverConst c` behind *two*
published global inputs: Dross' fractional decomposition theorem and a rounding (nibble) step.
This file **discharges the first of the two, unconditionally**, at the cost of a *fractional*
leftover that is a constant rather than `o(|V|²)` — and that constant is already below the `1/5`
wall.  So the target no longer needs Dross' theorem at all: only the rounding step remains.

## The statement proved here

* `Nibble.IsFracTrianglePacking` — nonnegative triangle weights with every edge load `≤ 1`;
  `Nibble.fracUncoveredTot w = ∑_e 2(1 - load(e))` is the fractional relaxation of
  `Nibble.uncoveredTot`.  The relaxation is *calibrated*: for the `0/1` weighting of a matching the
  two agree exactly (`Nibble.isFracTrianglePacking_indicator`), and a fractional *decomposition* is
  a packing with `fracUncoveredTot = 0` (`Nibble.fracUncoveredTot_eq_zero_of_decomp`).
* `Nibble.fracUncoveredTot_uniform_le_dense` / `Nibble.exists_fracTrianglePacking_dense` — **the
  main result**: at the Dross density `9|V| ≤ 10 δ(G)` the *uniform* weighting `w ≡ 1/(|V| - 2)` is
  a fractional triangle packing with

  `fracUncoveredTot ≤ (19/100)|V|² < (1/5)|V|²`.

  The proof is a two-line trade-off made exact: every edge `uv` has `|N(u) ∩ N(v)| ≥ d(u)+d(v)-|V|`
  common neighbours, so the uniform load deficiency of `uv` is at most `(2|V|-2-d(u)-d(v))/(|V|-2)`;
  summing and using Cauchy–Schwarz `∑_v d(v)² ≥ (2|E|)²/|V|` bounds the total deficiency by
  `γ(1-γ)|V|³/(|V|-2)` with `γ = 2|E|/|V|² ∈ [9/10, 1]`, whence the constant `2·0.9·0.1 = 0.18`
  (rounded to `0.19` to absorb the lower-order terms).  A graph that is dense enough to have many
  edges is automatically dense enough to have large codegrees: that is what beats `1/5`.

## A density-free side result

* `Nibble.hasFracTriangleDecomp_of_codegree_const` — a graph in which every edge lies in the same
  number `d > 0` of triangles decomposes fractionally (uniform weight `1/d`), with no density
  hypothesis; `Nibble.hasFracTriangleDecomp_tripartite` instantiates this at `K_{m,m,m}`, whose
  minimum degree is `(2/3)|V|` (`Nibble.degree_tripartite`).  So the Dross threshold is sufficient,
  not necessary.

## What is still assumed, and what it now buys

* `Nibble.NibbleFracRounding` — the rounding step (Frankl–Rödl / Pippenger–Spencer, in the
  fractional form of Kahn's theorem: for `3`-uniform hypergraphs of codegree `≤ 1`, an integral
  matching comes within `o(n²)` of the fractional optimum).  `Nibble.UniformTriangleRounding` is
  the narrower form actually used: rounding is needed *only* for the uniform weighting above.
* `Nibble.denseGlobalLeftoverConst_of_uniformTriangleRounding`,
  `Nibble.leftoverConst_below_fifth_of_uniformTriangleRounding`,
  `Nibble.beats_half_of_nibbleFracRounding` — the machine-checked chain

  `UniformTriangleRounding → DenseGlobalLeftoverConst (0.195) → (∃ c < 1/5, …)`
  `→ (∃ β < 1/2, per-vertex star bound β|V|)`.

  Note this needs a *single* global input where `Nibble.DrossFractional` needed two, and the input
  is exactly the library's own nibble theme.  Nothing here contradicts
  `Nibble.BandFifthRefutation`: that file refutes the *band* nibble (near-regularity at `μ = 1/5`
  forcing a near-perfect matching); the hypothesis here compares the integral matching with the
  *fractional* optimum, which the band witness also fails to beat.
* `Nibble.denseGlobalSmallLeftover_of_dross_of_nibbleFracRounding` — with Dross' theorem on top,
  the same rounding hypothesis still gives the full `o(|V|²)` residual, hence the `1/10`
  per-vertex bound.  So the new hypothesis is at least as useful as the old rounding hypothesis.

Sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.DrossFractional

open Finset SimpleGraph Hypergraph Nibble.YusterE

namespace Nibble

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ### Fractional triangle packings -/

/-- The total weight a fractional triangle weighting puts on the edge `e`. -/
noncomputable def fracLoad (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : Finset (EdgeV G) → ℝ) (e : EdgeV G) : ℝ :=
  ∑ T ∈ trianglesThrough G e, w T

/-- A **fractional triangle packing**: nonnegative weights on the triangles of `G` under which no
edge carries total weight more than `1`. -/
def IsFracTrianglePacking (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : Finset (EdgeV G) → ℝ) : Prop :=
  (∀ T ∈ triangleHypergraphSub G, 0 ≤ w T) ∧ ∀ e : EdgeV G, fracLoad G w e ≤ 1

/-- The **fractional uncovered incidence count** of a fractional triangle weighting: twice the
total edge deficiency `∑_e (1 - load(e))`. -/
noncomputable def fracUncoveredTot (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : Finset (EdgeV G) → ℝ) : ℝ :=
  ∑ e : EdgeV G, 2 * (1 - fracLoad G w e)

/-- A fractional triangle decomposition is a fractional triangle packing. -/
theorem IsFracTriangleDecomp.isFracTrianglePacking {G : SimpleGraph V} [DecidableRel G.Adj]
    {w : Finset (EdgeV G) → ℝ} (h : IsFracTriangleDecomp G w) : IsFracTrianglePacking G w :=
  ⟨h.1, fun e => le_of_eq (h.2 e)⟩

/-- A fractional triangle decomposition leaves nothing uncovered. -/
theorem fracUncoveredTot_eq_zero_of_decomp {G : SimpleGraph V} [DecidableRel G.Adj]
    {w : Finset (EdgeV G) → ℝ} (h : IsFracTriangleDecomp G w) : fracUncoveredTot G w = 0 := by
  simp [fracUncoveredTot, fracLoad, h.2]

/-! ### Common neighbourhoods -/

/-- The common neighbourhood of the two endpoints of an edge. -/
def commonNbrs (G : SimpleGraph V) [DecidableRel G.Adj] (e : EdgeV G) : Finset V :=
  Finset.univ.filter (fun z => ∀ x ∈ e.val, G.Adj x z)

/-- Every edge of the edge type is a pair of adjacent vertices. -/
theorem exists_pair_of_edgeV (G : SimpleGraph V) [DecidableRel G.Adj] (e : EdgeV G) :
    ∃ u v : V, u ≠ v ∧ G.Adj u v ∧ e.val = {u, v} := by
  have h := SimpleGraph.mem_cliqueFinset_iff.mp e.property
  obtain ⟨u, v, huv, hs⟩ := Finset.card_eq_two.mp h.card_eq
  exact ⟨u, v, huv, h.isClique (by simp [hs]) (by simp [hs]) huv, hs⟩

theorem commonNbrs_eq (G : SimpleGraph V) [DecidableRel G.Adj] {e : EdgeV G} {u v : V}
    (huv : e.val = {u, v}) : commonNbrs G e = G.neighborFinset u ∩ G.neighborFinset v := by
  ext z
  simp [commonNbrs, huv, SimpleGraph.adj_comm]

/-- **The `3`-cliques containing an edge** are exactly the edge together with one of its common
neighbours. -/
theorem cliqueFinset3_filter_supset_eq_image (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : EdgeV G) :
    ((G.cliqueFinset 3).filter (fun t => e.val ⊆ t))
      = (commonNbrs G e).image (fun z => insert z e.val) := by
  classical
  have hecard : (e.val).card = 2 := (SimpleGraph.mem_cliqueFinset_iff.mp e.property).card_eq
  have heclique : G.IsClique (e.val : Set V) := (SimpleGraph.mem_cliqueFinset_iff.mp e.property).1
  ext t
  simp only [Finset.mem_filter, Finset.mem_image, SimpleGraph.mem_cliqueFinset_iff, commonNbrs,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨ht, hsub⟩
    have hcard : (t \ e.val).card = 1 := by
      rw [Finset.card_sdiff_of_subset hsub, ht.card_eq, hecard]
    obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hcard
    have hzt : z ∈ t \ e.val := by rw [hz]; exact Finset.mem_singleton_self z
    rw [Finset.mem_sdiff] at hzt
    refine ⟨z, ?_, ?_⟩
    · intro x hx
      exact ht.isClique (hsub hx) hzt.1 (by rintro rfl; exact hzt.2 hx)
    · have hsubset : insert z e.val ⊆ t := by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact hzt.1
        · exact hsub hx
      have hcard3 : t.card ≤ (insert z e.val).card := by
        rw [ht.card_eq, Finset.card_insert_of_notMem hzt.2, hecard]
      exact Finset.eq_of_subset_of_card_le hsubset hcard3
  · rintro ⟨z, hz, rfl⟩
    have hznot : z ∉ e.val := fun hmem => (hz z hmem).ne rfl
    have hcard : (insert z e.val).card = 3 := by
      rw [Finset.card_insert_of_notMem hznot, hecard]
    refine ⟨⟨?_, hcard⟩, Finset.subset_insert _ _⟩
    intro a ha b hb hab
    simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at ha hb
    rcases ha with rfl | ha
    · rcases hb with rfl | hb
      · exact absurd rfl hab
      · exact (hz b hb).symm
    · rcases hb with rfl | hb
      · exact hz a ha
      · exact heclique ha hb hab

/-- **Adding a common neighbour to an edge is injective.** -/
theorem insert_commonNbrs_injOn (G : SimpleGraph V) [DecidableRel G.Adj] (e : EdgeV G) :
    Set.InjOn (fun z => insert z e.val) (commonNbrs G e : Finset V) := by
  classical
  intro z hz z' hz' heq
  simp only [Finset.mem_coe, commonNbrs, Finset.mem_filter, Finset.mem_univ, true_and] at hz hz'
  have hznot : z ∉ e.val := fun hmem => (hz z hmem).ne rfl
  have hmem : z ∈ insert z' e.val := by
    have : z ∈ insert z e.val := Finset.mem_insert_self z _
    simpa [heq] using this
  rcases Finset.mem_insert.mp hmem with h | h
  · exact h
  · exact absurd h hznot

/-- **The triangles through an edge are counted by its common neighbourhood.** -/
theorem card_trianglesThrough_eq_commonNbrs (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : EdgeV G) : (trianglesThrough G e).card = (commonNbrs G e).card := by
  classical
  rw [card_trianglesThrough_eq, cliqueFinset3_filter_supset_eq_image G e,
    Finset.card_image_of_injOn (insert_commonNbrs_injOn G e)]

/-- No edge lies in more than `|V| - 2` triangles. -/
theorem card_commonNbrs_le (G : SimpleGraph V) [DecidableRel G.Adj] (e : EdgeV G) :
    (commonNbrs G e).card + 2 ≤ Fintype.card V := by
  obtain ⟨u, v, huv, hadj, hval⟩ := exists_pair_of_edgeV G e
  have hsub : commonNbrs G e ⊆ Finset.univ \ ({u, v} : Finset V) := by
    intro z hz
    simp only [commonNbrs, Finset.mem_filter, Finset.mem_univ, true_and, hval] at hz
    have h1 : G.Adj u z := hz u (by simp)
    have h2 : G.Adj v z := hz v (by simp)
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    rintro (rfl | rfl)
    · exact h1.ne rfl
    · exact h2.ne rfl
  have hc : ((Finset.univ : Finset V) \ ({u, v} : Finset V)).card = Fintype.card V - 2 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
      Finset.card_insert_of_notMem (by simp [huv]), Finset.card_singleton]
  have h2 : 2 ≤ Fintype.card V := by
    have : ({u, v} : Finset V).card ≤ Fintype.card V := Finset.card_le_univ _
    rwa [Finset.card_insert_of_notMem (by simp [huv]), Finset.card_singleton] at this
  have := Finset.card_le_card hsub
  omega

/-- **The codegree bound**: the two endpoints of an edge have at least `d(u) + d(v) - |V|` common
neighbours. -/
theorem degree_add_degree_le (G : SimpleGraph V) [DecidableRel G.Adj] {e : EdgeV G} {u v : V}
    (huv : e.val = {u, v}) :
    G.degree u + G.degree v ≤ Fintype.card V + (commonNbrs G e).card := by
  rw [commonNbrs_eq G huv, ← SimpleGraph.card_neighborFinset_eq_degree,
    ← SimpleGraph.card_neighborFinset_eq_degree]
  have := Finset.card_union_add_card_inter (G.neighborFinset u) (G.neighborFinset v)
  have h2 : (G.neighborFinset u ∪ G.neighborFinset v).card ≤ Fintype.card V :=
    Finset.card_le_univ _
  omega

/-! ### Double counting over the edge type -/

theorem pair_mem_cliqueFinset_two (G : SimpleGraph V) [DecidableRel G.Adj] {u v : V}
    (h : G.Adj u v) : ({u, v} : Finset V) ∈ G.cliqueFinset 2 := by
  rw [SimpleGraph.mem_cliqueFinset_iff]
  refine ⟨?_, ?_⟩
  · simp only [Finset.coe_insert, Finset.coe_singleton]
    exact SimpleGraph.isClique_pair.mpr (fun _ => h)
  · rw [Finset.card_insert_of_notMem (by simp [h.ne]), Finset.card_singleton]

/-- **Each vertex lies on exactly `deg v` edges.** -/
theorem card_edgeV_at (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    (Finset.univ.filter (fun e : EdgeV G => v ∈ e.val)).card = G.degree v := by
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  refine (Finset.card_bij (fun w hw => (⟨{v, w}, pair_mem_cliqueFinset_two G
    (by simpa using hw)⟩ : EdgeV G)) ?_ ?_ ?_).symm
  · intro w hw
    simp
  · intro a ha b hb hab
    simp only [Subtype.mk.injEq] at hab
    have hb' : b ∈ ({v, a} : Finset V) := by rw [hab]; simp
    have hbne : b ≠ v := (G.ne_of_adj (by simpa using hb)).symm
    rcases Finset.mem_insert.mp hb' with h | h
    · exact absurd h hbne
    · exact (Finset.mem_singleton.mp h).symm
  · intro e he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
    obtain ⟨a, b, hab, hadj, hval⟩ := exists_pair_of_edgeV G e
    rw [hval] at he
    rcases Finset.mem_insert.mp he with rfl | h
    · exact ⟨b, by simpa using hadj, by apply Subtype.ext; simp [hval]⟩
    · rw [Finset.mem_singleton] at h
      subst h
      exact ⟨a, by simpa using hadj.symm, by apply Subtype.ext; simp [hval, Finset.pair_comm]⟩

/-- **The double-counting identity** over the edge type. -/
theorem sum_edgeV_sum_val (G : SimpleGraph V) [DecidableRel G.Adj] (f : V → ℝ) :
    ∑ e : EdgeV G, ∑ x ∈ e.val, f x = ∑ v : V, f v * (G.degree v : ℝ) := by
  classical
  have h1 : ∀ e : EdgeV G, ∑ x ∈ e.val, f x = ∑ v : V, if v ∈ e.val then f v else 0 := by
    intro e
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  simp_rw [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, card_edgeV_at G v,
    nsmul_eq_mul, mul_comm]

/-- **Handshake on the edge type.** -/
theorem two_mul_card_edgeV (G : SimpleGraph V) [DecidableRel G.Adj] :
    2 * (Fintype.card (EdgeV G) : ℝ) = ∑ v : V, (G.degree v : ℝ) := by
  have h := sum_edgeV_sum_val G (fun _ => (1 : ℝ))
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, one_mul] at h
  rw [← h]
  have hcard : ∀ e : EdgeV G, ((e.val).card : ℝ) = 2 := by
    intro e
    rw [(SimpleGraph.mem_cliqueFinset_iff.mp e.property).card_eq]
    norm_num
  simp_rw [hcard]
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, mul_comm]

/-- **The degree-square identity.** -/
theorem sum_edgeV_degrees (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∑ e : EdgeV G, ∑ x ∈ e.val, (G.degree x : ℝ) = ∑ v : V, (G.degree v : ℝ) ^ 2 := by
  rw [sum_edgeV_sum_val G (fun v => (G.degree v : ℝ))]
  exact Finset.sum_congr rfl (fun v _ => by ring)

/-- **Summed codegree bound**: `∑_e |N(u)∩N(v)| ≥ ∑_v d(v)² − |V|·|E|`. -/
theorem sum_card_commonNbrs_lower (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∑ v : V, (G.degree v : ℝ) ^ 2) - (Fintype.card V : ℝ) * (Fintype.card (EdgeV G) : ℝ)
      ≤ ∑ e : EdgeV G, ((commonNbrs G e).card : ℝ) := by
  have hper : ∀ e : EdgeV G, ∑ x ∈ e.val, (G.degree x : ℝ)
      ≤ (Fintype.card V : ℝ) + ((commonNbrs G e).card : ℝ) := by
    intro e
    obtain ⟨u, v, huv, hadj, hval⟩ := exists_pair_of_edgeV G e
    have hsum : ∑ x ∈ e.val, (G.degree x : ℝ) = (G.degree u : ℝ) + (G.degree v : ℝ) := by
      rw [hval, Finset.sum_insert (by simpa using huv), Finset.sum_singleton]
    rw [hsum]
    have := degree_add_degree_le G hval
    exact_mod_cast (by exact_mod_cast this : ((G.degree u + G.degree v : ℕ) : ℝ)
      ≤ ((Fintype.card V + (commonNbrs G e).card : ℕ) : ℝ))
  have hsum := Finset.sum_le_sum (fun e (_ : e ∈ (Finset.univ : Finset (EdgeV G))) => hper e)
  rw [sum_edgeV_degrees G, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
    Finset.card_univ] at hsum
  linarith

/-! ### The unconditional fractional packing -/

/-- **The uniform weighting `1/(|V|-2)` is a fractional triangle packing.** -/
theorem isFracTrianglePacking_uniform (G : SimpleGraph V) [DecidableRel G.Adj]
    (hV : 3 ≤ Fintype.card V) :
    IsFracTrianglePacking G (fun _ => 1 / ((Fintype.card V : ℝ) - 2)) := by
  have h2 : (0 : ℝ) < (Fintype.card V : ℝ) - 2 := by
    have : (3 : ℝ) ≤ (Fintype.card V : ℝ) := by exact_mod_cast hV
    linarith
  refine ⟨fun T _ => by positivity, fun e => ?_⟩
  rw [fracLoad, Finset.sum_const, nsmul_eq_mul, card_trianglesThrough_eq_commonNbrs]
  rw [mul_one_div, div_le_one h2]
  have := card_commonNbrs_le G e
  have : ((commonNbrs G e).card : ℝ) + 2 ≤ (Fintype.card V : ℝ) := by exact_mod_cast this
  linarith

/-- The uncovered count of the uniform weighting, in closed form. -/
theorem fracUncoveredTot_uniform (G : SimpleGraph V) [DecidableRel G.Adj] :
    fracUncoveredTot G (fun _ => 1 / ((Fintype.card V : ℝ) - 2))
      = 2 * (Fintype.card (EdgeV G) : ℝ)
        - (2 / ((Fintype.card V : ℝ) - 2)) * ∑ e : EdgeV G, ((commonNbrs G e).card : ℝ) := by
  have hload : ∀ e : EdgeV G, fracLoad G (fun _ => 1 / ((Fintype.card V : ℝ) - 2)) e
      = ((commonNbrs G e).card : ℝ) / ((Fintype.card V : ℝ) - 2) := by
    intro e
    rw [fracLoad, Finset.sum_const, nsmul_eq_mul, card_trianglesThrough_eq_commonNbrs, mul_one_div]
  have hterm : ∀ e : EdgeV G, 2 * (1 - ((commonNbrs G e).card : ℝ) / ((Fintype.card V : ℝ) - 2))
      = 2 - (2 / ((Fintype.card V : ℝ) - 2)) * ((commonNbrs G e).card : ℝ) := by
    intro e; ring
  simp_rw [fracUncoveredTot, hload, hterm]
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, Finset.card_univ, ← Finset.mul_sum]
  rw [card_EdgeV]
  ring

/-- The elementary inequality behind the bound. -/
theorem dense_frac_arith (n m Q S : ℝ) (hn : 3 ≤ n) (hm : 9 / 10 * n ^ 2 ≤ 2 * m)
    (hCS : 4 * m ^ 2 ≤ n * Q) (hQS : Q - n * m ≤ S) :
    2 * m - (2 / (n - 2)) * S ≤ (19 / 100) * n ^ 2 := by
  have hn2 : (0:ℝ) < n - 2 := by linarith
  have hs : 0 ≤ m - 45 / 100 * n ^ 2 := by linarith
  have key : 2 * m * (n - 2) - 2 * (Q - n * m) ≤ (19 / 100) * n ^ 2 * (n - 2) := by
    nlinarith [sq_nonneg (m - 45 / 100 * n ^ 2), mul_nonneg hs (by linarith : (0:ℝ) ≤ n),
      mul_nonneg hs (by nlinarith : (0:ℝ) ≤ n ^ 2), sq_nonneg n]
  have h1 : 2 * (Q - n * m) ≤ ((2 / (n - 2)) * S) * (n - 2) := by
    have h : ((2 / (n - 2)) * S) * (n - 2) = 2 * S := by field_simp
    rw [h]; linarith
  have h3 : (2 * m - (19 / 100) * n ^ 2) * (n - 2) ≤ ((2 / (n - 2)) * S) * (n - 2) := by linarith
  have := le_of_mul_le_mul_right h3 hn2
  linarith

/-- **The unconditional fractional bound at the Dross density.**  At `9|V| ≤ 10 δ(G)` the uniform
triangle weighting `1/(|V|-2)` is a fractional triangle packing whose uncovered incidence count is
at most `0.19|V|²` — strictly below the `1/5` wall. -/
theorem fracUncoveredTot_uniform_le_dense (G : SimpleGraph V) [DecidableRel G.Adj]
    (hV : 3 ≤ Fintype.card V) (hdense : 9 * Fintype.card V ≤ 10 * G.minDegree) :
    fracUncoveredTot G (fun _ => 1 / ((Fintype.card V : ℝ) - 2))
      ≤ (19 / 100) * (Fintype.card V : ℝ) ^ 2 := by
  rw [fracUncoveredTot_uniform G]
  set n : ℝ := (Fintype.card V : ℝ) with hn_def
  set m : ℝ := (Fintype.card (EdgeV G) : ℝ) with hm_def
  set Q : ℝ := ∑ v : V, (G.degree v : ℝ) ^ 2 with hQ_def
  set S : ℝ := ∑ e : EdgeV G, ((commonNbrs G e).card : ℝ) with hS_def
  have hn : (3 : ℝ) ≤ n := by rw [hn_def]; exact_mod_cast hV
  have hhand : 2 * m = ∑ v : V, (G.degree v : ℝ) := two_mul_card_edgeV G
  have hmin : ∀ v : V, ((G.minDegree : ℕ) : ℝ) ≤ (G.degree v : ℝ) := by
    intro v
    exact_mod_cast G.minDegree_le_degree v
  have hdense' : 9 * n ≤ 10 * ((G.minDegree : ℕ) : ℝ) := by rw [hn_def]; exact_mod_cast hdense
  have hm : 9 / 10 * n ^ 2 ≤ 2 * m := by
    rw [hhand]
    have : (n : ℝ) * ((G.minDegree : ℕ) : ℝ) ≤ ∑ v : V, (G.degree v : ℝ) := by
      calc (n : ℝ) * ((G.minDegree : ℕ) : ℝ)
          = ∑ _v : V, ((G.minDegree : ℕ) : ℝ) := by
            rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, hn_def]
        _ ≤ ∑ v : V, (G.degree v : ℝ) := Finset.sum_le_sum (fun v _ => hmin v)
    nlinarith [this, (by linarith : (0:ℝ) ≤ n)]
  have hCS : 4 * m ^ 2 ≤ n * Q := by
    have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset V))
      (f := fun v => (G.degree v : ℝ))
    rw [Finset.card_univ] at h
    rw [← hhand] at h
    calc 4 * m ^ 2 = (2 * m) ^ 2 := by ring
      _ ≤ n * Q := by rw [hQ_def, hn_def]; exact_mod_cast h
  exact dense_frac_arith n m Q S hn hm hCS (by
    have := sum_card_commonNbrs_lower G
    rw [← hQ_def, ← hS_def, ← hm_def, ← hn_def] at this
    linarith)

/-- **The unconditional fractional bound at the Dross density**, in existential form. -/
theorem exists_fracTrianglePacking_dense (G : SimpleGraph V) [DecidableRel G.Adj]
    (hV : 3 ≤ Fintype.card V) (hdense : 9 * Fintype.card V ≤ 10 * G.minDegree) :
    ∃ w : Finset (EdgeV G) → ℝ, IsFracTrianglePacking G w ∧
      fracUncoveredTot G w ≤ (19 / 100) * (Fintype.card V : ℝ) ^ 2 :=
  ⟨_, isFracTrianglePacking_uniform G hV, fracUncoveredTot_uniform_le_dense G hV hdense⟩

/-! ### A density-free sufficient criterion for an exact fractional decomposition -/

/-- **Codegree-regular graphs decompose fractionally.**  If every edge of `G` lies in exactly `d`
triangles (`d > 0`) then the uniform weighting `1/d` is a fractional triangle decomposition — with
no density hypothesis at all.  This covers `Kₙ` (`d = n - 2`), the cocktail-party graphs `Kₙ` minus
a perfect matching (`d = n - 4`) and the balanced complete multipartite graphs, whose minimum
degree is far below the Dross threshold. -/
theorem hasFracTriangleDecomp_of_codegree_const (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hd : 0 < d) (hreg : ∀ e : EdgeV G, (commonNbrs G e).card = d) :
    HasFracTriangleDecomp G := by
  have hd' : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  refine ⟨fun _ => 1 / (d : ℝ), fun T _ => by positivity, fun e => ?_⟩
  rw [Finset.sum_const, nsmul_eq_mul, card_trianglesThrough_eq_commonNbrs, hreg e, mul_one_div,
    div_self (ne_of_gt hd')]

/-! ### An example far below the Dross threshold: the balanced complete tripartite graph -/

/-- The balanced complete tripartite graph `K_{m,m,m}`. -/
def tripartite (m : ℕ) : SimpleGraph (Fin 3 × Fin m) where
  Adj a b := a.1 ≠ b.1
  symm := fun _ _ h => h.symm
  loopless := ⟨fun _ h => h rfl⟩

instance (m : ℕ) : DecidableRel (tripartite m).Adj := fun a b => by
  unfold tripartite; infer_instance

theorem card_tripartite (m : ℕ) : Fintype.card (Fin 3 × Fin m) = 3 * m := by simp

/-- `K_{m,m,m}` is `2m`-regular, i.e. its minimum degree is `(2/3)|V|`: far below the Dross
threshold `(9/10)|V|`. -/
theorem degree_tripartite (m : ℕ) (v : Fin 3 × Fin m) : (tripartite m).degree v = 2 * m := by
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have hset : (tripartite m).neighborFinset v
      = (Finset.univ.filter (fun c : Fin 3 => c ≠ v.1)) ×ˢ (Finset.univ : Finset (Fin m)) := by
    ext z
    simp [tripartite, SimpleGraph.mem_neighborFinset, Finset.mem_product, eq_comm]
  rw [hset, Finset.card_product, Finset.card_univ, Fintype.card_fin]
  have h2 : ∀ a : Fin 3, (Finset.univ.filter (fun c : Fin 3 => c ≠ a)).card = 2 := by decide +kernel
  rw [h2]

/-- Every edge of `K_{m,m,m}` lies in exactly `m` triangles. -/
theorem codegree_tripartite (m : ℕ) (e : EdgeV (tripartite m)) :
    (commonNbrs (tripartite m) e).card = m := by
  classical
  obtain ⟨u, v, huv, hadj, hval⟩ := exists_pair_of_edgeV (tripartite m) e
  have hne : u.1 ≠ v.1 := hadj
  have hset : commonNbrs (tripartite m) e
      = (Finset.univ.filter (fun c : Fin 3 => c ≠ u.1 ∧ c ≠ v.1))
          ×ˢ (Finset.univ : Finset (Fin m)) := by
    ext z
    simp only [commonNbrs, Finset.mem_filter, Finset.mem_univ, true_and, hval, Finset.mem_product,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro h
      exact ⟨⟨fun hc => (h u (Or.inl rfl)) hc.symm, fun hc => (h v (Or.inr rfl)) hc.symm⟩, trivial⟩
    · rintro ⟨⟨h1, h2⟩, -⟩ x (rfl | rfl)
      · exact fun hc => h1 hc.symm
      · exact fun hc => h2 hc.symm
  rw [hset, Finset.card_product, Finset.card_univ, Fintype.card_fin]
  have hc : ∀ a b : Fin 3, a ≠ b →
      (Finset.univ.filter (fun c : Fin 3 => c ≠ a ∧ c ≠ b)).card = 1 := by decide +kernel
  rw [hc u.1 v.1 hne, one_mul]

/-- **`K_{m,m,m}` has a fractional triangle decomposition**, although its minimum degree is only
`(2/3)|V|`: the Dross threshold is sufficient, not necessary. -/
theorem hasFracTriangleDecomp_tripartite {m : ℕ} (hm : 0 < m) :
    HasFracTriangleDecomp (tripartite m) :=
  hasFracTriangleDecomp_of_codegree_const (tripartite m) hm (codegree_tripartite m)

/-! ### Calibration: integral packings are fractional packings, with the same leftover -/

/-- **The `0/1` weighting of a matching is a fractional triangle packing, and its fractional
uncovered count is exactly `Nibble.uncoveredTot`.**  So `Nibble.fracUncoveredTot` really is the
fractional relaxation of the quantity the residual is stated in. -/
theorem isFracTrianglePacking_indicator (G : SimpleGraph V) [DecidableRel G.Adj]
    {M : Finset (Finset (EdgeV G))} (hM : IsMatching (triangleHypergraphSub G) M) :
    IsFracTrianglePacking G (fun T => if T ∈ M then 1 else 0) ∧
      fracUncoveredTot G (fun T => if T ∈ M then 1 else 0) = (uncoveredTot G M : ℝ) := by
  classical
  set w : Finset (EdgeV G) → ℝ := fun T => if T ∈ M then 1 else 0 with hw_def
  have hload : ∀ e : EdgeV G,
      fracLoad G w e = (((trianglesThrough G e).filter (fun T => T ∈ M)).card : ℝ) := by
    intro e
    rw [fracLoad, hw_def, Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero,
      nsmul_eq_mul, mul_one]
  have hle_one : ∀ e : EdgeV G, ((trianglesThrough G e).filter (fun T => T ∈ M)).card ≤ 1 := by
    intro e
    refine Finset.card_le_one.mpr (fun T hT T' hT' => ?_)
    simp only [Finset.mem_filter, trianglesThrough, Finset.mem_filter] at hT hT'
    by_contra hne
    exact (Finset.disjoint_left.mp (hM.disjoint T hT.2 T' hT'.2 hne)) hT.1.2 hT'.1.2
  have hpack : IsFracTrianglePacking G w := by
    refine ⟨fun T _ => by rw [hw_def]; positivity, fun e => ?_⟩
    rw [hload e]
    exact_mod_cast hle_one e
  refine ⟨hpack, ?_⟩
  have hdef : ∀ e : EdgeV G, 1 - fracLoad G w e = if e ∈ uncovered G M then 1 else 0 := by
    intro e
    rw [hload e]
    by_cases hu : e ∈ uncovered G M
    · have hempty : (trianglesThrough G e).filter (fun T => T ∈ M) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro T hT hTM
        simp only [trianglesThrough, Finset.mem_filter] at hT
        simp only [uncovered, Finset.mem_filter, Finset.mem_univ, true_and] at hu
        exact hu T hTM hT.2
      simp [hempty, hu]
    · have hne : ((trianglesThrough G e).filter (fun T => T ∈ M)).Nonempty := by
        simp only [uncovered, Finset.mem_filter, Finset.mem_univ, true_and, not_forall] at hu
        obtain ⟨T, hTM, hTe⟩ := hu
        rw [not_not] at hTe
        exact ⟨T, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hM.subset hTM, hTe⟩, hTM⟩⟩
      have hone : ((trianglesThrough G e).filter (fun T => T ∈ M)).card = 1 :=
        le_antisymm (hle_one e) (Finset.card_pos.mpr hne)
      simp [hone, hu]
  simp_rw [fracUncoveredTot, hdef]
  rw [← Finset.mul_sum, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul,
    mul_one, ← two_mul_card_uncovered G M]
  push_cast
  ring

/-- **Dross's theorem is a strictly stronger fractional input** than the unconditional bound proved
here: it would give a fractional packing with *no* uncovered incidences at all. -/
theorem exists_fracTrianglePacking_zero_of_dross (h : DrossFractional) (G : SimpleGraph V)
    [DecidableRel G.Adj] (hdense : 9 * Fintype.card V ≤ 10 * G.minDegree) :
    ∃ w : Finset (EdgeV G) → ℝ, IsFracTrianglePacking G w ∧ fracUncoveredTot G w = 0 := by
  obtain ⟨w, hw⟩ := h G hdense
  exact ⟨w, hw.isFracTrianglePacking, fracUncoveredTot_eq_zero_of_decomp hw⟩

/-! ### The single remaining global input, and the chain to the target -/

/-- **The nibble rounding step** (Frankl–Rödl / Pippenger–Spencer, in Kahn's fractional form): at
the Dross density, an integral triangle packing can be found whose uncovered incidence count
exceeds that of any prescribed fractional triangle packing by at most `ε|V|²`. -/
def NibbleFracRounding : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ,
    ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
      (w : Finset (EdgeV G) → ℝ),
      n₀ ≤ Fintype.card V → 9 * Fintype.card V ≤ 10 * G.minDegree →
      IsFracTrianglePacking G w →
      ∃ M : Finset (Finset (EdgeV G)), IsMatching (triangleHypergraphSub G) M ∧
        (uncoveredTot G M : ℝ) ≤ fracUncoveredTot G w + ε * (Fintype.card V : ℝ) ^ 2

/-- **The narrowest form of the missing input**: the rounding step is only ever needed for the
*uniform* fractional triangle packing `1/(|V|-2)`. -/
def UniformTriangleRounding : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ,
    ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      n₀ ≤ Fintype.card V → 9 * Fintype.card V ≤ 10 * G.minDegree →
      ∃ M : Finset (Finset (EdgeV G)), IsMatching (triangleHypergraphSub G) M ∧
        (uncoveredTot G M : ℝ)
          ≤ fracUncoveredTot G (fun _ => 1 / ((Fintype.card V : ℝ) - 2))
            + ε * (Fintype.card V : ℝ) ^ 2

/-- The general rounding step contains the uniform one. -/
theorem uniformTriangleRounding_of_nibbleFracRounding (h : NibbleFracRounding) :
    UniformTriangleRounding := by
  intro ε hε
  obtain ⟨n₀, hmain⟩ := h ε hε
  refine ⟨max n₀ 3, ?_⟩
  intro V _ _ G _ hV hdense
  have hV3 : 3 ≤ Fintype.card V := le_trans (le_max_right n₀ 3) hV
  have hVn₀ : n₀ ≤ Fintype.card V := le_trans (le_max_left n₀ 3) hV
  exact hmain G _ hVn₀ hdense (isFracTrianglePacking_uniform G hV3)

/-- **Rounding alone crosses the `1/5` wall.** -/
theorem denseGlobalLeftoverConst_of_uniformTriangleRounding (h : UniformTriangleRounding) :
    DenseGlobalLeftoverConst (195 / 1000) := by
  obtain ⟨n₀, hmain⟩ := h (5 / 1000) (by norm_num)
  refine ⟨max n₀ 3, ?_⟩
  intro V _ _ G _ hV hdense
  have hV3 : 3 ≤ Fintype.card V := le_trans (le_max_right n₀ 3) hV
  have hVn₀ : n₀ ≤ Fintype.card V := le_trans (le_max_left n₀ 3) hV
  obtain ⟨M, hM, hMle⟩ := hmain G hVn₀ hdense
  have hle := fracUncoveredTot_uniform_le_dense G hV3 hdense
  exact ⟨M, hM, by linarith⟩

/-- **Rounding alone crosses the `1/5` wall.** -/
theorem denseGlobalLeftoverConst_of_nibbleFracRounding (h : NibbleFracRounding) :
    DenseGlobalLeftoverConst (195 / 1000) :=
  denseGlobalLeftoverConst_of_uniformTriangleRounding
    (uniformTriangleRounding_of_nibbleFracRounding h)

/-- **The target, from the uniform rounding step alone.** -/
theorem leftoverConst_below_fifth_of_uniformTriangleRounding (h : UniformTriangleRounding) :
    ∃ c : ℝ, c < 1 / 5 ∧ DenseGlobalLeftoverConst c :=
  ⟨195 / 1000, by norm_num, denseGlobalLeftoverConst_of_uniformTriangleRounding h⟩

/-- **The target, from the rounding step alone.** -/
theorem leftoverConst_below_fifth_of_nibbleFracRounding (h : NibbleFracRounding) :
    ∃ c : ℝ, c < 1 / 5 ∧ DenseGlobalLeftoverConst c :=
  ⟨195 / 1000, by norm_num, denseGlobalLeftoverConst_of_nibbleFracRounding h⟩

/-- **Rounding alone beats the unconditional `1/2` wall** for the per-vertex uncovered star. -/
theorem beats_half_of_nibbleFracRounding (h : NibbleFracRounding) :
    ∃ β : ℝ, β < 1 / 2 ∧ ∃ n₀ : ℕ,
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        n₀ ≤ Fintype.card V → 9 * Fintype.card V ≤ 10 * G.minDegree →
        ∃ M : Finset (Finset (EdgeV G)), IsMatching (triangleHypergraphSub G) M ∧
          ∀ v : V, ((uncoveredAt G M v).card : ℝ) ≤ β * (Fintype.card V : ℝ) :=
  beats_half_of_leftoverConst (by norm_num : (0:ℝ) ≤ 195 / 1000) (by norm_num)
    (denseGlobalLeftoverConst_of_nibbleFracRounding h)

/-- **The new rounding hypothesis also replaces the old one** in the Dross route: together with
Dross's theorem it gives the full `o(|V|²)` residual `Nibble.DenseGlobalSmallLeftover`, hence the
per-vertex bound `1/10`. -/
theorem denseGlobalSmallLeftover_of_dross_of_nibbleFracRounding (hdross : DrossFractional)
    (hround : NibbleFracRounding) : DenseGlobalSmallLeftover := by
  intro ε hε
  obtain ⟨n₀, hmain⟩ := hround ε hε
  refine ⟨n₀, ?_⟩
  intro V _ _ G _ hV hdense
  obtain ⟨w, hw⟩ := hdross G hdense
  obtain ⟨M, hM, hMle⟩ := hmain G w hV hdense hw.isFracTrianglePacking
  refine ⟨M, hM, ?_⟩
  rw [fracUncoveredTot_eq_zero_of_decomp hw, zero_add] at hMle
  exact hMle

end Nibble
