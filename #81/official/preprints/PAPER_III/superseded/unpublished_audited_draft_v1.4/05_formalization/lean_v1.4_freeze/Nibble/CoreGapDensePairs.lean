/-
# Nibble — discarding the pairs of low density

`Nibble.AX1.ReducedFamilyAt ε μ η d₀ ε₁` hands the prover a graph reduced at the *coupled*
parameters `(ε₁/8, ε₁/4)`: the surviving pairs of clusters are `ε₁/8`-uniform of density at least
`ε₁/4`, so the regularity scale and the density threshold are locked at a ratio of two.  No counting
lemma survives that regime — `Nibble.AX1.uniform_triple_codegree` already needs `ε ≤ d/2`, and the
parameter budget of `Nibble.AX1.uniform_triple_member` needs `ε ≪ μηδ³`.

The coupling is harmless, because the regularity scale `ε₁` is existentially quantified in
`Nibble.AX1.ReducedFamilyResidual`: choose `ε₁` as small as the target parameters require and then
*throw away the pairs of density below a fixed threshold `δ`*.  This file formalises that step.

* `Nibble.AX1.densePairSubgraph` — the edges of `H` whose endpoints lie in a pair of parts of `P` of
  `G`-density at least `δ`.
* `Nibble.AX1.card_sparse_edges_le` — the discarded edges number at most `δ|V|²`.
* `Nibble.AX1.hasNearRegularFamily_of_densePairs` — **the decoupling step**: a near-regular family
  for the dense-pair subgraph is one for `H`, at accuracy `ε + δ`.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.CoreGapRegularFamily

open Finset SimpleGraph Hypergraph Nibble.YusterE
open scoped Classical

namespace Nibble.AX1

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ### The dense-pair subgraph -/

/-- The subgraph of `H` consisting of the edges whose endpoints lie in a pair of parts of `P` whose
`G`-density is at least `δ`. -/
def densePairSubgraph (H G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finpartition (univ : Finset V)) (δ : ℝ) : SimpleGraph V where
  Adj x y := H.Adj x y ∧
    ∀ U ∈ P.parts, ∀ W ∈ P.parts, x ∈ U → y ∈ W → δ ≤ (G.edgeDensity U W : ℝ)
  symm := by
    rintro x y ⟨h1, h2⟩
    refine ⟨h1.symm, ?_⟩
    intro U hU W hW hyU hxW
    rw [SimpleGraph.edgeDensity_comm]
    exact h2 W hW U hU hxW hyU
  loopless := ⟨fun x h => H.irrefl h.1⟩

noncomputable instance instDecidableRelDensePairSubgraph (H G : SimpleGraph V)
    [DecidableRel G.Adj] (P : Finpartition (univ : Finset V)) (δ : ℝ) :
    DecidableRel (densePairSubgraph H G P δ).Adj := fun _ _ => Classical.dec _

theorem densePairSubgraph_le (H G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finpartition (univ : Finset V)) (δ : ℝ) : densePairSubgraph H G P δ ≤ H :=
  fun _ _ h => h.1

theorem densePairSubgraph_adj (H G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finpartition (univ : Finset V)) (δ : ℝ) (x y : V) :
    (densePairSubgraph H G P δ).Adj x y ↔ H.Adj x y ∧
      ∀ U ∈ P.parts, ∀ W ∈ P.parts, x ∈ U → y ∈ W → δ ≤ (G.edgeDensity U W : ℝ) := Iff.rfl

/-! ### The discarded edges are few -/

omit [Fintype V] [DecidableEq V] in
/-- A pair of finsets of density below `δ` carries at most `δ|U||W|` edges. -/
theorem card_interedges_le_of_edgeDensity_lt (G : SimpleGraph V) [DecidableRel G.Adj]
    {U W : Finset V} {δ : ℝ} (h : (G.edgeDensity U W : ℝ) < δ) :
    ((#(G.interedges U W) : ℕ) : ℝ) ≤ δ * (#U : ℝ) * (#W : ℝ) := by
  classical
  rcases Nat.eq_zero_or_pos (#U) with hU | hU
  · have : G.interedges U W = ∅ := by
      rw [Finset.card_eq_zero] at hU
      rw [hU]
      simp [SimpleGraph.interedges, Rel.interedges]
    rw [this, hU]
    simp
  rcases Nat.eq_zero_or_pos (#W) with hW | hW
  · have : G.interedges U W = ∅ := by
      rw [Finset.card_eq_zero] at hW
      rw [hW]
      simp [SimpleGraph.interedges, Rel.interedges]
    rw [this, hW]
    simp
  have hUpos : (0 : ℝ) < (#U : ℝ) := by exact_mod_cast hU
  have hWpos : (0 : ℝ) < (#W : ℝ) := by exact_mod_cast hW
  have hdens : (G.edgeDensity U W : ℝ) = ((#(G.interedges U W) : ℕ) : ℝ) / ((#U : ℝ) * (#W : ℝ)) := by
    rw [SimpleGraph.edgeDensity_def]
    push_cast
    ring
  rw [hdens, div_lt_iff₀ (by positivity)] at h
  linarith only [h]

/-- **The edges discarded by `Nibble.AX1.densePairSubgraph` are at most `δ|V|²`.** -/
theorem card_sparse_edges_le (H G : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hHG : H ≤ G) (P : Finpartition (univ : Finset V)) {δ : ℝ} (hδ : 0 ≤ δ) :
    ((#(H.cliqueFinset 2 \ (densePairSubgraph H G P δ).cliqueFinset 2) : ℕ) : ℝ)
      ≤ δ * (Fintype.card V : ℝ) ^ 2 := by
  classical
  set Sp : Finset (Finset V × Finset V) :=
    {q ∈ P.parts ×ˢ P.parts | (G.edgeDensity q.1 q.2 : ℝ) < δ} with hSp
  have hsub : H.cliqueFinset 2 \ (densePairSubgraph H G P δ).cliqueFinset 2
      ⊆ Sp.biUnion (fun q => (G.interedges q.1 q.2).image (fun p => ({p.1, p.2} : Finset V))) := by
    intro e he
    rw [Finset.mem_sdiff] at he
    obtain ⟨heH, henot⟩ := he
    have hcard : #e = 2 := (SimpleGraph.mem_cliqueFinset_iff.mp heH).card_eq
    obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hcard
    have hadj : H.Adj x y := (pair_mem_cliqueFinset_two H hxy).mp heH
    have hnadj : ¬ (densePairSubgraph H G P δ).Adj x y := by
      intro hc
      exact henot ((pair_mem_cliqueFinset_two _ hxy).mpr hc)
    rw [densePairSubgraph_adj] at hnadj
    push_neg at hnadj
    obtain ⟨U, hU, W, hW, hxU, hyW, hlt⟩ := hnadj hadj
    refine Finset.mem_biUnion.mpr ⟨(U, W), ?_, ?_⟩
    · rw [hSp, Finset.mem_filter]
      exact ⟨Finset.mem_product.mpr ⟨hU, hW⟩, hlt⟩
    · refine Finset.mem_image.mpr ⟨(x, y), ?_, rfl⟩
      rw [SimpleGraph.mem_interedges_iff]
      exact ⟨hxU, hyW, hHG hadj⟩
  have hcard1 : ((#(H.cliqueFinset 2 \ (densePairSubgraph H G P δ).cliqueFinset 2) : ℕ) : ℝ)
      ≤ ∑ q ∈ Sp, ((#(G.interedges q.1 q.2) : ℕ) : ℝ) := by
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_biUnion_le (s := Sp)
      (t := fun q => (G.interedges q.1 q.2).image (fun p => ({p.1, p.2} : Finset V)))
    have h3 : ∑ q ∈ Sp, #((G.interedges q.1 q.2).image (fun p => ({p.1, p.2} : Finset V)))
        ≤ ∑ q ∈ Sp, #(G.interedges q.1 q.2) :=
      Finset.sum_le_sum fun q _ => Finset.card_image_le
    have h4 : #(H.cliqueFinset 2 \ (densePairSubgraph H G P δ).cliqueFinset 2)
        ≤ ∑ q ∈ Sp, #(G.interedges q.1 q.2) := le_trans h1 (le_trans h2 h3)
    exact_mod_cast h4
  have hcard2 : ∑ q ∈ Sp, ((#(G.interedges q.1 q.2) : ℕ) : ℝ)
      ≤ ∑ q ∈ Sp, δ * (#q.1 : ℝ) * (#q.2 : ℝ) := by
    refine Finset.sum_le_sum fun q hq => ?_
    rw [hSp, Finset.mem_filter] at hq
    exact card_interedges_le_of_edgeDensity_lt G hq.2
  have hcard3 : ∑ q ∈ Sp, δ * (#q.1 : ℝ) * (#q.2 : ℝ)
      ≤ ∑ q ∈ P.parts ×ˢ P.parts, δ * (#q.1 : ℝ) * (#q.2 : ℝ) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
    intro q _ _
    positivity
  have hcard4 : ∑ q ∈ P.parts ×ˢ P.parts, δ * (#q.1 : ℝ) * (#q.2 : ℝ)
      = δ * (∑ U ∈ P.parts, (#U : ℝ)) * (∑ W ∈ P.parts, (#W : ℝ)) := by
    rw [Finset.sum_product]
    simp [Finset.mul_sum, Finset.sum_mul, mul_assoc]
    rw [Finset.sum_comm]
  have hparts : ∑ U ∈ P.parts, (#U : ℝ) = (Fintype.card V : ℝ) := by
    rw [show ((Fintype.card V : ℕ) : ℝ) = ((#(univ : Finset V) : ℕ) : ℝ) from
      by rw [Finset.card_univ]]
    exact_mod_cast P.sum_card_parts
  rw [hcard4, hparts] at hcard3
  calc ((#(H.cliqueFinset 2 \ (densePairSubgraph H G P δ).cliqueFinset 2) : ℕ) : ℝ)
      ≤ ∑ q ∈ Sp, ((#(G.interedges q.1 q.2) : ℕ) : ℝ) := hcard1
    _ ≤ ∑ q ∈ Sp, δ * (#q.1 : ℝ) * (#q.2 : ℝ) := hcard2
    _ ≤ δ * (Fintype.card V : ℝ) * (Fintype.card V : ℝ) := hcard3
    _ = δ * (Fintype.card V : ℝ) ^ 2 := by ring

/-! ### The decoupling step -/

/-- **Discarding the low-density pairs.**  A near-regular family for the dense-pair subgraph of `H`
is a near-regular family for `H`, at accuracy `ε + δ`.  Together with
`Nibble.AX1.hasNearRegularFamily_of_reduced` this decouples the regularity scale of
`Nibble.AX1.ReducedFamilyAt` from the density threshold: one may run the regularity lemma at a scale
`ε₁` as small as one likes and then keep only the pairs of density at least `δ`, with `ε₁ ≪ δ`. -/
theorem hasNearRegularFamily_of_densePairs (H G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel H.Adj] (hHG : H ≤ G) (P : Finpartition (univ : Finset V))
    {δ ε μ η d₀ : ℝ} (hδ : 0 ≤ δ)
    (h : HasNearRegularFamily (densePairSubgraph H G P δ) ε μ η d₀) :
    HasNearRegularFamily H (ε + δ) μ η d₀ := by
  classical
  refine HasNearRegularFamily.mono_of_le (densePairSubgraph_le H G P δ) ?_ h
  have hdel := nu3star_le_add_deleted H (densePairSubgraph H G P δ) (densePairSubgraph_le H G P δ)
  have hcnt := card_sparse_edges_le H G hHG P hδ
  linarith only [hdel, hcnt]

end Nibble.AX1
