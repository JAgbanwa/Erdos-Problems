/-
  Part B (Phase 2) — B-I reduction: an integral triangle packing covering `≥ (1-β)·e(G)` edges
  yields an `ApproxTriangleDecomp` with leftover `≤ β·n²`.

  This is the *integral-packing → approximate-decomposition* half of the Haxell–Rödl bridge
  `approx_of_fractional`, isolated as a self-contained, `sorry`-free, ax2-internal lemma. The
  remaining (hard) half is producing such a packing from the fractional decomposition — the Rödl
  nibble / Yuster gap bound `ν₃ ≥ (1-β)·e(G)/3`, delegated to the `nibble` project.
-/
import Ax2.PartB.BKLO.Defs
import Ax2.PartB.BKLO.Gadget

namespace Ax2.BKLO

open SimpleGraph Finset Ax2

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The edges covered by a family of `G`-triangles are edges of `G`. -/
theorem coveredEdges_subset_edgeFinset (G : SimpleGraph V) [DecidableRel G.Adj]
    {P : Finset (Finset V)} (hP : ∀ t ∈ P, G.IsNClique 3 t) :
    coveredEdges P ⊆ G.edgeFinset := by
  intro e he
  rw [coveredEdges, Finset.mem_biUnion] at he
  obtain ⟨t, htP, het⟩ := he
  have hclq : G.IsClique (t : Set V) := (hP t htP).1
  unfold triEdges at het
  rw [Finset.mem_filter] at het
  obtain ⟨hmem, hdiag⟩ := het
  induction e using Sym2.ind with
  | _ a b =>
    rw [Finset.mk_mem_sym2_iff] at hmem
    rw [Sym2.mk_isDiag_iff] at hdiag
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    exact hclq hmem.1 hmem.2 hdiag

/-- **Total weight of a fractional triangle decomposition is `e(G)/3`.** If nonneg weights `w`
cover every edge with total `1` (`hcov`), then `∑_t w t = e(G)/3` — each of the `e(G)` edges gets
weight `1`, and every triangle's weight is counted through its `3` edges. (Mirrors `handshake`.) -/
theorem fractional_weight_sum (G : SimpleGraph V) [DecidableRel G.Adj] (w : Finset V → ℝ)
    (hcov : ∀ e ∈ G.edgeFinset,
      (∑ t ∈ G.cliqueFinset 3, if e ∈ triEdges t then w t else 0) = 1) :
    (∑ t ∈ G.cliqueFinset 3, w t) = (G.edgeFinset.card : ℝ) / 3 := by
  classical
  -- 3 * ∑_t w t = ∑_t ∑_{e ∈ triEdges t} w t = ∑_e ∑_t [e ∈ triEdges t] w t = ∑_{e ∈ E} 1 = e(G)
  have hstep : (3 : ℝ) * (∑ t ∈ G.cliqueFinset 3, w t) = (G.edgeFinset.card : ℝ) := by
    have h1 : ∀ t ∈ G.cliqueFinset 3,
        (3 : ℝ) * w t = ∑ e : Sym2 V, if e ∈ triEdges t then w t else 0 := by
      intro t ht
      have hc : (triEdges t).card = 3 :=
        Ax2.BKLO.triEdges_card_of_isNClique G ((SimpleGraph.mem_cliqueFinset_iff).mp ht)
      rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter,
        Finset.sum_const, hc]
      simp [nsmul_eq_mul]
    calc (3 : ℝ) * (∑ t ∈ G.cliqueFinset 3, w t)
        = ∑ t ∈ G.cliqueFinset 3, ((3 : ℝ) * w t) := by rw [Finset.mul_sum]
      _ = ∑ t ∈ G.cliqueFinset 3, ∑ e : Sym2 V, if e ∈ triEdges t then w t else 0 :=
          Finset.sum_congr rfl h1
      _ = ∑ e : Sym2 V, ∑ t ∈ G.cliqueFinset 3, if e ∈ triEdges t then w t else 0 :=
          Finset.sum_comm
      _ = ∑ e : Sym2 V, if e ∈ G.edgeFinset then (1 : ℝ) else 0 := by
          refine Finset.sum_congr rfl (fun e _ => ?_)
          by_cases he : e ∈ G.edgeFinset
          · rw [if_pos he]; exact hcov e he
          · rw [if_neg he]
            refine Finset.sum_eq_zero (fun t ht => ?_)
            rw [if_neg]
            intro hetri
            exact he (coveredEdges_subset_edgeFinset G
              (fun t' ht' => (SimpleGraph.mem_cliqueFinset_iff).mp ht')
              (by rw [coveredEdges, Finset.mem_biUnion]; exact ⟨t, ht, hetri⟩))
      _ = (G.edgeFinset.card : ℝ) := by
          rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one]
  linarith

/-- `e(G) ≤ n²` (crude, via `2·e(G) = ∑ deg ≤ n·n`). -/
theorem edgeFinset_card_le_sq (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.edgeFinset.card : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 := by
  have h2 : ∑ v, G.degree v = 2 * G.edgeFinset.card := G.sum_degrees_eq_twice_card_edges
  have hdeg : ∑ v, G.degree v ≤ ∑ _v : V, Fintype.card V := by
    refine Finset.sum_le_sum (fun v _ => ?_)
    rw [SimpleGraph.degree]
    exact (Finset.card_le_card (Finset.subset_univ _)).trans_eq (Finset.card_univ)
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul] at hdeg
  have hnat : 2 * G.edgeFinset.card ≤ Fintype.card V * Fintype.card V := by omega
  have : (2 * G.edgeFinset.card : ℝ) ≤ (Fintype.card V : ℝ) * (Fintype.card V : ℝ) := by
    exact_mod_cast hnat
  nlinarith [this]

/-- **B-I (packing half).** An edge-disjoint family `P` of `G`-triangles covering at least a
`(1-β)`-fraction of `E(G)` yields an approximate triangle decomposition whose leftover has
`≤ β·n²` edges. Together with the nibble output `ν₃ ≥ (1-β)·e(G)/3` (`⇒` such a `P` of `≥ (1-β)e/3`
triangles, covering `3·(1-β)e/3 = (1-β)e` edges), this discharges `approx_of_fractional`. -/
theorem approx_of_packing (G : SimpleGraph V) [DecidableRel G.Adj] {β : ℝ} (hβ : 0 ≤ β)
    {P : Finset (Finset V)} (hP : ∀ t ∈ P, G.IsNClique 3 t) (hPd : EdgeDisjoint P)
    (hcov : (1 - β) * (G.edgeFinset.card : ℝ) ≤ ((coveredEdges P).card : ℝ)) :
    ∃ L : Finset (Sym2 V), L ⊆ G.edgeFinset ∧
      (L.card : ℝ) ≤ β * (Fintype.card V : ℝ) ^ 2 ∧ ApproxTriangleDecomp G L := by
  classical
  have hsub : coveredEdges P ⊆ G.edgeFinset := coveredEdges_subset_edgeFinset G hP
  refine ⟨G.edgeFinset \ coveredEdges P, Finset.sdiff_subset, ?_, ?_⟩
  · -- |L| = e(G) - |coveredEdges P| ≤ β·e(G) ≤ β·n²
    have hadd : (G.edgeFinset \ coveredEdges P).card + (coveredEdges P).card = G.edgeFinset.card :=
      Finset.card_sdiff_add_card_eq_card hsub
    have hLR : ((G.edgeFinset \ coveredEdges P).card : ℝ)
        = (G.edgeFinset.card : ℝ) - ((coveredEdges P).card : ℝ) := by
      have hc : ((G.edgeFinset \ coveredEdges P).card : ℝ) + ((coveredEdges P).card : ℝ)
          = (G.edgeFinset.card : ℝ) := by exact_mod_cast hadd
      linarith
    rw [hLR]
    have hesq := edgeFinset_card_le_sq G
    nlinarith [hcov, hesq, hβ, mul_nonneg hβ (sub_nonneg.mpr hesq)]
  · -- ApproxTriangleDecomp: P covers E \ L = coveredEdges P
    refine ⟨P, hP, hPd, ?_⟩
    ext x
    simp only [Finset.mem_sdiff]
    constructor
    · intro hx; exact ⟨hsub hx, fun h => h.2 hx⟩
    · rintro ⟨hx, hx2⟩; by_contra h; exact hx2 ⟨hx, h⟩

end Ax2.BKLO
