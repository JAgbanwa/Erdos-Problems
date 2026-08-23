/-
# The approximate-decomposition threshold `δ_F^η` (`ApproxTriDecompMinDeg`) in the dense regime

`BKLO.ApproxTriDecompMinDeg δ` (Section10TransformStepProof.lean) is the input `δ ≥ δ_F^η` of the
repaired transformation step of BKLO Lemma 10.6: every large graph of minimum edge-degree `≥ δn` has
an edge-disjoint triangle family leaving `≤ ηn²` edges uncovered.

For the Erdős #81 regime `δ ≥ 9/10` this is exactly the content of the already-proved dense
maximum-degree triangle nibble `Nibble.denseTriNibbleMaxDeg_holds` (which even gives the stronger
`per-vertex` leftover bound `≤ ηn`).  This file wires the two together, `sorry`-free:

  `BKLO.approxTriDecompMinDeg_dense (hδ : 9/10 ≤ δ) : ApproxTriDecompMinDeg δ`.

Combined with `BKLO.transformStepK3Res_of_approxTriDecomp` and `BKLO.lemma106K3Res_of_inputs`, this
makes `TransformStepK3Res δ` unconditional and reduces `Lemma106K3Res δ` to `Lemma103K3` alone, in
the `δ ≥ 9/10` regime.
-/
import Nibble.DenseTriNibbleMaxDeg
import BKLO.Section10TransformStepProof

open Finset

namespace BKLO

variable {V : Type} [DecidableEq V]

/-- `edgesOf` (used by the nibble via `triEdges`) and `cliqueEdges` (used by `famEdges`/`TriFamilyIn`)
are the same edge set: the non-diagonal edges with both ends in `t`. -/
theorem edgesOf_eq_cliqueEdges (t : Finset V) : Nibble.edgesOf t = cliqueEdges t := by
  ext e
  rw [Nibble.mem_edgesOf, mem_cliqueEdgesV]
  tauto

/-- The same, phrased on the nibble's `triEdges` abbreviation (so `rw` matches syntactically). -/
theorem triEdges_eq_cliqueEdges (t : Finset V) : Nibble.triEdges t = cliqueEdges t :=
  edgesOf_eq_cliqueEdges t

/-- A non-diagonal edge meets `univ` in exactly its two endpoints. -/
theorem card_filter_univ_mem_edge [Fintype V] {e : Sym2 V} (he : ¬ e.IsDiag) :
    (Finset.univ.filter (fun v => v ∈ e)).card = 2 := by
  classical
  induction e using Sym2.ind with
  | _ a b =>
    have hab : a ≠ b := by
      intro h; exact he (by simp [Sym2.isDiag_iff_proj_eq, h])
    have hfil : Finset.univ.filter (fun v => v ∈ s(a, b)) = {a, b} := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Sym2.mem_iff,
        Finset.mem_insert, Finset.mem_singleton]
    rw [hfil, Finset.card_insert_of_notMem (by simpa using hab), Finset.card_singleton]

/-- **Handshake for a loopless edge set.**  `∑_v edeg L v = 2|L|`. -/
theorem sum_edeg_eq_two_mul_card [Fintype V] {L : Finset (Sym2 V)}
    (hL : ∀ e ∈ L, ¬ e.IsDiag) : ∑ v : V, edeg L v = 2 * L.card := by
  classical
  have hcomm : ∑ v : V, edeg L v = ∑ e ∈ L, (Finset.univ.filter (fun v => v ∈ e)).card := by
    unfold edeg
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  rw [hcomm, Finset.sum_congr rfl (fun e he => card_filter_univ_mem_edge (hL e he)),
    Finset.sum_const, smul_eq_mul, Nat.mul_comm]

/-- **`ApproxTriDecompMinDeg` in the dense regime.**  For `δ ≥ 9/10` the approximate-decomposition
threshold `δ_F^η` holds, from the dense maximum-degree triangle nibble. -/
theorem approxTriDecompMinDeg_dense {δ : ℝ} (hδ : (9 : ℝ) / 10 ≤ δ) :
    ApproxTriDecompMinDeg δ := by
  intro η hη
  obtain ⟨n₀, hnib⟩ := Nibble.denseTriNibbleMaxDeg_holds η hη
  refine ⟨max n₀ 1, ?_⟩
  intro V _ _ E hn hloop hdeg
  classical
  -- the graph of `E` on `V`
  set G : SimpleGraph V := SimpleGraph.fromEdgeSet (E : Set (Sym2 V)) with hGdef
  haveI : DecidableRel G.Adj := Classical.decRel _
  have hES : G.edgeSet = (E : Set (Sym2 V)) := by
    rw [hGdef, SimpleGraph.edgeSet_fromEdgeSet]
    ext e
    simp only [Set.mem_diff, Finset.mem_coe]
    constructor
    · rintro ⟨h1, -⟩; exact h1
    · rintro h1; exact ⟨h1, hloop e h1⟩
  have hEFin : G.edgeFinset = E := by
    apply Finset.coe_injective
    rw [SimpleGraph.coe_edgeFinset, hES]
  -- the nibble's `edgeFinset` uses `G.fintypeEdgeSet`; identify it with the ambient instance
  have hinst : @SimpleGraph.edgeFinset V G G.fintypeEdgeSet = G.edgeFinset := by
    apply Finset.coe_injective
    rw [SimpleGraph.coe_edgeFinset, SimpleGraph.coe_edgeFinset]
  have hdegG : ∀ v, G.degree v = edeg E v := by
    intro v
    rw [← G.card_incidenceFinset_eq_degree v, G.incidenceFinset_eq_filter v, hEFin, edeg]
  -- min-degree bound `9n ≤ 10·minDegree`
  have hVpos : 0 < Fintype.card V := by
    have : 1 ≤ Fintype.card V := le_trans (le_max_right n₀ 1) hn
    omega
  haveI : Nonempty V := Fintype.card_pos_iff.1 hVpos
  obtain ⟨v0, hv0⟩ := G.exists_minimal_degree_vertex
  have hmin : 9 * Fintype.card V ≤ 10 * G.minDegree := by
    have hb : (9 : ℝ) / 10 * (Fintype.card V : ℝ) ≤ (G.degree v0 : ℝ) := by
      rw [hdegG v0]
      have hcard0 : (0 : ℝ) ≤ (Fintype.card V : ℝ) := by positivity
      calc (9 : ℝ) / 10 * (Fintype.card V : ℝ)
          ≤ δ * (Fintype.card V : ℝ) := by nlinarith only [hδ, hcard0]
        _ ≤ (edeg E v0 : ℝ) := hdeg v0
    have hR : (9 * Fintype.card V : ℝ) ≤ (10 * G.degree v0 : ℝ) := by nlinarith only [hb]
    have hnat : 9 * Fintype.card V ≤ 10 * G.degree v0 := by exact_mod_cast hR
    rw [hv0]; exact hnat
  obtain ⟨P, htri, hdisj, hleft⟩ := hnib G (le_trans (le_max_left n₀ 1) hn) hmin
  rw [hinst] at hleft
  -- `P.biUnion triEdges = famEdges P` and `G.edgeFinset = E`
  have hbi : P.biUnion Nibble.triEdges = famEdges P := by
    unfold famEdges
    exact Finset.biUnion_congr rfl (fun t _ => triEdges_eq_cliqueEdges t)
  refine ⟨P, ?_, ?_⟩
  · -- `TriFamilyIn E P`
    refine ⟨fun t ht => (htri t ht).card_eq, ?_, ?_⟩
    · -- `cliqueEdges t ⊆ E`
      intro t ht e he
      obtain ⟨hsub, hnd⟩ := mem_cliqueEdgesV.1 he
      induction e using Sym2.ind with
      | _ a b =>
        have ha : a ∈ t := hsub a (by simp)
        have hb : b ∈ t := hsub b (by simp)
        have hab : a ≠ b := by
          intro h; exact hnd (by simp [Sym2.isDiag_iff_proj_eq, h])
        have hadj : G.Adj a b := (htri t ht).1 ha hb hab
        have : s(a, b) ∈ G.edgeFinset := by rw [SimpleGraph.mem_edgeFinset]; exact hadj
        rwa [hEFin] at this
    · -- pairwise edge-disjoint
      intro t ht t' ht' hne
      have hd := hdisj ht ht' hne
      -- rewrite the *goal* (`cliqueEdges`) to the nibble's `edgesOf`/`triEdges` form; `exact` is up to defeq
      rw [← edgesOf_eq_cliqueEdges t, ← edgesOf_eq_cliqueEdges t']
      exact hd
  · -- total leftover `≤ η n²`
    -- the leftover `E \ famEdges P` equals the nibble's leftover set
    have key : E \ famEdges P = G.edgeFinset \ (P.biUnion Nibble.triEdges) := by rw [hEFin, hbi]
    have hLloop : ∀ e ∈ E \ famEdges P, ¬ e.IsDiag :=
      fun e he => hloop e (Finset.mem_sdiff.1 he).1
    have hleftE : ∀ v : V, (edeg (E \ famEdges P) v : ℝ) ≤ η * (Fintype.card V : ℝ) := by
      intro v; rw [key]; unfold edeg; exact hleft v
    -- handshake: `2|L| = ∑_v edeg L v ≤ n · (η n)`
    have hsum : (∑ v : V, edeg (E \ famEdges P) v : ℝ)
        ≤ (Fintype.card V : ℝ) * (η * (Fintype.card V : ℝ)) := by
      calc (∑ v : V, edeg (E \ famEdges P) v : ℝ)
          = ∑ v : V, (edeg (E \ famEdges P) v : ℝ) := by rfl
        _ ≤ ∑ _v : V, η * (Fintype.card V : ℝ) := Finset.sum_le_sum (fun v _ => hleftE v)
        _ = (Fintype.card V : ℝ) * (η * (Fintype.card V : ℝ)) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hhandN : 2 * (E \ famEdges P).card = ∑ v : V, edeg (E \ famEdges P) v :=
      (sum_edeg_eq_two_mul_card hLloop).symm
    have hhand : (2 * (E \ famEdges P).card : ℝ) = (∑ v : V, edeg (E \ famEdges P) v : ℝ) := by
      exact_mod_cast hhandN
    have hle2 : (2 * (E \ famEdges P).card : ℝ)
        ≤ (Fintype.card V : ℝ) * (η * (Fintype.card V : ℝ)) := by rw [hhand]; exact hsum
    have hcard0 : (0 : ℝ) ≤ (Fintype.card V : ℝ) := by positivity
    nlinarith only [hle2, hη, hcard0]

end BKLO
