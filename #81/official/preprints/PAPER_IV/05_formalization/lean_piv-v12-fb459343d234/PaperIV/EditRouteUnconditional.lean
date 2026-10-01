/-
The edit route, assembled: `FixedL4Localization s` for every rooted defect `s`, with no hypothesis.

The ingredients:
* `AlonShapira.near_chordal_of_induced_cycles_littleO'` (Alon–Shapira, Lemma 4.2, fully proved in
  `RequestProject/`): a class with `o(n^k)` labelled induced `C_k` for every fixed `k ≥ 4` is `o(n²)`-close in edit
  distance to chordal (no induced long cycle).
* `lemmaK` (`PaperIV/EditRouteLemmaK.lean`, via Erdős's k-partite theorem and Lemma B): rooted defect `≤ s` gives
  `o(n^k)` labelled induced `C_k`.
* `isChordal_of_noInducedCycle` (`PaperIV/EditRouteChordalBridge.lean`): no induced long cycle ⇒
  `SimpleGraph.IsChordal`.
* `fixedL4Localization_of_editApprox` (run E7): edit-closeness at every precision ⇒ localization.

Results: `editApproxAt_all : EditApproxAt s δ` for every `δ > 0`, and `fixedL4Localization_unconditional s`.

Layer E (unconditional): axiom target = {propext, Classical.choice, Quot.sound}.
-/
import RequestProject.AlonShapira
import PaperIV.EditRouteLemmaK
import PaperIV.EditRouteChordalBridge
import PaperIV.EditRouteLocalization

namespace PaperIV.EditRoute

open Finset PaperIV.RootedSimplicialDefect PaperIV.FixedL4

/-- Labelled induced copies of `C_k` are exactly the tuples of `cycTuples`. -/
theorem indCopies_eq_card_cycTuples {n k : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    AlonShapira.indCopies (SimpleGraph.cycleGraph k) G = (cycTuples G k).card := by
  classical
  unfold AlonShapira.indCopies
  rw [← Fintype.card_coe (cycTuples G k)]
  refine Fintype.card_congr
    { toFun := fun e => ⟨e, mem_filter.mpr ⟨mem_univ _, e.injective, fun i j => e.map_adj_iff⟩⟩
      invFun := fun f => ⟨⟨f.1, (mem_filter.mp f.2).2.1⟩, fun {i j} => (mem_filter.mp f.2).2.2 i j⟩
      left_inv := fun e => by ext; rfl
      right_inv := fun f => by ext; rfl }

/-- **Edit-closeness to chordal at every precision**, for every rooted defect. -/
theorem editApproxAt_all (s : ℕ) (δ : ℚ) (hδ : 0 < δ) : EditApproxAt s δ := by
  classical
  have hδR : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ
  obtain ⟨M, hM⟩ := AlonShapira.near_chordal_of_induced_cycles_littleO'
    (fun n G => ∃ _ : DecidableRel G.Adj, RootedDefectAt G s)
    (fun k hk δ' hδ' => by
      obtain ⟨M, hM⟩ := lemmaK s k hk δ' hδ'
      refine ⟨M, fun n hn G ⟨inst, hG⟩ => ?_⟩
      rw [@indCopies_eq_card_cycTuples n k G inst]
      exact @hM n hn G inst hG)
    (δ : ℝ) hδR
  refine ⟨M, fun n hn G _ hG => ?_⟩
  obtain ⟨G', hch, hed⟩ := hM n hn G ⟨inferInstance, hG⟩
  refine ⟨G', isChordal_of_noInducedCycle G' (fun k hk => hch k (SimpleGraph.cycleGraph k) ⟨hk, rfl⟩), ?_⟩
  have hset : symmDiff G.edgeSet G'.edgeSet =
      ((symmDiff G.edgeFinset G'.edgeFinset : Finset (Sym2 (Fin n))) : Set (Sym2 (Fin n))) := by
    rw [Finset.coe_symmDiff, SimpleGraph.coe_edgeFinset, SimpleGraph.coe_edgeFinset]
  have hcard : (symmDiff G.edgeSet G'.edgeSet).ncard = AlonShapira.editDist G G' := by
    rw [hset, Set.ncard_coe_finset]
    unfold AlonShapira.editDist
    congr 1
    ext e
    simp only [Finset.mem_symmDiff, SimpleGraph.mem_edgeFinset]
  rw [hcard]
  have h : ((AlonShapira.editDist G G' : ℚ) : ℝ) ≤ ((δ * (n : ℚ) ^ 2 : ℚ) : ℝ) := by
    push_cast; exact hed.le
  exact_mod_cast h

/-- **Fixed-`L = 4` localization at every rooted defect, unconditionally.** -/
theorem fixedL4Localization_unconditional (s : ℕ) : FixedL4Localization s :=
  fixedL4Localization_of_editApprox s (fun δ hδ => editApproxAt_all s δ hδ)

end PaperIV.EditRoute
