import EditRootRecovery
import E32.Transfer
import PaperIV.RootPartitionStability

/-! Quantitative transport of integral stability through a chordal edit.
This is a proved adapter; the chordal edit will be supplied by SublinearEdit.
The chosen real root works for all partitions, including unrestricted pieces.
-/
namespace PaperIV.SublinearResearch
open scoped symmDiff
open Finset PaperIV.FarRounding PaperIV.RootedSimplicialDefect
open PaperIV.RootVocab PaperIV.RootPartitionStability

theorem partition_lower_bound_transfers {n : ℕ} (G H : SimpleGraph (Fin n))
    [DecidableRel G.Adj] [DecidableRel H.Adj] (δ : ℚ)
    (hmin : ∀ Q : CliquePartition G, Q.OrderAtMost 4 →
      (targetSize n : ℚ) - δ ≤ Q.size) :
    ∀ Q : CliquePartition H, Q.OrderAtMost 4 →
      (targetSize n : ℚ) - (δ + 4 * ((G.edgeFinset ∆ H.edgeFinset).card : ℚ))
        ≤ Q.size := by
  classical
  intro Q hQ
  obtain ⟨P,hP,hsize⟩ := E32.exists_partition_of_edit G H Q hQ
  have hp := hmin P hP
  have hs : (P.size : ℚ) ≤ Q.size + (G.edgeFinset \ H.edgeFinset).card +
      4 * (H.edgeFinset \ G.edgeFinset).card := by exact_mod_cast hsize
  have hid : (G.edgeFinset ∆ H.edgeFinset).card =
      (G.edgeFinset \ H.edgeFinset).card + (H.edgeFinset \ G.edgeFinset).card :=
    card_union_of_disjoint disjoint_sdiff_sdiff
  rw [hid]
  push_cast
  have hn : (0 : ℚ) ≤ (G.edgeFinset \ H.edgeFinset).card := Nat.cast_nonneg _
  linarith

theorem baseline_loss_on_shrinking {n : ℕ} (hn : 1 ≤ n)
    {A R : Finset (Fin n)} (hRA : R ⊆ A) :
    splitBaseline n A.card - splitBaseline n R.card ≤
      2 * (n : ℚ) * ((A \ R).card : ℚ) := by
  have hr : R.card ≤ A.card := card_le_card hRA
  have hd : ((A \ R).card : ℚ) = (A.card : ℚ) - R.card := by
    rw [card_sdiff_of_subset hRA, Nat.cast_sub hr]
  have hrq : (R.card : ℚ) ≤ A.card := by exact_mod_cast hr
  have hnq : (1 : ℚ) ≤ n := by exact_mod_cast hn
  have ha0 : (0 : ℚ) ≤ A.card := Nat.cast_nonneg _
  have hr0 : (0 : ℚ) ≤ R.card := Nat.cast_nonneg _
  rw [hd]
  unfold splitBaseline
  nlinarith [mul_nonneg (sub_nonneg.mpr hrq) (by linarith :
    (0 : ℚ) ≤ 2*(n : ℚ) + 3*(A.card : ℚ) + 3*(R.card : ℚ) - 1)]

/-- Explicit loss before choosing epsilon-delta parameters. There is no
chordality assumption on G. The only approximation input is the actual H. -/
theorem stability_via_chordal_edit :
    ∃ N : ℕ, ∀ n s : ℕ, N ≤ n →
    ∀ (G H : SimpleGraph (Fin n)) [DecidableRel G.Adj] [DecidableRel H.Adj],
      RootedDefectAt G s → H.IsChordal → ∀ δ u : ℚ,
      0 ≤ δ → 0 ≤ u →
      2 * ((G.edgeFinset ∆ H.edgeFinset).card : ℚ) ≤ u^2 →
      δ + 4*((G.edgeFinset ∆ H.edgeFinset).card : ℚ) ≤
        IntegralStability.gamma * (n : ℚ)^2 →
      (∀ Q : CliquePartition G, Q.OrderAtMost 4 →
        (targetSize n : ℚ)-δ ≤ Q.size) →
      ∃ R : Finset (Fin n), G.IsClique (R : Set (Fin n)) ∧
        (missingIncidences G R : ℚ) + (outsideEdges G R).card ≤
          16*δ + 65*((G.edgeFinset ∆ H.edgeFinset).card : ℚ) + n*((s : ℚ)+u) ∧
        (targetSize n : ℚ) - splitBaseline n R.card ≤
          δ + 4*((G.edgeFinset ∆ H.edgeFinset).card : ℚ) + 2*n*((s : ℚ)+u) ∧
        ∀ (Q : CliquePartition G) (τ : ℚ), (Q.size : ℚ) ≤ targetSize n + τ →
          ((noncanonicalPieces R Q).card : ℚ) ≤ τ + 49*δ +
            199*((G.edgeFinset ∆ H.edgeFinset).card : ℚ) + 5*n*((s : ℚ)+u) := by
  classical
  obtain ⟨N,hstab⟩ := IntegralStability.chordal_linear_stability_sixteen
  refine ⟨max N 1,?_⟩
  intro n s hn G H _ _ hG hH δ u hδ hu hsq hbudget hmin
  have hN : N ≤ n := (le_max_left _ _).trans hn
  have hn1 : 1 ≤ n := (le_max_right _ _).trans hn
  have ht : (0 : ℚ) ≤ (G.edgeFinset ∆ H.edgeFinset).card := Nat.cast_nonneg _
  obtain ⟨A,hA,_,_,hbase,_,hacct,_⟩ := hstab n hN H hH
    (δ+4*((G.edgeFinset ∆ H.edgeFinset).card : ℚ))
    (by positivity) hbudget (partition_lower_bound_transfers G H δ hmin)
  have hdel : (H.edgeFinset \ G.edgeFinset).card ≤
      (G.edgeFinset ∆ H.edgeFinset).card := by
    apply card_le_card
    intro e he
    exact mem_symmDiff.mpr (Or.inr (mem_sdiff.mp he))
  have hdelq : ((H.edgeFinset \ G.edgeFinset).card : ℚ) ≤
      (G.edgeFinset ∆ H.edgeFinset).card := by exact_mod_cast hdel
  obtain ⟨R,hRA,hR,hremoved⟩ := recover_clique_from_edit G H hG A hA u hu
    (by linarith)
  have hm0 : (0 : ℚ) ≤ missingIncidences H A := Nat.cast_nonneg _
  have ho0 : (0 : ℚ) ≤ (outsideEdges H A).card := Nat.cast_nonneg _
  have hmassH : (missingIncidences H A : ℚ) + (outsideEdges H A).card ≤
      16*(δ+4*((G.edgeFinset ∆ H.edgeFinset).card : ℚ)) := by linarith
  have hgapH : (targetSize n : ℚ)-splitBaseline n A.card ≤
      δ+4*((G.edgeFinset ∆ H.edgeFinset).card : ℚ) := by linarith
  have htr := PaperIV.EditRoute.missingIncidences_add_outsideEdges_le_of_edit
    (G := G) (G' := H) hRA hA
  simp only [Fintype.card_fin] at htr
  have htrq : (missingIncidences G R : ℚ) + (outsideEdges G R).card ≤
      missingIncidences H A + (outsideEdges H A).card +
      (H.edgeFinset \ G.edgeFinset).card + (G.edgeFinset \ H.edgeFinset).card +
      ((A \ R).card : ℚ)*n := by exact_mod_cast htr
  have hid : (G.edgeFinset ∆ H.edgeFinset).card =
      (G.edgeFinset \ H.edgeFinset).card + (H.edgeFinset \ G.edgeFinset).card :=
    card_union_of_disjoint disjoint_sdiff_sdiff
  have hidq : ((G.edgeFinset ∆ H.edgeFinset).card : ℚ) =
      (G.edgeFinset \ H.edgeFinset).card + (H.edgeFinset \ G.edgeFinset).card := by
    exact_mod_cast hid
  have hn0 : (0 : ℚ) ≤ n := Nat.cast_nonneg _
  have hloss := mul_le_mul_of_nonneg_left hremoved hn0
  have hm : (missingIncidences G R : ℚ) + (outsideEdges G R).card ≤
      16*δ+65*((G.edgeFinset ∆ H.edgeFinset).card : ℚ)+n*((s : ℚ)+u) := by
    nlinarith only [htrq,hidq,hmassH,hloss]
  have hbl := baseline_loss_on_shrinking hn1 hRA
  have hg : (targetSize n : ℚ)-splitBaseline n R.card ≤
      δ+4*((G.edgeFinset ∆ H.edgeFinset).card : ℚ)+2*n*((s : ℚ)+u) := by
    nlinarith only [hgapH,hbl,hloss]
  refine ⟨R,hR,hm,hg,?_⟩
  intro Q τ hQ
  have hq := card_noncanonicalPieces_le R hR Q
    ((targetSize n : ℚ)+τ-splitBaseline n R.card) (by simpa using hQ)
  have hmG0 : (0 : ℚ) ≤ missingIncidences G R := Nat.cast_nonneg _
  linarith

end PaperIV.SublinearResearch
#print axioms PaperIV.SublinearResearch.partition_lower_bound_transfers
#print axioms PaperIV.SublinearResearch.baseline_loss_on_shrinking
#print axioms PaperIV.SublinearResearch.stability_via_chordal_edit
