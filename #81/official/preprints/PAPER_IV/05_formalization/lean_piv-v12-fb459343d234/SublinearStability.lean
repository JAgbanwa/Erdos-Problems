import SublinearStabilityTransfer
import SublinearEdit

/-! Uniform sublinear-defect stability in the order-four model.
For each accuracy the defect ratio and the extremality margin are fixed before
the order, graph, and partition. One actual clique root controls all partitions.
This does not assert linear stability in the extremal deficit for growing s.
-/
namespace PaperIV.SublinearResearch
open scoped symmDiff
open Finset PaperIV.FarRounding PaperIV.RootedSimplicialDefect
open PaperIV.RootVocab PaperIV.RootPartitionStability

theorem integral_baseline_le_target (n k : ℕ) :
    splitBaseline (n : ℚ) k ≤ (targetSize n : ℚ) := by
  let S : ℤ := (k : ℤ)*((n : ℤ)-k)-(k.choose 2 : ℤ)
  have hS : (S : ℚ) = splitBaseline (n : ℚ) k := by
    dsimp [S,splitBaseline]
    push_cast
    rw [Nat.cast_choose_two]
  have hle := SplitBaselineTarget.splitBaseline_le_targetSize hS
  have hq : (S : ℚ) ≤ (targetSize n : ℚ) := by exact_mod_cast hle
  rwa [hS] at hq

/-- Complete epsilon-delta statement, uniform over defects s <= theta*n.
The lower bound on c4 is written without assuming a chosen minimizer.
The final universal quantifier ranges over ALL clique partitions of G. -/
theorem uniform_sublinear_stability (ε : ℚ) (hε : 0 < ε) :
    ∃ η θ : ℚ, 0 < η ∧ 0 < θ ∧ ∃ N : ℕ, ∀ n s : ℕ, N ≤ n →
    (s : ℚ) ≤ θ*n → ∀ G : SimpleGraph (Fin n), ∀ [DecidableRel G.Adj],
    RootedDefectAt G s →
    (∀ Q : CliquePartition G, Q.OrderAtMost 4 →
      (targetSize n : ℚ)-η*(n : ℚ)^2 ≤ Q.size) →
    ∃ R : Finset (Fin n), G.IsClique (R : Set (Fin n)) ∧
      (EditMetric.editDist G.edgeFinset
        (GraphFamilyDistance.graphEdgeSupport
          (SplitUniformIncidence.splitGraph R (univ \ R))) : ℚ) ≤ ε*(n : ℚ)^2 ∧
      0 ≤ (targetSize n : ℚ)-splitBaseline n R.card ∧
      (targetSize n : ℚ)-splitBaseline n R.card ≤ ε*(n : ℚ)^2 ∧
      ∀ (Q : CliquePartition G) (τ : ℚ), (Q.size : ℚ) ≤ targetSize n+τ →
        ((noncanonicalPieces R Q).card : ℚ) ≤ τ+ε*(n : ℚ)^2 := by
  classical
  let κ : ℚ := min 1 (min (IntegralStability.gamma/4) (ε/200))
  have hk : 0 < κ := lt_min (by norm_num)
    (lt_min (by exact div_pos IntegralStability.gamma_pos (by norm_num)) (by positivity))
  have hk1 : κ ≤ 1 := min_le_left _ _
  have hkg : κ ≤ IntegralStability.gamma/4 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hke : κ ≤ ε/200 := (min_le_right _ _).trans (min_le_right _ _)
  have hk2 : κ^2 ≤ κ := by nlinarith
  obtain ⟨θ,hθ,Ne,he⟩ := uniform_chordal_edit (κ^2/2) (by positivity)
  obtain ⟨Ns,hstab⟩ := stability_via_chordal_edit
  refine ⟨κ^2,min θ κ,by positivity,lt_min hθ hk,max Ne Ns,?_⟩
  intro n s hn hs G _ hG hmin
  have hNe : Ne ≤ n := (le_max_left _ _).trans hn
  have hNs : Ns ≤ n := (le_max_right _ _).trans hn
  have hn0 : (0 : ℚ) ≤ n := Nat.cast_nonneg _
  have hsθ : (s : ℚ) ≤ θ*n := hs.trans
    (mul_le_mul_of_nonneg_right (min_le_left _ _) hn0)
  have hsκ : (s : ℚ) ≤ κ*n := hs.trans
    (mul_le_mul_of_nonneg_right (min_le_right _ _) hn0)
  obtain ⟨H,hH,hedit⟩ := he n s hNe hsθ G hG
  rw [E34.ncard_eq_editDist, E34.editDist_eq_card] at hedit
  have hsq : 2*((G.edgeFinset ∆ H.edgeFinset).card : ℚ) ≤ (κ*n)^2 := by
    nlinarith only [hedit]
  have hbudget : κ^2*(n : ℚ)^2+4*((G.edgeFinset ∆ H.edgeFinset).card : ℚ) ≤
      IntegralStability.gamma*(n : ℚ)^2 := by
    have hcoef : 3*κ^2 ≤ IntegralStability.gamma := by nlinarith
    have hmul := mul_le_mul_of_nonneg_right hcoef (sq_nonneg (n : ℚ))
    nlinarith only [hedit,hmul]
  obtain ⟨R,hR,hm,hb,hpart⟩ := hstab n s hNs G H hG hH
    (κ^2*(n : ℚ)^2) (κ*n) (by positivity) (by positivity) hsq hbudget hmin
  have hscaled := mul_le_mul_of_nonneg_right hk2 (sq_nonneg (n : ℚ))
  have hescaled := mul_le_mul_of_nonneg_right hke (sq_nonneg (n : ℚ))
  have hsprod := mul_le_mul_of_nonneg_left hsκ hn0
  have hκ0 : 0 ≤ κ*(n : ℚ)^2 := by positivity
  have hmass : (missingIncidences G R : ℚ)+(outsideEdges G R).card ≤ ε*(n : ℚ)^2 := by
    nlinarith only [hm,hedit,hscaled,hescaled,hsprod,hκ0]
  refine ⟨R,hR,?_,sub_nonneg.mpr (integral_baseline_le_target n R.card),?_,?_⟩
  · rw [SplitEditIdentity.editDist_split_eq G hR]
    push_cast
    linarith only [hmass]
  · nlinarith only [hb,hedit,hscaled,hescaled,hsprod,hκ0]
  · intro Q τ hQ
    have hp := hpart Q τ hQ
    nlinarith only [hp,hedit,hscaled,hescaled,hsprod,hκ0]

end PaperIV.SublinearResearch
#print axioms PaperIV.SublinearResearch.integral_baseline_le_target
#print axioms PaperIV.SublinearResearch.uniform_sublinear_stability
