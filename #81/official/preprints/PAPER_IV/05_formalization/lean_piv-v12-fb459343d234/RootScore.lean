import SublinearLocalization

/-! A root chosen once by finite minimization, independently of epsilon and of
every partition. Its nonnegative score retains all three structural budgets.
-/
namespace PaperIV.SublinearResearch
open Finset PaperIV.FarRounding PaperIV.RootedSimplicialDefect
open PaperIV.RootVocab PaperIV.RootPartitionStability

noncomputable def rootScore {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (R : Finset (Fin n)) : ℚ :=
  |(R.card : ℚ)-(n : ℚ)/3| * n +
    ((missingIncidences G R : ℚ)+(outsideEdges G R).card) +
    ((targetSize n : ℚ)-splitBaseline n R.card)

theorem rootScore_components {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (R : Finset (Fin n)) :
    0 ≤ rootScore G R ∧
    |(R.card : ℚ)-(n : ℚ)/3| * n ≤ rootScore G R ∧
    (missingIncidences G R : ℚ)+(outsideEdges G R).card ≤ rootScore G R ∧
    (targetSize n : ℚ)-splitBaseline n R.card ≤ rootScore G R := by
  have hgap := integral_baseline_le_target n R.card
  have hw : 0 ≤ |(R.card : ℚ)-(n : ℚ)/3| * (n : ℚ) := by positivity
  have hm : (0 : ℚ) ≤ missingIncidences G R := Nat.cast_nonneg _
  have ho : (0 : ℚ) ≤ (outsideEdges G R).card := Nat.cast_nonneg _
  dsimp [rootScore]
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem exists_minimum_rootScore {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] :
    ∃ R : Finset (Fin n), G.IsClique (R : Set (Fin n)) ∧
      ∀ S : Finset (Fin n), G.IsClique (S : Set (Fin n)) → rootScore G R ≤ rootScore G S := by
  classical
  let F : Finset (Finset (Fin n)) := univ.filter (fun R => G.IsClique (R : Set (Fin n)))
  have he : (∅ : Finset (Fin n)) ∈ F := by simp [F]
  obtain ⟨R,hR,hm⟩ := exists_min_image F (rootScore G) ⟨∅,he⟩
  exact ⟨R,(mem_filter.mp hR).2,fun S hS => hm S (by simp [F,hS])⟩

theorem rootScore_le_of_localization {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (R : Finset (Fin n)) {ε : ℚ}
    (hn : 1 ≤ n) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hw : |(R.card : ℚ)-(n : ℚ)/3| ≤ ε*n)
    (hm : (missingIncidences G R : ℚ)+(outsideEdges G R).card ≤ ε*(n : ℚ)^2) :
    rootScore G R ≤ 4*ε*(n : ℚ)^2 := by
  have htarget := targetSize_cast_le_continuous n
  have hnq : (1 : ℚ) ≤ n := by exact_mod_cast hn
  have hwin := abs_le.mp hw
  have hsq := mul_nonneg (sub_nonneg.mpr hwin.2) (show 0 ≤ ε*n+((R.card : ℚ)-n/3) by linarith)
  have hprod := mul_nonneg (show 0 ≤ ε*(n : ℚ)^2 by positivity) (show 0 ≤ 1-ε by linarith)
  have hlin := mul_nonneg (show 0 ≤ ε*(n : ℚ) by positivity) (show 0 ≤ (n : ℚ)-1 by linarith)
  have hgap : (targetSize n : ℚ)-splitBaseline n R.card ≤ 2*ε*(n : ℚ)^2 := by
    unfold splitBaseline
    nlinarith only [htarget,hsq,hprod,hlin,hwin.1]
  have hww := mul_le_mul_of_nonneg_right hw (show (0 : ℚ) ≤ n by positivity)
  dsimp [rootScore]
  nlinarith only [hgap,hww,hm]

theorem noncanonical_le_rootScore {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] {R : Finset (Fin n)} (hR : G.IsClique (R : Set (Fin n)))
    (Q : CliquePartition G) (τ : ℚ) (hQ : (Q.size : ℚ) ≤ targetSize n+τ) :
    ((noncanonicalPieces R Q).card : ℚ) ≤ τ+3*rootScore G R := by
  have hb := card_noncanonicalPieces_le R hR Q
    (τ+((targetSize n : ℚ)-splitBaseline n R.card)) (by simp only [Fintype.card_fin]; linarith)
  have hgap := integral_baseline_le_target n R.card
  have hw : 0 ≤ |(R.card : ℚ)-(n : ℚ)/3| * (n : ℚ) := by positivity
  have hm : (0 : ℚ) ≤ missingIncidences G R := Nat.cast_nonneg _
  dsimp [rootScore]
  linarith

end PaperIV.SublinearResearch
