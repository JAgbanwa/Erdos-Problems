/-
A4 at every rooted defect `s`: the literal sharp target reduces to the localized terminal ledger alone.

* `A4Sharp s` — for all large `n`, every graph of rooted defect `≤ s` has a clique partition of order `≤ 4` with at
  most `defectTarget s n = M(n+s) − C(s+1,2)` pieces (for `s = 1` this is `A4S1.DefectOneReduction.A4Sharp₁`).
* `LocalizedTerminal s ε` — the same conclusion for near-extremal graphs (`F4' ≥ n²/6 − εn²`) of rooted defect `≤ s`
  that contain a localized real clique at precision `ε` (for `s = 1` this is `LocalizedTerminalS1 ε`).
* `a4Sharp_of_localizedTerminal` — `LocalizedTerminal s ε` for one `ε > 0` gives `A4Sharp s`. The localization is
  now unconditional (`PaperIV.EditRoute.fixedL4Localization_unconditional`), and the far regime is handled by the
  universal mixed rounding (`farRegime_cliquePartition_allGraphs`), with `M(n) ≤ defectTarget s n`.

So for every `s` the only open input of A4 is the terminal ledger `LocalizedTerminal s ε`.

Layer E (unconditional): axiom target = {propext, Classical.choice, Quot.sound}.
-/
import PaperIV.EditRouteUnconditional
import PaperIV.FarRegimeAllGraphs
import PaperIV.DefectTargetArithmetic
import PaperIV.CertifiedF4Bridge
import PaperIV.CertifiedOptimumExistence

namespace PaperIV.A4AllDefects

open PaperIV.FarRounding PaperIV.RootedSimplicialDefect PaperIV.FixedL4 PaperIV.DefectTargetArithmetic

/-- The literal order-four A4 target at rooted defect `s`. -/
def A4Sharp (s : ℕ) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    RootedDefectAt G s →
      ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size ≤ defectTarget s n

/-- The localized terminal ledger at rooted defect `s`. -/
def LocalizedTerminal (s : ℕ) (eps : ℚ) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    RootedDefectAt G s →
    (n : ℝ) ^ 2 / 6 - (eps : ℝ) * (n : ℝ) ^ 2 ≤ PaperIV.VertexCopyGate.F4' G →
    Nonempty (LocalizedClique G eps) →
      ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size ≤ defectTarget s n

/-- **A4 at every defect from the terminal ledger alone.** -/
theorem a4Sharp_of_localizedTerminal (s : ℕ) {eps : ℚ} (heps : 0 < eps)
    (hterm : LocalizedTerminal s eps) : A4Sharp s := by
  classical
  obtain ⟨eta, heta, NL, hNL⟩ := PaperIV.EditRoute.fixedL4Localization_unconditional s eps heps
  set eta' : ℚ := min eta eps with heta'
  have heta'pos : 0 < eta' := lt_min heta heps
  have h1 : eta' ≤ eta := min_le_left _ _
  have h2 : eta' ≤ eps := min_le_right _ _
  obtain ⟨Nf, hNf⟩ := PaperIV.FarRegimeAllGraphs.farRegime_cliquePartition_allGraphs eta' heta'pos
  obtain ⟨NT, hNT⟩ := hterm
  refine ⟨NL + Nf + NT + s + 2, ?_⟩
  intro n hn G _ hdef
  by_cases hfar : PaperIV.VertexCopyGate.F4' G <
      (n : ℝ) ^ 2 / 6 - (eta' : ℝ) * (n : ℝ) ^ 2
  · obtain ⟨Q, hQ4, hQs⟩ := hNf n (by omega) G hfar
    exact ⟨Q, hQ4, le_trans hQs (targetSize_le_defectTarget s n (by omega))⟩
  push_neg at hfar
  have hsqR : (0 : ℝ) ≤ (n : ℝ) ^ 2 := by positivity
  have h1R : (eta' : ℝ) ≤ (eta : ℝ) := by exact_mod_cast h1
  have h2R : (eta' : ℝ) ≤ (eps : ℝ) := by exact_mod_cast h2
  have hfarEps : (n : ℝ) ^ 2 / 6 - (eps : ℝ) * (n : ℝ) ^ 2 ≤ PaperIV.VertexCopyGate.F4' G := by
    nlinarith
  obtain ⟨w, hw⟩ := PaperIV.CertifiedOptimumExistence.exists_certifiedFractionalOptimum G
  have hF := PaperIV.CertifiedF4Bridge.F4'_eq_edge_sub_certified hw
  have hnear : (n : ℚ) ^ 2 / 6 - eta * (n : ℚ) ^ 2 ≤ (G.edgeFinset.card : ℚ) - w := by
    have hR : (n : ℝ) ^ 2 / 6 - (eta : ℝ) * (n : ℝ) ^ 2 ≤
        (((G.edgeFinset.card : ℚ) - w : ℚ) : ℝ) := by
      rw [← hF]; nlinarith
    have h : ((((n : ℚ) ^ 2 / 6 - eta * (n : ℚ) ^ 2 : ℚ)) : ℝ) ≤
        (((G.edgeFinset.card : ℚ) - w : ℚ) : ℝ) := by
      push_cast at hR ⊢; linarith
    exact_mod_cast h
  exact hNT n (by omega) G hdef hfarEps (hNL n (by omega) G hdef w hw hnear)

end PaperIV.A4AllDefects
