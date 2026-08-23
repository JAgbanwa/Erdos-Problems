/-
# Paper III — AX1 bridge from the standalone nibble project

This module converts the nibble AX1 reduction to the exact AX1-shaped theorem consumed by
the Paper III assembly.  The only remaining mathematical inputs are the nibble theorem and
the near-regularity obligation; strong duality is imported as a theorem from `nibble`.
-/
import PaperIII.AX1Bridge
import Nibble.NibbleGapReduction
import Nibble.StrongDualityInst
import Nibble.YusterBridgePacking
import Nibble.DenseGapAX1

namespace PaperIII

/-- Paper III AX1 assembled from the nibble theorem, strong duality, and near-regularity. -/
theorem AX1_from_nibbleTheorem_and_regularity
    (hNib : Nibble.NibbleTheoremMost)
    (hReg : ∀ μ η d₀ : ℝ, 0 < μ → 0 < η → 0 < d₀ →
      Nibble.AX1.NearRegObligation μ η d₀) :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ,
      ∀ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
        (G : SimpleGraph V) (_ : DecidableRel G.Adj),
        n₀ ≤ Fintype.card V →
        tau3Star G - (nu3 G : ℝ) ≤ ε * (Fintype.card V : ℝ) ^ 2 := by
  intro ε hε
  obtain ⟨n₀, hn₀⟩ :=
    Nibble.AX1.ax1_of_nibbleTheorem_strongDuality_regularity
      hNib Nibble.AX1.strongDualityHyp_holds hReg ε hε
  refine ⟨n₀, ?_⟩
  intro V _ _ G _ hV
  have h := hn₀ V G hV
  have hnu : Nibble.YusterE.nu3 G = nu3 G := by
    rw [nu3]
    exact Nibble.YusterE.nu3_eq_trianglePacking_sSup G
  rw [hnu] at h
  simpa using h

/-- Paper III AX1 assembled from the ceiling-aware nibble theorem, strong duality, and
near-regularity. This is the corrected endpoint for the Freedman route because the ② obligation
supplies the global degree ceiling. -/
theorem AX1_from_nibbleTheoremCeil_and_regularity
    (hNib : Nibble.NibbleTheoremMostCeil)
    (hReg : ∀ μ η d₀ : ℝ, 0 < μ → 0 < η → 0 < d₀ →
      Nibble.AX1.NearRegObligation μ η d₀) :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ,
      ∀ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
        (G : SimpleGraph V) (_ : DecidableRel G.Adj),
        n₀ ≤ Fintype.card V →
        tau3Star G - (nu3 G : ℝ) ≤ ε * (Fintype.card V : ℝ) ^ 2 := by
  intro ε hε
  obtain ⟨n₀, hn₀⟩ :=
    Nibble.AX1.ax1_of_nibbleTheoremCeil_strongDuality_regularity
      hNib Nibble.AX1.strongDualityHyp_holds hReg ε hε
  refine ⟨n₀, ?_⟩
  intro V _ _ G _ hV
  have h := hn₀ V G hV
  have hnu : Nibble.YusterE.nu3 G = nu3 G := by
    rw [nu3]
    exact Nibble.YusterE.nu3_eq_trianglePacking_sSup G
  rw [hnu] at h
  simpa using h

/-- Paper III AX1 assembled from the sized ceiling-aware nibble theorem, strong duality, and
near-regularity with the triangle-specific size bound. -/
theorem AX1_from_nibbleTheoremCeilSized_and_regularity
    (hNib : Nibble.NibbleTheoremMostCeilSized)
    (hReg : ∀ μ η d₀ K : ℝ, 0 < μ → 0 < η → 0 < d₀ → 0 < K →
      Nibble.AX1.NearRegObligationSized μ η d₀ K) :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ,
      ∀ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
        (G : SimpleGraph V) (_ : DecidableRel G.Adj),
        n₀ ≤ Fintype.card V →
        tau3Star G - (nu3 G : ℝ) ≤ ε * (Fintype.card V : ℝ) ^ 2 := by
  intro ε hε
  obtain ⟨n₀, hn₀⟩ :=
    Nibble.AX1.ax1_of_nibbleTheoremCeilSized_strongDuality_regularity
      hNib Nibble.AX1.strongDualityHyp_holds hReg ε hε
  refine ⟨n₀, ?_⟩
  intro V _ _ G _ hV
  have h := hn₀ V G hV
  have hnu : Nibble.YusterE.nu3 G = nu3 G := by
    rw [nu3]
    exact Nibble.YusterE.nu3_eq_trianglePacking_sSup G
  rw [hnu] at h
  simpa using h

/-- Paper III AX1 assembled from the sized ceiling-aware nibble theorem and the dense-regime
linear-size form of the regularity obligation. -/
theorem AX1_from_nibbleTheoremCeilSized_and_linearRegularity
    (hNib : Nibble.NibbleTheoremMostCeilSized)
    (hReg : ∀ μ η d₀ L : ℝ, 0 < μ → 0 < η → 0 < d₀ → 0 < L →
      Nibble.AX1.NearRegObligationLinearSized μ η d₀ L) :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ,
      ∀ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
        (G : SimpleGraph V) (_ : DecidableRel G.Adj),
        n₀ ≤ Fintype.card V →
        tau3Star G - (nu3 G : ℝ) ≤ ε * (Fintype.card V : ℝ) ^ 2 := by
  intro ε hε
  obtain ⟨n₀, hn₀⟩ :=
    Nibble.AX1.ax1_of_nibbleTheoremCeilSized_strongDuality_linearRegularity
      hNib Nibble.AX1.strongDualityHyp_holds hReg ε hε
  refine ⟨n₀, ?_⟩
  intro V _ _ G _ hV
  have h := hn₀ V G hV
  have hnu : Nibble.YusterE.nu3 G = nu3 G := by
    rw [nu3]
    exact Nibble.YusterE.nu3_eq_trianglePacking_sSup G
  rw [hnu] at h
  simpa using h

/-- Paper III AX1 assembled from the single honest nibble residual `NibbleGapResidual` (the
non-dense, triangle-rich case of Haxell–Rödl).  The dense and triangle-poor branches are discharged
unconditionally inside `Nibble.AX1.ax1_holds_of_residual`; strong duality is internal. -/
theorem AX1_from_residual (hres : Nibble.AX1.NibbleGapResidual) :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ,
      ∀ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
        (G : SimpleGraph V) (_ : DecidableRel G.Adj),
        n₀ ≤ Fintype.card V →
        tau3Star G - (nu3 G : ℝ) ≤ ε * (Fintype.card V : ℝ) ^ 2 := by
  intro ε hε
  obtain ⟨n₀, hn₀⟩ := Nibble.AX1.ax1_holds_of_residual hres ε hε
  refine ⟨n₀, ?_⟩
  intro V _ _ G _ hV
  have h := hn₀ V G hV
  have hnu : Nibble.YusterE.nu3 G = nu3 G := by
    rw [nu3]
    exact Nibble.YusterE.nu3_eq_trianglePacking_sSup G
  rw [hnu] at h
  simpa using h

end PaperIII
