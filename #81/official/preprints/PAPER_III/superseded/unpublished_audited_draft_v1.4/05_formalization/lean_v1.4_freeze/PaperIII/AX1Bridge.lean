/-
# Paper III — AX1 assembly from its two final components

This is the PaperIII-native version of the AX1 final assembly. The mathematical
components are isolated as hypotheses so the theorem can be wired directly once
the standalone nibble development exports the matching PaperIII statements.
-/
import PaperIII.AXDefs

namespace PaperIII

/-- Cover-side strong duality for the triangle LP: `τ₃* ≤ ν₃*`. -/
def StrongDualityHyp : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    tau3Star G ≤ nu3Star G

/-- The unconditional fractional-to-integral triangle-packing gap. -/
def NibbleGapHyp : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ,
    ∀ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
      (G : SimpleGraph V) (_ : DecidableRel G.Adj),
      n₀ ≤ Fintype.card V →
      nu3Star G - (nu3 G : ℝ) ≤ ε * (Fintype.card V : ℝ) ^ 2

/-- Paper III's AX1 statement assembled from strong duality plus the nibble gap. -/
theorem AX1_from_strongDuality_and_nibbleGap
    (hdual : StrongDualityHyp) (hgap : NibbleGapHyp) :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ,
      ∀ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
        (G : SimpleGraph V) (_ : DecidableRel G.Adj),
        n₀ ≤ Fintype.card V →
        tau3Star G - (nu3 G : ℝ) ≤ ε * (Fintype.card V : ℝ) ^ 2 := by
  intro ε hε
  obtain ⟨n₀, hn₀⟩ := hgap ε hε
  refine ⟨n₀, ?_⟩
  intro V _ _ G _ hV
  have hgapG := hn₀ V inferInstance inferInstance G inferInstance hV
  have hdualG := hdual G
  linarith

end PaperIII
