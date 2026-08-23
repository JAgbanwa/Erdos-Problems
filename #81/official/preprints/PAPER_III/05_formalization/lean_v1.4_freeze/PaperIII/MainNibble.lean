/-
# Paper III — final assembly through the standalone nibble AX1 bridge

This module keeps the heavy `PaperIII.Main` file unchanged and adds the AX1-free wrappers in a small
assembly layer. The only inputs are the standalone nibble theorem and the dense-regime
near-regularity obligation.
-/
import PaperIII.Main
import PaperIII.AX1NibbleBridge
import Nibble.MostAssemblyFreedman

namespace PaperIII

open SplitGraph

/-- Paper III AX1 from the final concrete Freedman residual pair and linear-sized regularity. -/
theorem AX1_from_freedmanConcreteBadRound_linearRegularity
    (hBadRound : ∀ r : ℕ, 2 ≤ r → ∀ β : ℝ, 0 < β →
      ∃ d₀ : ℝ, 0 < d₀ ∧
        Nibble.FreedmanCardExplicitBadRoundCore Nibble.freedmanExplicitP Nibble.freedmanExplicitC
          Nibble.freedmanExplicitLam Nibble.freedmanExplicitT r β ((1 : ℝ) / 100)
          (min (β / 4) ((1 : ℝ) / 100)) d₀ 1)
    (hReg : ∀ μ η d₀ L : ℝ, 0 < μ → 0 < η → 0 < d₀ → 0 < L →
      Nibble.AX1.NearRegObligationLinearSized μ η d₀ L) :
    AX1Assumption :=
  AX1_from_nibbleTheoremCeilSized_and_linearRegularity
    (Nibble.nibbleTheoremMostCeilSized_of_freedman_concrete_badRound hBadRound) hReg

/-- Paper III AX1 from the two final concrete Freedman residual halves and linear-sized regularity. -/
theorem AX1_from_freedmanConcreteBadEventRoundIneq_linearRegularity
    (hBadEvent : ∀ r : ℕ, 2 ≤ r → ∀ β : ℝ, 0 < β →
      ∃ d₀ : ℝ, 0 < d₀ ∧
        Nibble.FreedmanCardExplicitBadEventCore Nibble.freedmanExplicitP Nibble.freedmanExplicitC
          r β ((1 : ℝ) / 100) d₀ 1)
    (hRoundIneq : ∀ r : ℕ, 2 ≤ r → ∀ β : ℝ, 0 < β →
      ∃ d₀ : ℝ, 0 < d₀ ∧
        Nibble.FreedmanCardExplicitRoundIneqCore Nibble.freedmanExplicitP Nibble.freedmanExplicitC
          Nibble.freedmanExplicitLam Nibble.freedmanExplicitT r β ((1 : ℝ) / 100)
          (min (β / 4) ((1 : ℝ) / 100)) d₀ 1)
    (hReg : ∀ μ η d₀ L : ℝ, 0 < μ → 0 < η → 0 < d₀ → 0 < L →
      Nibble.AX1.NearRegObligationLinearSized μ η d₀ L) :
    AX1Assumption := by
  refine AX1_from_freedmanConcreteBadRound_linearRegularity ?_ hReg
  intro r hr β hβ
  obtain ⟨dB, hdB, hB⟩ := hBadEvent r hr β hβ
  obtain ⟨dR, hdR, hR⟩ := hRoundIneq r hr β hβ
  refine ⟨max dB dR, lt_of_lt_of_le hdB (le_max_left _ _), ?_⟩
  exact Nibble.freedmanCardExplicitBadRoundCore_of_badEvent_roundIneq
    (fun N d hd hd0 hsize => hB N d hd (le_trans (le_max_left dB dR) hd0) hsize)
    (fun N d hd hd0 hsize => hR N d hd (le_trans (le_max_right dB dR) hd0) hsize)

/-- Theorem 1.1 assembled from standalone nibble AX1 and an external AX2 input. This is the
AX1/AX2-free final assembly surface: once both inputs are supplied by closed modules, this
wrapper does not instantiate the local Layer-X axioms. -/
theorem Theorem_1_1_of_nibble_linearRegularity_AX2
    (hNib : Nibble.NibbleTheoremMostCeilSized)
    (hReg : ∀ μ η d₀ L : ℝ, 0 < μ → 0 < η → 0 < d₀ → 0 < L →
      Nibble.AX1.NearRegObligationLinearSized μ η d₀ L)
    (hAX2 : AX2Assumption) :
    ∃ C : ℝ, ∀ G : SplitGraph, ((G.Phi : ℤ) : ℝ) ≤ (G.n : ℝ) ^ 2 / 6 + C * (G.n : ℝ) :=
  Theorem_1_1_of_AX1_AX2
    (AX1_from_nibbleTheoremCeilSized_and_linearRegularity hNib hReg)
    hAX2

/-- Theorem 1.1 from the axiom-clean Freedman parameter-core interface. This names all remaining
mathematical inputs explicitly and avoids the old direct parameter theorem. -/
theorem Theorem_1_1_of_freedmanCore_linearRegularity_AX2
    (hCore : ∀ r : ℕ, 2 ≤ r → ∀ β : ℝ, 0 < β →
      Nibble.FreedmanSizedParameterCore r β ((1 : ℝ) / 100)
        (min (β / 4) ((1 : ℝ) / 100)) 1)
    (hReg : ∀ μ η d₀ L : ℝ, 0 < μ → 0 < η → 0 < d₀ → 0 < L →
      Nibble.AX1.NearRegObligationLinearSized μ η d₀ L)
    (hAX2 : AX2Assumption) :
    ∃ C : ℝ, ∀ G : SplitGraph, ((G.Phi : ℤ) : ℝ) ≤ (G.n : ℝ) ^ 2 / 6 + C * (G.n : ℝ) :=
  Theorem_1_1_of_nibble_linearRegularity_AX2
    (Nibble.nibbleTheoremMostCeilSized_of_freedman_core hCore) hReg hAX2

/-- Theorem 1.1 from the axiom-clean thresholded Freedman parameter-core interface. This is the
asymptotic version needed by the nibble theorem: the remaining parameter choice may select a degree
threshold before proving the Freedman inequalities. -/
theorem Theorem_1_1_of_freedmanThresholdCore_linearRegularity_AX2
    (hCore : ∀ r : ℕ, 2 ≤ r → ∀ β : ℝ, 0 < β →
      ∃ d₀ : ℝ, 0 < d₀ ∧
        Nibble.FreedmanSizedThresholdParameterCore r β ((1 : ℝ) / 100)
          (min (β / 4) ((1 : ℝ) / 100)) d₀ 1)
    (hReg : ∀ μ η d₀ L : ℝ, 0 < μ → 0 < η → 0 < d₀ → 0 < L →
      Nibble.AX1.NearRegObligationLinearSized μ η d₀ L)
    (hAX2 : AX2Assumption) :
    ∃ C : ℝ, ∀ G : SplitGraph, ((G.Phi : ℤ) : ℝ) ≤ (G.n : ℝ) ^ 2 / 6 + C * (G.n : ℝ) :=
  Theorem_1_1_of_nibble_linearRegularity_AX2
    (Nibble.nibbleTheoremMostCeilSized_of_freedman_threshold_core hCore) hReg hAX2

/-- Theorem 1.1 from the ceiled Freedman parameter core. This is the same final assembly as the
threshold-core wrapper, but the remaining nibble obligation no longer chooses the integer degree
ceiling: it is fixed as `Nat.ceil ((1 + μ) * d)`. -/
theorem Theorem_1_1_of_freedmanCeilCore_linearRegularity_AX2
    (hCore : ∀ r : ℕ, 2 ≤ r → ∀ β : ℝ, 0 < β →
      ∃ d₀ : ℝ, 0 < d₀ ∧
        Nibble.FreedmanCeilThresholdParameterCore r β ((1 : ℝ) / 100)
          (min (β / 4) ((1 : ℝ) / 100)) d₀ 1)
    (hReg : ∀ μ η d₀ L : ℝ, 0 < μ → 0 < η → 0 < d₀ → 0 < L →
      Nibble.AX1.NearRegObligationLinearSized μ η d₀ L)
    (hAX2 : AX2Assumption) :
    ∃ C : ℝ, ∀ G : SplitGraph, ((G.Phi : ℤ) : ℝ) ≤ (G.n : ℝ) ^ 2 / 6 + C * (G.n : ℝ) := by
  exact Theorem_1_1_of_freedmanThresholdCore_linearRegularity_AX2
    (fun r hr β hβ =>
      let μ : ℝ := (1 : ℝ) / 100
      have hμ : 0 < μ := by norm_num [μ]
      let η : ℝ := min (β / 4) ((1 : ℝ) / 100)
      let hceil := hCore r hr β hβ
      hceil.imp fun d₀ hd =>
        ⟨hd.1, Nibble.freedmanSizedThresholdParameterCore_of_ceil (r := r) (β := β)
          (μ := μ) (η := η) (d₀ := d₀) (K := 1) hμ hd.2⟩)
    hReg hAX2

/-- Theorem 1.1 from the fully numeric ceiled Freedman parameter core. The nibble-side remaining
obligation has no hypergraph input: it only chooses `p,c,lam,T` from `r,β,|V|,d` with
`|V| ≤ d^2`. -/
theorem Theorem_1_1_of_freedmanNumericCore_linearRegularity_AX2
    (hCore : ∀ r : ℕ, 2 ≤ r → ∀ β : ℝ, 0 < β →
      ∃ d₀ : ℝ, 0 < d₀ ∧
        Nibble.FreedmanCeilNumericThresholdParameterCore r β ((1 : ℝ) / 100)
          (min (β / 4) ((1 : ℝ) / 100)) d₀ 1)
    (hReg : ∀ μ η d₀ L : ℝ, 0 < μ → 0 < η → 0 < d₀ → 0 < L →
      Nibble.AX1.NearRegObligationLinearSized μ η d₀ L)
    (hAX2 : AX2Assumption) :
    ∃ C : ℝ, ∀ G : SplitGraph, ((G.Phi : ℤ) : ℝ) ≤ (G.n : ℝ) ^ 2 / 6 + C * (G.n : ℝ) := by
  exact Theorem_1_1_of_freedmanCeilCore_linearRegularity_AX2
    (fun r hr β hβ =>
      (hCore r hr β hβ).imp fun d₀ hd =>
        ⟨hd.1, Nibble.freedmanCeilThresholdParameterCore_of_numeric hd.2⟩)
    hReg hAX2

/-- Theorem 1.1 from the type-free cardinal numeric Freedman parameter core. This is the smallest
current nibble-side residual: a pure real/natural-number parameter selection with ambient size `N`. -/
theorem Theorem_1_1_of_freedmanCardCore_linearRegularity_AX2
    (hCore : ∀ r : ℕ, 2 ≤ r → ∀ β : ℝ, 0 < β →
      ∃ d₀ : ℝ, 0 < d₀ ∧
        Nibble.FreedmanCardNumericThresholdParameterCore r β ((1 : ℝ) / 100)
          (min (β / 4) ((1 : ℝ) / 100)) d₀ 1)
    (hReg : ∀ μ η d₀ L : ℝ, 0 < μ → 0 < η → 0 < d₀ → 0 < L →
      Nibble.AX1.NearRegObligationLinearSized μ η d₀ L)
    (hAX2 : AX2Assumption) :
    ∃ C : ℝ, ∀ G : SplitGraph, ((G.Phi : ℤ) : ℝ) ≤ (G.n : ℝ) ^ 2 / 6 + C * (G.n : ℝ) := by
  exact Theorem_1_1_of_freedmanNumericCore_linearRegularity_AX2
    (fun r hr β hβ =>
      (hCore r hr β hβ).imp fun d₀ hd =>
        ⟨hd.1, Nibble.freedmanCeilNumericThresholdParameterCore_of_card hd.2⟩)
    hReg hAX2

/-- Theorem 1.1 from an explicit type-free Freedman parameter choice. This is the narrowest current
AX1-side interface: the remaining nibble work is to provide concrete functions `p,c,lam,T` and prove
their real/natural-number inequalities. -/
theorem Theorem_1_1_of_freedmanExplicitCardCore_linearRegularity_AX2
    (p c lam : ℕ → ℝ → ℕ → ℝ → ℝ) (T : ℕ → ℝ → ℕ → ℝ → ℕ)
    (hCore : ∀ r : ℕ, 2 ≤ r → ∀ β : ℝ, 0 < β →
      ∃ d₀ : ℝ, 0 < d₀ ∧
        Nibble.FreedmanCardExplicitParameterCore p c lam T r β ((1 : ℝ) / 100)
          (min (β / 4) ((1 : ℝ) / 100)) d₀ 1)
    (hReg : ∀ μ η d₀ L : ℝ, 0 < μ → 0 < η → 0 < d₀ → 0 < L →
      Nibble.AX1.NearRegObligationLinearSized μ η d₀ L)
    (hAX2 : AX2Assumption) :
    ∃ C : ℝ, ∀ G : SplitGraph, ((G.Phi : ℤ) : ℝ) ≤ (G.n : ℝ) ^ 2 / 6 + C * (G.n : ℝ) := by
  exact Theorem_1_1_of_freedmanCardCore_linearRegularity_AX2
    (fun r hr β hβ =>
      (hCore r hr β hβ).imp fun d₀ hd =>
        ⟨hd.1, Nibble.freedmanCardNumericThresholdParameterCore_of_explicit hd.2⟩)
    hReg hAX2

/-- Theorem 1.1 from the split explicit type-free Freedman parameter core. This exposes the
remaining AX1-side checks as three independent real/natural-number obligations. -/
theorem Theorem_1_1_of_freedmanSplitExplicitCore_linearRegularity_AX2
    (p c lam : ℕ → ℝ → ℕ → ℝ → ℝ) (T : ℕ → ℝ → ℕ → ℝ → ℕ)
    (hCore : ∀ r : ℕ, 2 ≤ r → ∀ β : ℝ, 0 < β →
      ∃ d₀ : ℝ, 0 < d₀ ∧
        Nibble.FreedmanCardExplicitSplitCore p c lam T r β ((1 : ℝ) / 100)
          (min (β / 4) ((1 : ℝ) / 100)) d₀ 1)
    (hReg : ∀ μ η d₀ L : ℝ, 0 < μ → 0 < η → 0 < d₀ → 0 < L →
      Nibble.AX1.NearRegObligationLinearSized μ η d₀ L)
    (hAX2 : AX2Assumption) :
    ∃ C : ℝ, ∀ G : SplitGraph, ((G.Phi : ℤ) : ℝ) ≤ (G.n : ℝ) ^ 2 / 6 + C * (G.n : ℝ) := by
  exact Theorem_1_1_of_freedmanExplicitCardCore_linearRegularity_AX2 p c lam T
    (fun r hr β hβ =>
      (hCore r hr β hβ).imp fun d₀ hd =>
        ⟨hd.1, Nibble.freedmanCardExplicitParameterCore_of_split hd.2⟩)
    hReg hAX2

/-- Theorem 1.1 from the split explicit Freedman core through the direct nibble theorem wrapper. -/
theorem Theorem_1_1_of_freedmanSplitExplicitNibble_linearRegularity_AX2
    (p c lam : ℕ → ℝ → ℕ → ℝ → ℝ) (T : ℕ → ℝ → ℕ → ℝ → ℕ)
    (hCore : ∀ r : ℕ, 2 ≤ r → ∀ β : ℝ, 0 < β →
      ∃ d₀ : ℝ, 0 < d₀ ∧
        Nibble.FreedmanCardExplicitSplitCore p c lam T r β ((1 : ℝ) / 100)
          (min (β / 4) ((1 : ℝ) / 100)) d₀ 1)
    (hReg : ∀ μ η d₀ L : ℝ, 0 < μ → 0 < η → 0 < d₀ → 0 < L →
      Nibble.AX1.NearRegObligationLinearSized μ η d₀ L)
    (hAX2 : AX2Assumption) :
    ∃ C : ℝ, ∀ G : SplitGraph, ((G.Phi : ℤ) : ℝ) ≤ (G.n : ℝ) ^ 2 / 6 + C * (G.n : ℝ) :=
  Theorem_1_1_of_nibble_linearRegularity_AX2
    (Nibble.nibbleTheoremMostCeilSized_of_freedman_split_explicit_core p c lam T hCore)
    hReg hAX2

/-- Theorem 1.1 from the factored split explicit Freedman core. -/
theorem Theorem_1_1_of_freedmanSplitFactoredNibble_linearRegularity_AX2
    (p c lam : ℕ → ℝ → ℕ → ℝ → ℝ) (T : ℕ → ℝ → ℕ → ℝ → ℕ)
    (hCore : ∀ r : ℕ, 2 ≤ r → ∀ β : ℝ, 0 < β →
      ∃ d₀ : ℝ, 0 < d₀ ∧
        Nibble.FreedmanCardExplicitSplitFactoredCore p c lam T r β ((1 : ℝ) / 100)
          (min (β / 4) ((1 : ℝ) / 100)) d₀ 1)
    (hReg : ∀ μ η d₀ L : ℝ, 0 < μ → 0 < η → 0 < d₀ → 0 < L →
      Nibble.AX1.NearRegObligationLinearSized μ η d₀ L)
    (hAX2 : AX2Assumption) :
    ∃ C : ℝ, ∀ G : SplitGraph, ((G.Phi : ℤ) : ℝ) ≤ (G.n : ℝ) ^ 2 / 6 + C * (G.n : ℝ) :=
  Theorem_1_1_of_freedmanSplitExplicitNibble_linearRegularity_AX2 p c lam T
    (fun r hr β hβ =>
      (hCore r hr β hβ).imp fun d₀ hd =>
        ⟨hd.1, Nibble.freedmanCardExplicitSplitCore_of_factored hd.2⟩)
    hReg hAX2

/-- Theorem 1.1 from the card-penalty split explicit Freedman core. -/
theorem Theorem_1_1_of_freedmanSplitCardPenaltyNibble_linearRegularity_AX2
    (p c lam : ℕ → ℝ → ℕ → ℝ → ℝ) (T : ℕ → ℝ → ℕ → ℝ → ℕ)
    (hCore : ∀ r : ℕ, 2 ≤ r → ∀ β : ℝ, 0 < β →
      ∃ d₀ : ℝ, 0 < d₀ ∧
        Nibble.FreedmanCardExplicitSplitCardPenaltyCore p c lam T r β ((1 : ℝ) / 100)
          (min (β / 4) ((1 : ℝ) / 100)) d₀ 1)
    (hReg : ∀ μ η d₀ L : ℝ, 0 < μ → 0 < η → 0 < d₀ → 0 < L →
      Nibble.AX1.NearRegObligationLinearSized μ η d₀ L)
    (hAX2 : AX2Assumption) :
    ∃ C : ℝ, ∀ G : SplitGraph, ((G.Phi : ℤ) : ℝ) ≤ (G.n : ℝ) ^ 2 / 6 + C * (G.n : ℝ) :=
  Theorem_1_1_of_freedmanSplitFactoredNibble_linearRegularity_AX2 p c lam T
    (fun r hr β hβ =>
      (hCore r hr β hβ).imp fun d₀ hd =>
        ⟨hd.1, Nibble.freedmanCardExplicitSplitFactoredCore_of_cardPenalty hd.2⟩)
    hReg hAX2

/-- Theorem 1.1 from the scalar gain-lower explicit Freedman core. -/
theorem Theorem_1_1_of_freedmanSplitGainLowerNibble_linearRegularity_AX2
    (p c lam : ℕ → ℝ → ℕ → ℝ → ℝ) (T : ℕ → ℝ → ℕ → ℝ → ℕ)
    (hCore : ∀ r : ℕ, 2 ≤ r → ∀ β : ℝ, 0 < β →
      ∃ d₀ : ℝ, 0 < d₀ ∧
        Nibble.FreedmanCardExplicitSplitGainLowerCore p c lam T r β ((1 : ℝ) / 100)
          (min (β / 4) ((1 : ℝ) / 100)) d₀ 1)
    (hReg : ∀ μ η d₀ L : ℝ, 0 < μ → 0 < η → 0 < d₀ → 0 < L →
      Nibble.AX1.NearRegObligationLinearSized μ η d₀ L)
    (hAX2 : AX2Assumption) :
    ∃ C : ℝ, ∀ G : SplitGraph, ((G.Phi : ℤ) : ℝ) ≤ (G.n : ℝ) ^ 2 / 6 + C * (G.n : ℝ) :=
  Theorem_1_1_of_freedmanSplitCardPenaltyNibble_linearRegularity_AX2 p c lam T
    (fun r hr β hβ =>
      (hCore r hr β hβ).imp fun d₀ hd =>
        ⟨hd.1, Nibble.freedmanCardExplicitSplitCardPenaltyCore_of_gainLower hd.2⟩)
    hReg hAX2

/-- Theorem 1.1 from the proxy-nonnegative plus scalar-lower explicit Freedman core. -/
theorem Theorem_1_1_of_freedmanSplitProxyScalarNibble_linearRegularity_AX2
    (p c lam : ℕ → ℝ → ℕ → ℝ → ℝ) (T : ℕ → ℝ → ℕ → ℝ → ℕ)
    (hCore : ∀ r : ℕ, 2 ≤ r → ∀ β : ℝ, 0 < β →
      ∃ d₀ : ℝ, 0 < d₀ ∧
        Nibble.FreedmanCardExplicitSplitProxyScalarCore p c lam T r β ((1 : ℝ) / 100)
          (min (β / 4) ((1 : ℝ) / 100)) d₀ 1)
    (hReg : ∀ μ η d₀ L : ℝ, 0 < μ → 0 < η → 0 < d₀ → 0 < L →
      Nibble.AX1.NearRegObligationLinearSized μ η d₀ L)
    (hAX2 : AX2Assumption) :
    ∃ C : ℝ, ∀ G : SplitGraph, ((G.Phi : ℤ) : ℝ) ≤ (G.n : ℝ) ^ 2 / 6 + C * (G.n : ℝ) := by
  exact Theorem_1_1_of_freedmanSplitGainLowerNibble_linearRegularity_AX2 p c lam T
    (fun r hr β hβ =>
      (hCore r hr β hβ).imp fun d₀ hd =>
        ⟨hd.1, Nibble.freedmanCardExplicitSplitGainLowerCore_of_proxyScalar hd.2⟩)
    hReg hAX2

/-- Theorem 1.1 from the proxy-nonnegative plus factored-round-inequality Freedman core. -/
theorem Theorem_1_1_of_freedmanSplitProxyIneqNibble_linearRegularity_AX2
    (p c lam : ℕ → ℝ → ℕ → ℝ → ℝ) (T : ℕ → ℝ → ℕ → ℝ → ℕ)
    (hCore : ∀ r : ℕ, 2 ≤ r → ∀ β : ℝ, 0 < β →
      ∃ d₀ : ℝ, 0 < d₀ ∧
        Nibble.FreedmanCardExplicitSplitProxyIneqCore p c lam T r β ((1 : ℝ) / 100)
          (min (β / 4) ((1 : ℝ) / 100)) d₀ 1)
    (hReg : ∀ μ η d₀ L : ℝ, 0 < μ → 0 < η → 0 < d₀ → 0 < L →
      Nibble.AX1.NearRegObligationLinearSized μ η d₀ L)
    (hAX2 : AX2Assumption) :
    ∃ C : ℝ, ∀ G : SplitGraph, ((G.Phi : ℤ) : ℝ) ≤ (G.n : ℝ) ^ 2 / 6 + C * (G.n : ℝ) := by
  exact Theorem_1_1_of_freedmanSplitFactoredNibble_linearRegularity_AX2 p c lam T
    (fun r hr β hβ =>
      (hCore r hr β hβ).imp fun d₀ hd =>
        ⟨hd.1, Nibble.freedmanCardExplicitSplitFactoredCore_of_proxyIneq hd.2⟩)
    hReg hAX2

/-- Theorem 1.1 from the remaining bad-event plus factored-round-inequality Freedman core, after
basic parameter facts and proxy nonnegativity have been discharged separately. -/
theorem Theorem_1_1_of_freedmanBadRoundNibble_linearRegularity_AX2
    (p c lam : ℕ → ℝ → ℕ → ℝ → ℝ) (T : ℕ → ℝ → ℕ → ℝ → ℕ)
    (hBasic : ∀ r : ℕ, 2 ≤ r → ∀ β : ℝ, 0 < β →
      ∃ d₀ : ℝ, 0 < d₀ ∧
        Nibble.FreedmanCardExplicitBasicCore p c lam T r β ((1 : ℝ) / 100) d₀ 1)
    (hProxy : ∀ r : ℕ, 2 ≤ r → ∀ β : ℝ, 0 < β →
      ∃ d₀ : ℝ, 0 < d₀ ∧
        Nibble.FreedmanCardExplicitDegreeProxyNonnegCore p c T r β ((1 : ℝ) / 100) d₀ 1)
    (hBadRound : ∀ r : ℕ, 2 ≤ r → ∀ β : ℝ, 0 < β →
      ∃ d₀ : ℝ, 0 < d₀ ∧
        Nibble.FreedmanCardExplicitBadRoundCore p c lam T r β ((1 : ℝ) / 100)
          (min (β / 4) ((1 : ℝ) / 100)) d₀ 1)
    (hReg : ∀ μ η d₀ L : ℝ, 0 < μ → 0 < η → 0 < d₀ → 0 < L →
      Nibble.AX1.NearRegObligationLinearSized μ η d₀ L)
    (hAX2 : AX2Assumption) :
    ∃ C : ℝ, ∀ G : SplitGraph, ((G.Phi : ℤ) : ℝ) ≤ (G.n : ℝ) ^ 2 / 6 + C * (G.n : ℝ) := by
  exact Theorem_1_1_of_freedmanSplitProxyIneqNibble_linearRegularity_AX2 p c lam T
    (fun r hr β hβ => by
      obtain ⟨dB, hdB, hB⟩ := hBasic r hr β hβ
      obtain ⟨dP, hdP, hP⟩ := hProxy r hr β hβ
      obtain ⟨dR, hdR, hR⟩ := hBadRound r hr β hβ
      exact ⟨max dB (max dP dR), lt_of_lt_of_le hdB (le_max_left _ _), by
        refine Nibble.freedmanCardExplicitSplitProxyIneqCore_of_badRound ?_ ?_ ?_
        · intro N d hd hd0 hsize
          exact hB N d hd (le_trans (le_max_left dB (max dP dR)) hd0) hsize
        · intro N d hd hd0 hsize
          exact hP N d hd (le_trans (le_trans (le_max_left dP dR) (le_max_right dB (max dP dR))) hd0)
            hsize
        · refine ⟨?_, ?_⟩
          · intro N d hd hd0 hsize
            exact hR.1 N d hd
              (le_trans (le_trans (le_max_right dP dR) (le_max_right dB (max dP dR))) hd0)
              hsize
          · intro N d hd hd0 hsize
            exact hR.2 N d hd
              (le_trans (le_trans (le_max_right dP dR) (le_max_right dB (max dP dR))) hd0)
              hsize⟩)
    hReg hAX2

/-- Theorem 1.1 from the final concrete Freedman residual pair. The basic parameter facts and proxy
nonnegativity are supplied by the standalone nibble development. -/
theorem Theorem_1_1_of_freedmanConcreteBadRoundNibble_linearRegularity_AX2
    (hBadRound : ∀ r : ℕ, 2 ≤ r → ∀ β : ℝ, 0 < β →
      ∃ d₀ : ℝ, 0 < d₀ ∧
        Nibble.FreedmanCardExplicitBadRoundCore Nibble.freedmanExplicitP Nibble.freedmanExplicitC
          Nibble.freedmanExplicitLam Nibble.freedmanExplicitT r β ((1 : ℝ) / 100)
          (min (β / 4) ((1 : ℝ) / 100)) d₀ 1)
    (hReg : ∀ μ η d₀ L : ℝ, 0 < μ → 0 < η → 0 < d₀ → 0 < L →
      Nibble.AX1.NearRegObligationLinearSized μ η d₀ L)
    (hAX2 : AX2Assumption) :
    ∃ C : ℝ, ∀ G : SplitGraph, ((G.Phi : ℤ) : ℝ) ≤ (G.n : ℝ) ^ 2 / 6 + C * (G.n : ℝ) := by
  exact Theorem_1_1_of_AX1_AX2
    (AX1_from_freedmanConcreteBadRound_linearRegularity hBadRound hReg) hAX2

/-- Theorem 1.1 from the two final concrete Freedman residual halves. -/
theorem Theorem_1_1_of_freedmanConcreteBadEventRoundIneq_linearRegularity_AX2
    (hBadEvent : ∀ r : ℕ, 2 ≤ r → ∀ β : ℝ, 0 < β →
      ∃ d₀ : ℝ, 0 < d₀ ∧
        Nibble.FreedmanCardExplicitBadEventCore Nibble.freedmanExplicitP Nibble.freedmanExplicitC
          r β ((1 : ℝ) / 100) d₀ 1)
    (hRoundIneq : ∀ r : ℕ, 2 ≤ r → ∀ β : ℝ, 0 < β →
      ∃ d₀ : ℝ, 0 < d₀ ∧
        Nibble.FreedmanCardExplicitRoundIneqCore Nibble.freedmanExplicitP Nibble.freedmanExplicitC
          Nibble.freedmanExplicitLam Nibble.freedmanExplicitT r β ((1 : ℝ) / 100)
          (min (β / 4) ((1 : ℝ) / 100)) d₀ 1)
    (hReg : ∀ μ η d₀ L : ℝ, 0 < μ → 0 < η → 0 < d₀ → 0 < L →
      Nibble.AX1.NearRegObligationLinearSized μ η d₀ L)
    (hAX2 : AX2Assumption) :
    ∃ C : ℝ, ∀ G : SplitGraph, ((G.Phi : ℤ) : ℝ) ≤ (G.n : ℝ) ^ 2 / 6 + C * (G.n : ℝ) := by
  exact Theorem_1_1_of_AX1_AX2
    (AX1_from_freedmanConcreteBadEventRoundIneq_linearRegularity hBadEvent hRoundIneq hReg) hAX2

/-- Corollary 1.2 assembled from standalone nibble AX1 and an external AX2 input. -/
theorem Corollary_1_2_of_nibble_linearRegularity_AX2
    (hNib : Nibble.NibbleTheoremMostCeilSized)
    (hReg : ∀ μ η d₀ L : ℝ, 0 < μ → 0 < η → 0 < d₀ → 0 < L →
      Nibble.AX1.NearRegObligationLinearSized μ η d₀ L)
    (hAX2 : AX2Assumption) :
    ∃ C : ℝ, ∀ G : SplitGraph, (G.cp : ℝ) ≤ (G.n : ℝ) ^ 2 / 6 + C * (G.n : ℝ) :=
  Corollary_1_2_of_AX1_AX2
    (AX1_from_nibbleTheoremCeilSized_and_linearRegularity hNib hReg)
    hAX2

/-- Corollary 1.2 from the axiom-clean Freedman parameter-core interface. -/
theorem Corollary_1_2_of_freedmanCore_linearRegularity_AX2
    (hCore : ∀ r : ℕ, 2 ≤ r → ∀ β : ℝ, 0 < β →
      Nibble.FreedmanSizedParameterCore r β ((1 : ℝ) / 100)
        (min (β / 4) ((1 : ℝ) / 100)) 1)
    (hReg : ∀ μ η d₀ L : ℝ, 0 < μ → 0 < η → 0 < d₀ → 0 < L →
      Nibble.AX1.NearRegObligationLinearSized μ η d₀ L)
    (hAX2 : AX2Assumption) :
    ∃ C : ℝ, ∀ G : SplitGraph, (G.cp : ℝ) ≤ (G.n : ℝ) ^ 2 / 6 + C * (G.n : ℝ) :=
  Corollary_1_2_of_nibble_linearRegularity_AX2
    (Nibble.nibbleTheoremMostCeilSized_of_freedman_core hCore) hReg hAX2

/-- Corollary 1.2 from the axiom-clean thresholded Freedman parameter-core interface. -/
theorem Corollary_1_2_of_freedmanThresholdCore_linearRegularity_AX2
    (hCore : ∀ r : ℕ, 2 ≤ r → ∀ β : ℝ, 0 < β →
      ∃ d₀ : ℝ, 0 < d₀ ∧
        Nibble.FreedmanSizedThresholdParameterCore r β ((1 : ℝ) / 100)
          (min (β / 4) ((1 : ℝ) / 100)) d₀ 1)
    (hReg : ∀ μ η d₀ L : ℝ, 0 < μ → 0 < η → 0 < d₀ → 0 < L →
      Nibble.AX1.NearRegObligationLinearSized μ η d₀ L)
    (hAX2 : AX2Assumption) :
    ∃ C : ℝ, ∀ G : SplitGraph, (G.cp : ℝ) ≤ (G.n : ℝ) ^ 2 / 6 + C * (G.n : ℝ) :=
  Corollary_1_2_of_nibble_linearRegularity_AX2
    (Nibble.nibbleTheoremMostCeilSized_of_freedman_threshold_core hCore) hReg hAX2

/-- Corollary 1.2 from the ceiled Freedman parameter core. -/
theorem Corollary_1_2_of_freedmanCeilCore_linearRegularity_AX2
    (hCore : ∀ r : ℕ, 2 ≤ r → ∀ β : ℝ, 0 < β →
      ∃ d₀ : ℝ, 0 < d₀ ∧
        Nibble.FreedmanCeilThresholdParameterCore r β ((1 : ℝ) / 100)
          (min (β / 4) ((1 : ℝ) / 100)) d₀ 1)
    (hReg : ∀ μ η d₀ L : ℝ, 0 < μ → 0 < η → 0 < d₀ → 0 < L →
      Nibble.AX1.NearRegObligationLinearSized μ η d₀ L)
    (hAX2 : AX2Assumption) :
    ∃ C : ℝ, ∀ G : SplitGraph, (G.cp : ℝ) ≤ (G.n : ℝ) ^ 2 / 6 + C * (G.n : ℝ) := by
  exact Corollary_1_2_of_freedmanThresholdCore_linearRegularity_AX2
    (fun r hr β hβ =>
      let μ : ℝ := (1 : ℝ) / 100
      have hμ : 0 < μ := by norm_num [μ]
      let η : ℝ := min (β / 4) ((1 : ℝ) / 100)
      let hceil := hCore r hr β hβ
      hceil.imp fun d₀ hd =>
        ⟨hd.1, Nibble.freedmanSizedThresholdParameterCore_of_ceil (r := r) (β := β)
          (μ := μ) (η := η) (d₀ := d₀) (K := 1) hμ hd.2⟩)
    hReg hAX2

/-- Corollary 1.2 from the fully numeric ceiled Freedman parameter core. -/
theorem Corollary_1_2_of_freedmanNumericCore_linearRegularity_AX2
    (hCore : ∀ r : ℕ, 2 ≤ r → ∀ β : ℝ, 0 < β →
      ∃ d₀ : ℝ, 0 < d₀ ∧
        Nibble.FreedmanCeilNumericThresholdParameterCore r β ((1 : ℝ) / 100)
          (min (β / 4) ((1 : ℝ) / 100)) d₀ 1)
    (hReg : ∀ μ η d₀ L : ℝ, 0 < μ → 0 < η → 0 < d₀ → 0 < L →
      Nibble.AX1.NearRegObligationLinearSized μ η d₀ L)
    (hAX2 : AX2Assumption) :
    ∃ C : ℝ, ∀ G : SplitGraph, (G.cp : ℝ) ≤ (G.n : ℝ) ^ 2 / 6 + C * (G.n : ℝ) := by
  exact Corollary_1_2_of_freedmanCeilCore_linearRegularity_AX2
    (fun r hr β hβ =>
      (hCore r hr β hβ).imp fun d₀ hd =>
        ⟨hd.1, Nibble.freedmanCeilThresholdParameterCore_of_numeric hd.2⟩)
    hReg hAX2

/-- Corollary 1.2 from the type-free cardinal numeric Freedman parameter core. -/
theorem Corollary_1_2_of_freedmanCardCore_linearRegularity_AX2
    (hCore : ∀ r : ℕ, 2 ≤ r → ∀ β : ℝ, 0 < β →
      ∃ d₀ : ℝ, 0 < d₀ ∧
        Nibble.FreedmanCardNumericThresholdParameterCore r β ((1 : ℝ) / 100)
          (min (β / 4) ((1 : ℝ) / 100)) d₀ 1)
    (hReg : ∀ μ η d₀ L : ℝ, 0 < μ → 0 < η → 0 < d₀ → 0 < L →
      Nibble.AX1.NearRegObligationLinearSized μ η d₀ L)
    (hAX2 : AX2Assumption) :
    ∃ C : ℝ, ∀ G : SplitGraph, (G.cp : ℝ) ≤ (G.n : ℝ) ^ 2 / 6 + C * (G.n : ℝ) := by
  exact Corollary_1_2_of_freedmanNumericCore_linearRegularity_AX2
    (fun r hr β hβ =>
      (hCore r hr β hβ).imp fun d₀ hd =>
        ⟨hd.1, Nibble.freedmanCeilNumericThresholdParameterCore_of_card hd.2⟩)
    hReg hAX2

/-- Corollary 1.2 from an explicit type-free Freedman parameter choice. -/
theorem Corollary_1_2_of_freedmanExplicitCardCore_linearRegularity_AX2
    (p c lam : ℕ → ℝ → ℕ → ℝ → ℝ) (T : ℕ → ℝ → ℕ → ℝ → ℕ)
    (hCore : ∀ r : ℕ, 2 ≤ r → ∀ β : ℝ, 0 < β →
      ∃ d₀ : ℝ, 0 < d₀ ∧
        Nibble.FreedmanCardExplicitParameterCore p c lam T r β ((1 : ℝ) / 100)
          (min (β / 4) ((1 : ℝ) / 100)) d₀ 1)
    (hReg : ∀ μ η d₀ L : ℝ, 0 < μ → 0 < η → 0 < d₀ → 0 < L →
      Nibble.AX1.NearRegObligationLinearSized μ η d₀ L)
    (hAX2 : AX2Assumption) :
    ∃ C : ℝ, ∀ G : SplitGraph, (G.cp : ℝ) ≤ (G.n : ℝ) ^ 2 / 6 + C * (G.n : ℝ) := by
  exact Corollary_1_2_of_freedmanCardCore_linearRegularity_AX2
    (fun r hr β hβ =>
      (hCore r hr β hβ).imp fun d₀ hd =>
        ⟨hd.1, Nibble.freedmanCardNumericThresholdParameterCore_of_explicit hd.2⟩)
    hReg hAX2

/-- Corollary 1.2 from the split explicit type-free Freedman parameter core. -/
theorem Corollary_1_2_of_freedmanSplitExplicitCore_linearRegularity_AX2
    (p c lam : ℕ → ℝ → ℕ → ℝ → ℝ) (T : ℕ → ℝ → ℕ → ℝ → ℕ)
    (hCore : ∀ r : ℕ, 2 ≤ r → ∀ β : ℝ, 0 < β →
      ∃ d₀ : ℝ, 0 < d₀ ∧
        Nibble.FreedmanCardExplicitSplitCore p c lam T r β ((1 : ℝ) / 100)
          (min (β / 4) ((1 : ℝ) / 100)) d₀ 1)
    (hReg : ∀ μ η d₀ L : ℝ, 0 < μ → 0 < η → 0 < d₀ → 0 < L →
      Nibble.AX1.NearRegObligationLinearSized μ η d₀ L)
    (hAX2 : AX2Assumption) :
    ∃ C : ℝ, ∀ G : SplitGraph, (G.cp : ℝ) ≤ (G.n : ℝ) ^ 2 / 6 + C * (G.n : ℝ) := by
  exact Corollary_1_2_of_freedmanExplicitCardCore_linearRegularity_AX2 p c lam T
    (fun r hr β hβ =>
      (hCore r hr β hβ).imp fun d₀ hd =>
        ⟨hd.1, Nibble.freedmanCardExplicitParameterCore_of_split hd.2⟩)
    hReg hAX2

/-- Corollary 1.2 from the split explicit Freedman core through the direct nibble theorem wrapper. -/
theorem Corollary_1_2_of_freedmanSplitExplicitNibble_linearRegularity_AX2
    (p c lam : ℕ → ℝ → ℕ → ℝ → ℝ) (T : ℕ → ℝ → ℕ → ℝ → ℕ)
    (hCore : ∀ r : ℕ, 2 ≤ r → ∀ β : ℝ, 0 < β →
      ∃ d₀ : ℝ, 0 < d₀ ∧
        Nibble.FreedmanCardExplicitSplitCore p c lam T r β ((1 : ℝ) / 100)
          (min (β / 4) ((1 : ℝ) / 100)) d₀ 1)
    (hReg : ∀ μ η d₀ L : ℝ, 0 < μ → 0 < η → 0 < d₀ → 0 < L →
      Nibble.AX1.NearRegObligationLinearSized μ η d₀ L)
    (hAX2 : AX2Assumption) :
    ∃ C : ℝ, ∀ G : SplitGraph, (G.cp : ℝ) ≤ (G.n : ℝ) ^ 2 / 6 + C * (G.n : ℝ) :=
  Corollary_1_2_of_nibble_linearRegularity_AX2
    (Nibble.nibbleTheoremMostCeilSized_of_freedman_split_explicit_core p c lam T hCore)
    hReg hAX2

/-- Corollary 1.2 from the factored split explicit Freedman core. -/
theorem Corollary_1_2_of_freedmanSplitFactoredNibble_linearRegularity_AX2
    (p c lam : ℕ → ℝ → ℕ → ℝ → ℝ) (T : ℕ → ℝ → ℕ → ℝ → ℕ)
    (hCore : ∀ r : ℕ, 2 ≤ r → ∀ β : ℝ, 0 < β →
      ∃ d₀ : ℝ, 0 < d₀ ∧
        Nibble.FreedmanCardExplicitSplitFactoredCore p c lam T r β ((1 : ℝ) / 100)
          (min (β / 4) ((1 : ℝ) / 100)) d₀ 1)
    (hReg : ∀ μ η d₀ L : ℝ, 0 < μ → 0 < η → 0 < d₀ → 0 < L →
      Nibble.AX1.NearRegObligationLinearSized μ η d₀ L)
    (hAX2 : AX2Assumption) :
    ∃ C : ℝ, ∀ G : SplitGraph, (G.cp : ℝ) ≤ (G.n : ℝ) ^ 2 / 6 + C * (G.n : ℝ) :=
  Corollary_1_2_of_freedmanSplitExplicitNibble_linearRegularity_AX2 p c lam T
    (fun r hr β hβ =>
      (hCore r hr β hβ).imp fun d₀ hd =>
        ⟨hd.1, Nibble.freedmanCardExplicitSplitCore_of_factored hd.2⟩)
    hReg hAX2

/-- Corollary 1.2 from the card-penalty split explicit Freedman core. -/
theorem Corollary_1_2_of_freedmanSplitCardPenaltyNibble_linearRegularity_AX2
    (p c lam : ℕ → ℝ → ℕ → ℝ → ℝ) (T : ℕ → ℝ → ℕ → ℝ → ℕ)
    (hCore : ∀ r : ℕ, 2 ≤ r → ∀ β : ℝ, 0 < β →
      ∃ d₀ : ℝ, 0 < d₀ ∧
        Nibble.FreedmanCardExplicitSplitCardPenaltyCore p c lam T r β ((1 : ℝ) / 100)
          (min (β / 4) ((1 : ℝ) / 100)) d₀ 1)
    (hReg : ∀ μ η d₀ L : ℝ, 0 < μ → 0 < η → 0 < d₀ → 0 < L →
      Nibble.AX1.NearRegObligationLinearSized μ η d₀ L)
    (hAX2 : AX2Assumption) :
    ∃ C : ℝ, ∀ G : SplitGraph, (G.cp : ℝ) ≤ (G.n : ℝ) ^ 2 / 6 + C * (G.n : ℝ) :=
  Corollary_1_2_of_freedmanSplitFactoredNibble_linearRegularity_AX2 p c lam T
    (fun r hr β hβ =>
      (hCore r hr β hβ).imp fun d₀ hd =>
        ⟨hd.1, Nibble.freedmanCardExplicitSplitFactoredCore_of_cardPenalty hd.2⟩)
    hReg hAX2

/-- Corollary 1.2 from the scalar gain-lower explicit Freedman core. -/
theorem Corollary_1_2_of_freedmanSplitGainLowerNibble_linearRegularity_AX2
    (p c lam : ℕ → ℝ → ℕ → ℝ → ℝ) (T : ℕ → ℝ → ℕ → ℝ → ℕ)
    (hCore : ∀ r : ℕ, 2 ≤ r → ∀ β : ℝ, 0 < β →
      ∃ d₀ : ℝ, 0 < d₀ ∧
        Nibble.FreedmanCardExplicitSplitGainLowerCore p c lam T r β ((1 : ℝ) / 100)
          (min (β / 4) ((1 : ℝ) / 100)) d₀ 1)
    (hReg : ∀ μ η d₀ L : ℝ, 0 < μ → 0 < η → 0 < d₀ → 0 < L →
      Nibble.AX1.NearRegObligationLinearSized μ η d₀ L)
    (hAX2 : AX2Assumption) :
    ∃ C : ℝ, ∀ G : SplitGraph, (G.cp : ℝ) ≤ (G.n : ℝ) ^ 2 / 6 + C * (G.n : ℝ) :=
  Corollary_1_2_of_freedmanSplitCardPenaltyNibble_linearRegularity_AX2 p c lam T
    (fun r hr β hβ =>
      (hCore r hr β hβ).imp fun d₀ hd =>
        ⟨hd.1, Nibble.freedmanCardExplicitSplitCardPenaltyCore_of_gainLower hd.2⟩)
    hReg hAX2

/-- Corollary 1.2 from the proxy-nonnegative plus scalar-lower explicit Freedman core. -/
theorem Corollary_1_2_of_freedmanSplitProxyScalarNibble_linearRegularity_AX2
    (p c lam : ℕ → ℝ → ℕ → ℝ → ℝ) (T : ℕ → ℝ → ℕ → ℝ → ℕ)
    (hCore : ∀ r : ℕ, 2 ≤ r → ∀ β : ℝ, 0 < β →
      ∃ d₀ : ℝ, 0 < d₀ ∧
        Nibble.FreedmanCardExplicitSplitProxyScalarCore p c lam T r β ((1 : ℝ) / 100)
          (min (β / 4) ((1 : ℝ) / 100)) d₀ 1)
    (hReg : ∀ μ η d₀ L : ℝ, 0 < μ → 0 < η → 0 < d₀ → 0 < L →
      Nibble.AX1.NearRegObligationLinearSized μ η d₀ L)
    (hAX2 : AX2Assumption) :
    ∃ C : ℝ, ∀ G : SplitGraph, (G.cp : ℝ) ≤ (G.n : ℝ) ^ 2 / 6 + C * (G.n : ℝ) := by
  exact Corollary_1_2_of_freedmanSplitGainLowerNibble_linearRegularity_AX2 p c lam T
    (fun r hr β hβ =>
      (hCore r hr β hβ).imp fun d₀ hd =>
        ⟨hd.1, Nibble.freedmanCardExplicitSplitGainLowerCore_of_proxyScalar hd.2⟩)
    hReg hAX2

/-- Corollary 1.2 from the proxy-nonnegative plus factored-round-inequality Freedman core. -/
theorem Corollary_1_2_of_freedmanSplitProxyIneqNibble_linearRegularity_AX2
    (p c lam : ℕ → ℝ → ℕ → ℝ → ℝ) (T : ℕ → ℝ → ℕ → ℝ → ℕ)
    (hCore : ∀ r : ℕ, 2 ≤ r → ∀ β : ℝ, 0 < β →
      ∃ d₀ : ℝ, 0 < d₀ ∧
        Nibble.FreedmanCardExplicitSplitProxyIneqCore p c lam T r β ((1 : ℝ) / 100)
          (min (β / 4) ((1 : ℝ) / 100)) d₀ 1)
    (hReg : ∀ μ η d₀ L : ℝ, 0 < μ → 0 < η → 0 < d₀ → 0 < L →
      Nibble.AX1.NearRegObligationLinearSized μ η d₀ L)
    (hAX2 : AX2Assumption) :
    ∃ C : ℝ, ∀ G : SplitGraph, (G.cp : ℝ) ≤ (G.n : ℝ) ^ 2 / 6 + C * (G.n : ℝ) := by
  exact Corollary_1_2_of_freedmanSplitFactoredNibble_linearRegularity_AX2 p c lam T
    (fun r hr β hβ =>
      (hCore r hr β hβ).imp fun d₀ hd =>
        ⟨hd.1, Nibble.freedmanCardExplicitSplitFactoredCore_of_proxyIneq hd.2⟩)
    hReg hAX2

/-- Corollary 1.2 from the remaining bad-event plus factored-round-inequality Freedman core, after
basic parameter facts and proxy nonnegativity have been discharged separately. -/
theorem Corollary_1_2_of_freedmanBadRoundNibble_linearRegularity_AX2
    (p c lam : ℕ → ℝ → ℕ → ℝ → ℝ) (T : ℕ → ℝ → ℕ → ℝ → ℕ)
    (hBasic : ∀ r : ℕ, 2 ≤ r → ∀ β : ℝ, 0 < β →
      ∃ d₀ : ℝ, 0 < d₀ ∧
        Nibble.FreedmanCardExplicitBasicCore p c lam T r β ((1 : ℝ) / 100) d₀ 1)
    (hProxy : ∀ r : ℕ, 2 ≤ r → ∀ β : ℝ, 0 < β →
      ∃ d₀ : ℝ, 0 < d₀ ∧
        Nibble.FreedmanCardExplicitDegreeProxyNonnegCore p c T r β ((1 : ℝ) / 100) d₀ 1)
    (hBadRound : ∀ r : ℕ, 2 ≤ r → ∀ β : ℝ, 0 < β →
      ∃ d₀ : ℝ, 0 < d₀ ∧
        Nibble.FreedmanCardExplicitBadRoundCore p c lam T r β ((1 : ℝ) / 100)
          (min (β / 4) ((1 : ℝ) / 100)) d₀ 1)
    (hReg : ∀ μ η d₀ L : ℝ, 0 < μ → 0 < η → 0 < d₀ → 0 < L →
      Nibble.AX1.NearRegObligationLinearSized μ η d₀ L)
    (hAX2 : AX2Assumption) :
    ∃ C : ℝ, ∀ G : SplitGraph, (G.cp : ℝ) ≤ (G.n : ℝ) ^ 2 / 6 + C * (G.n : ℝ) := by
  exact Corollary_1_2_of_freedmanSplitProxyIneqNibble_linearRegularity_AX2 p c lam T
    (fun r hr β hβ => by
      obtain ⟨dB, hdB, hB⟩ := hBasic r hr β hβ
      obtain ⟨dP, hdP, hP⟩ := hProxy r hr β hβ
      obtain ⟨dR, hdR, hR⟩ := hBadRound r hr β hβ
      exact ⟨max dB (max dP dR), lt_of_lt_of_le hdB (le_max_left _ _), by
        refine Nibble.freedmanCardExplicitSplitProxyIneqCore_of_badRound ?_ ?_ ?_
        · intro N d hd hd0 hsize
          exact hB N d hd (le_trans (le_max_left dB (max dP dR)) hd0) hsize
        · intro N d hd hd0 hsize
          exact hP N d hd (le_trans (le_trans (le_max_left dP dR) (le_max_right dB (max dP dR))) hd0)
            hsize
        · refine ⟨?_, ?_⟩
          · intro N d hd hd0 hsize
            exact hR.1 N d hd
              (le_trans (le_trans (le_max_right dP dR) (le_max_right dB (max dP dR))) hd0)
              hsize
          · intro N d hd hd0 hsize
            exact hR.2 N d hd
              (le_trans (le_trans (le_max_right dP dR) (le_max_right dB (max dP dR))) hd0)
              hsize⟩)
    hReg hAX2

/-- Corollary 1.2 from the final concrete Freedman residual pair. -/
theorem Corollary_1_2_of_freedmanConcreteBadRoundNibble_linearRegularity_AX2
    (hBadRound : ∀ r : ℕ, 2 ≤ r → ∀ β : ℝ, 0 < β →
      ∃ d₀ : ℝ, 0 < d₀ ∧
        Nibble.FreedmanCardExplicitBadRoundCore Nibble.freedmanExplicitP Nibble.freedmanExplicitC
          Nibble.freedmanExplicitLam Nibble.freedmanExplicitT r β ((1 : ℝ) / 100)
          (min (β / 4) ((1 : ℝ) / 100)) d₀ 1)
    (hReg : ∀ μ η d₀ L : ℝ, 0 < μ → 0 < η → 0 < d₀ → 0 < L →
      Nibble.AX1.NearRegObligationLinearSized μ η d₀ L)
    (hAX2 : AX2Assumption) :
    ∃ C : ℝ, ∀ G : SplitGraph, (G.cp : ℝ) ≤ (G.n : ℝ) ^ 2 / 6 + C * (G.n : ℝ) := by
  exact Corollary_1_2_of_AX1_AX2
    (AX1_from_freedmanConcreteBadRound_linearRegularity hBadRound hReg) hAX2

/-- Corollary 1.2 from the two final concrete Freedman residual halves. -/
theorem Corollary_1_2_of_freedmanConcreteBadEventRoundIneq_linearRegularity_AX2
    (hBadEvent : ∀ r : ℕ, 2 ≤ r → ∀ β : ℝ, 0 < β →
      ∃ d₀ : ℝ, 0 < d₀ ∧
        Nibble.FreedmanCardExplicitBadEventCore Nibble.freedmanExplicitP Nibble.freedmanExplicitC
          r β ((1 : ℝ) / 100) d₀ 1)
    (hRoundIneq : ∀ r : ℕ, 2 ≤ r → ∀ β : ℝ, 0 < β →
      ∃ d₀ : ℝ, 0 < d₀ ∧
        Nibble.FreedmanCardExplicitRoundIneqCore Nibble.freedmanExplicitP Nibble.freedmanExplicitC
          Nibble.freedmanExplicitLam Nibble.freedmanExplicitT r β ((1 : ℝ) / 100)
          (min (β / 4) ((1 : ℝ) / 100)) d₀ 1)
    (hReg : ∀ μ η d₀ L : ℝ, 0 < μ → 0 < η → 0 < d₀ → 0 < L →
      Nibble.AX1.NearRegObligationLinearSized μ η d₀ L)
    (hAX2 : AX2Assumption) :
    ∃ C : ℝ, ∀ G : SplitGraph, (G.cp : ℝ) ≤ (G.n : ℝ) ^ 2 / 6 + C * (G.n : ℝ) := by
  exact Corollary_1_2_of_AX1_AX2
    (AX1_from_freedmanConcreteBadEventRoundIneq_linearRegularity hBadEvent hRoundIneq hReg) hAX2

end PaperIII
