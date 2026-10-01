import PaperIV.RC01Final
import PaperIV.MixedRoundingAdapter
import PaperIV.NB08Interface

/-!
# Unconditional far-regime assembly from RC01

This module connects the unconditional mixed rounding theorem proved by RC01
to the canonical `PaperIV.FarRounding` model.  It discharges the old external
rounding boundary in the far branch; it does not assume RUW, NB08, or a chordal
integrality-gap theorem.

The near/critical branch is deliberately absent from the conclusions below.
Thus this file must not be read as a proof of the final all-chordal linear
theorem by itself.
-/

namespace PaperIV.RC01FarAssembly

open PaperIV.FarRounding
open PaperIV.NB08Interface
open PaperIV.MixedRoundingAdapter

/-- RC01, transported to the `FarRounding` fractional-packing model. -/
theorem uniformRoundingAt (ζ : ℚ) (hζ : 0 < ζ) :
    UniformRoundingAt ζ := by
  obtain ⟨N, hN⟩ := PaperIV.RC01Final.rc01_uniformRoundingTarget ζ hζ
  refine ⟨N, ?_⟩
  intro n hn G _ x
  obtain ⟨P, hP⟩ := hN n hn G (ofFarFrac x)
  refine ⟨toFarPacking P, ?_⟩
  rw [gain_toFarPacking, ← value_ofFarFrac x]
  exact hP

/-- RC01 supplies the uniform transfer formerly carried as an external input. -/
theorem uniformTransferAt (ζ : ℚ) (hζ : 0 < ζ) :
    UniformTransferAt ζ :=
  uniformTransferAt_of_uniformRoundingAt (uniformRoundingAt ζ hζ)

/-- The chordal far-rounding predicate is unconditional for every positive
quadratic separation parameter. -/
theorem farRoundingAt (η : ℚ) (hη : 0 < η) :
    FarRoundingAt η := by
  apply farRoundingAt_of_uniformTransferAt
  exact uniformTransferAt (η / 2) (by positivity)

/-- **Unconditional RC01 far branch.**  Every sufficiently large chordal graph
whose certified mixed fractional defect has quadratic slack `η n²` has an
exact clique partition of the target size. -/
theorem farRegime_cliquePartition (η : ℚ) (hη : 0 < η) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      IsChordal G → ∀ w : ℚ, CertifiedFractionalOptimum G w →
        (G.edgeFinset.card : ℚ) - w < (n : ℚ) ^ 2 / 6 - η * (n : ℚ) ^ 2 →
          ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size ≤ targetSize n :=
  PaperIV.FarRounding.farRegime_cliquePartition hη.le (farRoundingAt η hη)

/-! ## Exact interface to the still separate critical branch -/

/-- The critical/near obligation complementary to RC01's far theorem.  This is
kept as a named proposition so the final assembly cannot hide it inside an
unnamed implication. -/
def NearRegimeAt (η : ℚ) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    IsChordal G → ∀ w : ℚ, CertifiedFractionalOptimum G w →
      ¬ ((G.edgeFinset.card : ℚ) - w <
        (n : ℚ) ^ 2 / 6 - η * (n : ℚ) ^ 2) →
        ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size ≤ targetSize n

/-- The target conclusion, phrased for every certified rational optimum. -/
def ChordalTargetAt : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    IsChordal G → ∀ w : ℚ, CertifiedFractionalOptimum G w →
      ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size ≤ targetSize n

/-- **Complete far/near case assembly.**  RC01 discharges the far side, so a
proof of the explicitly named `NearRegimeAt η` is sufficient for the full
target conclusion. -/
theorem chordalTargetAt_of_nearRegimeAt (η : ℚ) (hη : 0 < η)
    (hnear : NearRegimeAt η) : ChordalTargetAt := by
  obtain ⟨Nfar, hfar⟩ := farRegime_cliquePartition η hη
  obtain ⟨Nnear, hnear⟩ := hnear
  refine ⟨max Nfar Nnear, ?_⟩
  intro n hn G _ hG w hw
  by_cases hslack :
      (G.edgeFinset.card : ℚ) - w <
        (n : ℚ) ^ 2 / 6 - η * (n : ℚ) ^ 2
  · exact hfar n (le_trans (Nat.le_max_left _ _) hn) G hG w hw hslack
  · exact hnear n (le_trans (Nat.le_max_right _ _) hn) G hG w hw hslack

end PaperIV.RC01FarAssembly
