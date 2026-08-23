/-
# Paper III — Theorem 1.1 assembled on the CURRENT atoms (sharp round + honest AX2)

`MainNibble.lean`'s concrete top theorems are stated on the OLD Freedman parameter cores
(`FreedmanCardExplicitBadRoundCore`), which the nibble reformulation refuted
(`Nibble.not_freedmanCardExplicitBadEventCore`).  This file re-states Theorem 1.1 on the CURRENT
open atoms:

* the nibble is fed through `Nibble.SharpRoundHyp` (the tight-band single round), via
  `nibbleTheoremMostCeilSized_of_sharpRound` and `AX1.nibbleGap_of_sharpRound`;
* AX2 is derived from the standalone `ax2` project through the HONEST local-budget absorber route
  (`AX2Bridge.AX2_from_Ax2_of_nibbleGap`, whose `ax2_of_nibbleGap` now routes through
  `reserve_absorber_local`, not the refuted transformer);
* strong duality is discharged (`Nibble.AX1.strongDualityHyp_holds`).

Hence the theorem is conditional on exactly the remaining research obligations:
`SharpRoundHyp` (nibble), the near-regularity obligation `hReg`, and — inside AX2 — the absorber
kernel and the degree-bounded approximation (both carried as internal `sorryAx` of `ax2_of_nibbleGap`
until closed).  When those close, `#print axioms` on this theorem is
`[propext, Classical.choice, Quot.sound]`.
-/
import PaperIII.Main
import PaperIII.AX1NibbleBridge
import PaperIII.AX2Bridge
import Nibble.TightNibble

namespace PaperIII

open Nibble

/-- **Theorem 1.1 on the current atoms.**  `Phi(G) ≤ n²/6 + C·n`, assembled from the sharp-round
nibble hypothesis and the near-regularity obligation, with AX2 through the honest absorber. -/
theorem Theorem_1_1_of_sharpRound_linearRegularity
    (hSharp : Nibble.SharpRoundHyp)
    (hReg : ∀ μ η d₀ L : ℝ, 0 < μ → 0 < η → 0 < d₀ → 0 < L →
      Nibble.AX1.NearRegObligationLinearSized μ η d₀ L) :
    ∃ C : ℝ, ∀ G : SplitGraph, ((G.Phi : ℤ) : ℝ) ≤ (G.n : ℝ) ^ 2 / 6 + C * (G.n : ℝ) := by
  -- AX1 from the sharp-round nibble theorem + regularity (strong duality is internal)
  have hAX1 : AX1Assumption :=
    AX1_from_nibbleTheoremCeilSized_and_linearRegularity
      (Nibble.nibbleTheoremMostCeilSized_of_sharpRound hSharp) hReg
  -- the sized near-regularity obligation for the nibble-gap (from the linear form)
  have hRegSized : ∀ μ η d₀ K : ℝ, 0 < μ → 0 < η → 0 < d₀ → 0 < K →
      Nibble.AX1.NearRegObligationSized μ η d₀ K :=
    fun μ η d₀ K hμ hη hd₀ hK =>
      Nibble.AX1.nearRegSized_of_forall_linearSized hK
        (fun L hL => hReg μ η d₀ L hμ hη hd₀ hL)
  -- AX2 from the honest absorber route, via the sharp-round nibble gap
  have hgap : Nibble.AX1.NibbleGapHyp :=
    Nibble.AX1.nibbleGap_of_sharpRound hSharp hRegSized
  have hAX2 : AX2Assumption := AX2_from_Ax2_of_nibbleGap hgap
  exact Theorem_1_1_of_AX1_AX2 hAX1 hAX2

/-- **Theorem 1.1, with the nibble UNCONDITIONAL** (post-`feca8761`: `SharpRoundHyp` is proved by
the tight schedule, so it is no longer a hypothesis).  `Phi(G) ≤ n²/6 + C·n`, conditional only on
the near-regularity obligation `hReg` (and, internally to AX2, the absorber atoms). -/
theorem Theorem_1_1_of_linearRegularity
    (hReg : ∀ μ η d₀ L : ℝ, 0 < μ → 0 < η → 0 < d₀ → 0 < L →
      Nibble.AX1.NearRegObligationLinearSized μ η d₀ L) :
    ∃ C : ℝ, ∀ G : SplitGraph, ((G.Phi : ℤ) : ℝ) ≤ (G.n : ℝ) ^ 2 / 6 + C * (G.n : ℝ) := by
  have hAX1 : AX1Assumption :=
    AX1_from_nibbleTheoremCeilSized_and_linearRegularity
      Nibble.nibbleTheoremMostCeilSized_holds hReg
  have hRegSized : ∀ μ η d₀ K : ℝ, 0 < μ → 0 < η → 0 < d₀ → 0 < K →
      Nibble.AX1.NearRegObligationSized μ η d₀ K :=
    fun μ η d₀ K hμ hη hd₀ hK =>
      Nibble.AX1.nearRegSized_of_forall_linearSized hK
        (fun L hL => hReg μ η d₀ L hμ hη hd₀ hL)
  have hgap : Nibble.AX1.NibbleGapHyp := Nibble.AX1.nibbleGap_holds hRegSized
  have hAX2 : AX2Assumption := AX2_from_Ax2_of_nibbleGap hgap
  exact Theorem_1_1_of_AX1_AX2 hAX1 hAX2

/-- **Theorem 1.1 on the single honest AX1 residual** (post-`d13ae96a`: the false near-regularity
obligation `hReg` is refuted and replaced by the TRUE residual `NibbleGapResidual`, the non-dense
triangle-rich case of Haxell–Rödl; the dense and triangle-poor branches are proved unconditionally).
Conditional only on `NibbleGapResidual` (and, internally to AX2, the absorber atoms). -/
theorem Theorem_1_1_of_residual (hres : Nibble.AX1.NibbleGapResidual) :
    ∃ C : ℝ, ∀ G : SplitGraph, ((G.Phi : ℤ) : ℝ) ≤ (G.n : ℝ) ^ 2 / 6 + C * (G.n : ℝ) := by
  have hAX1 : AX1Assumption := AX1_from_residual hres
  have hgap : Nibble.AX1.NibbleGapHyp := Nibble.AX1.nibbleGapHyp_of_residual hres
  have hAX2 : AX2Assumption := AX2_from_Ax2_of_nibbleGap hgap
  exact Theorem_1_1_of_AX1_AX2 hAX1 hAX2

/-- **Corollary 1.2 on the single honest AX1 residual.** -/
theorem Corollary_1_2_of_residual (hres : Nibble.AX1.NibbleGapResidual) :
    ∃ C : ℝ, ∀ G : SplitGraph, (G.cp : ℝ) ≤ (G.n : ℝ) ^ 2 / 6 + C * (G.n : ℝ) := by
  obtain ⟨C, hC⟩ := Theorem_1_1_of_residual hres
  refine ⟨C, fun G => ?_⟩
  have h1 : (G.cp : ℝ) ≤ ((G.Phi : ℤ) : ℝ) := by exact_mod_cast cp_le_Phi G
  exact le_trans h1 (hC G)

/-- **Corollary 1.2 on the current atoms.** `cp(G) ≤ n²/6 + C·n`. -/
theorem Corollary_1_2_of_sharpRound_linearRegularity
    (hSharp : Nibble.SharpRoundHyp)
    (hReg : ∀ μ η d₀ L : ℝ, 0 < μ → 0 < η → 0 < d₀ → 0 < L →
      Nibble.AX1.NearRegObligationLinearSized μ η d₀ L) :
    ∃ C : ℝ, ∀ G : SplitGraph, (G.cp : ℝ) ≤ (G.n : ℝ) ^ 2 / 6 + C * (G.n : ℝ) := by
  obtain ⟨C, hC⟩ := Theorem_1_1_of_sharpRound_linearRegularity hSharp hReg
  refine ⟨C, fun G => ?_⟩
  have h1 : (G.cp : ℝ) ≤ ((G.Phi : ℤ) : ℝ) := by exact_mod_cast cp_le_Phi G
  exact le_trans h1 (hC G)

end PaperIII
