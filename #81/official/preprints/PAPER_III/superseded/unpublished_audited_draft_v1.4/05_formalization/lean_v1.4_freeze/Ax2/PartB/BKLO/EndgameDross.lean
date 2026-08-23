/-
# hDross discharged into the repaired AX2 endgame

`BKLO.erdos81_ax2half_of_dross_nib_step` (nibble, `BKLO/Erdos81AX2Endgame.lean`) derives the AX2 half
of Erdős #81 from three inputs — `hDross : FracTriangleThreshold`, `hNib : FracToApproxMaxDeg`, and
`hstep : RoutedSweepInvCellCountForeignBalancedWide6hStepScaledComplete` (Dirac's matching is already
discharged inside it).

Here the first input is discharged with `Ax2.BKLOBridge.fracTriangleThreshold_holds`
(`Ax2/PartB/BKLO/Bridge.lean`), which reduces it to the proved `Ax2.DrossNet.dross_fractional_flow_exact`.
What remains is the AX2 half from **two** inputs only — the published nibble max-degree form `hNib`
and the one-link absorber step `hstep` (itself reduced, in
`BKLO/PerturbedLinkEngine.lean`, to `BKLO.PerturbedLinkCycleOnlyPairing`).

Stated over `Ax2.TriangleDecomposable`, which coincides with `BKLO.TriangleDecomposable`
definitionally (`Ax2.BKLOBridge.triDecomp_iff`).

No `sorry`; the only remaining obligations are the two carried hypotheses.
-/
import Ax2.PartB.BKLO.Bridge
import BKLO.Erdos81AX2Endgame

namespace Ax2.BKLOBridge

/-- **AX2 half of Erdős #81 with Dross discharged.**  From the published nibble input `hNib` and the
one-link step `hstep`, via the repaired endgame `BKLO.erdos81_ax2half_of_dross_nib_step` with the
Dross input supplied by `fracTriangleThreshold_holds`.  The density budget is `(9/10 + ε)|V|`. -/
theorem erdos81_ax2half_dross_discharged
    (hNib : BKLO.FracToApproxMaxDeg)
    (hstep : BKLO.RoutedSweepInvCellCountForeignBalancedWide6hStepScaledComplete) :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ,
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        n₀ ≤ Fintype.card V →
        (3 ∣ G.edgeFinset.card ∧ ∀ v, Even (G.degree v)) →
        (9 / 10 + ε) * (Fintype.card V : ℝ) ≤ (G.minDegree : ℝ) →
        Ax2.TriangleDecomposable G := by
  intro ε hε
  obtain ⟨n₀, H⟩ :=
    BKLO.erdos81_ax2half_of_dross_nib_step fracTriangleThreshold_holds hNib hstep ε hε
  refine ⟨n₀, ?_⟩
  intro V _ _ G _ hn hdiv hδ
  exact (triDecomp_iff G).2 (H G hn hdiv hδ)

end Ax2.BKLOBridge
