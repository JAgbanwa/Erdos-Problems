/-
# The AX2 half of Erdős #81 — endgame, with the one proved input discharged

`BKLO.triangle_decomposition_of_inputs_and_cell_step_countWideForeignBalanced`
(`BKLO/AX2ForeignFibreBalance.lean`) derives the AX2 half of Erdős #81 — every large,
`K₃`-divisible `G` with `δ(G) ≥ (9/10 + ε)|V|` is triangle-decomposable — from **four** inputs:

1. `hDross : FracTriangleThreshold`  (Dross's fractional threshold; a *published* theorem),
2. `hNib   : FracToApproxMaxDeg`     (the nibble / Pippenger–Spencer max-degree form; *published*),
3. `hDirac : PerfectMatchingDirac`   (Dirac's matching; **proved in this library**),
4. `hstep  : RoutedSweepInvCellCountForeignBalancedWide6hStepScaledComplete`  (the one-link absorber
   step — the sole genuinely new combinatorial obligation).

This file discharges input 3 with the library's own `BKLO.perfectMatchingDirac_holds`
(`BKLO/DiracMatching.lean`, proved via Tutte), collapsing the endgame to the **three** remaining
obligations and stating them as a single theorem.  It records, precisely and machine-checked, what
still stands between the library and the unconditional AX2 half:

* `hDross` — to be imported from the `dross_fractional_flow_exact` bridge (a published theorem);
* `hNib`  — the nibble max-degree form in the dense regime (a published theorem);
* `hstep` — the perturbation-only close now under way, with the scaffolding of
  `BKLO/PerturbationOnlyPairing.lean` already in place.

Everything here is `sorry`-free.
-/
import BKLO.AX2ForeignFibreBalance
import BKLO.DiracMatching

namespace BKLO

/-- **AX2 half of Erdős #81, from the three remaining inputs.**  Dirac's matching input is
discharged internally by `BKLO.perfectMatchingDirac_holds`; only the two published inputs
(`hDross`, `hNib`) and the new one-link step (`hstep`) remain.  The density budget is unchanged:
`(9/10 + ε)|V| ≤ δ(G)`. -/
theorem erdos81_ax2half_of_dross_nib_step
    (hDross : FracTriangleThreshold) (hNib : FracToApproxMaxDeg)
    (hstep : RoutedSweepInvCellCountForeignBalancedWide6hStepScaledComplete) :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ,
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        n₀ ≤ Fintype.card V →
        (3 ∣ G.edgeFinset.card ∧ ∀ v, Even (G.degree v)) →
        (9 / 10 + ε) * (Fintype.card V : ℝ) ≤ (G.minDegree : ℝ) →
        TriangleDecomposable G :=
  triangle_decomposition_of_inputs_and_cell_step_countWideForeignBalanced
    hDross hNib perfectMatchingDirac_holds hstep

end BKLO
