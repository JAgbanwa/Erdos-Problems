/-
# The AX2 half of Erdős #81, from the faithful §10/§11 near-optimal decomposition

This is the penultimate assembly of the faithful route: once the faithful §11 vortex assembly supplies
`BKLO.NearOptimalConclusion` (built from `BKLO.section10_K3_dense_final`, i.e. from the repaired
`Lemma1012K3'` alone — Lemma 10.3 and `δ_F^η` are already discharged), the AX2 half of Erdős #81
follows from the three classical inputs via `BKLO.triangle_decomposition_of_inputs`.

`NearOptimalConclusion` trivially packages as `NearOptimalDecomp` (the three inputs are not needed
beyond producing the conclusion).  Everything here is `sorry`-free.
-/
import BKLO.Main

open Finset

namespace BKLO

/-- **AX2 half of Erdős #81, faithful route.**  From the three classical inputs (Dross's fractional
triangle-decomposition threshold, the Haxell–Rödl / nibble approximate decomposition, and Dirac's
theorem) together with the faithful near-optimal decomposition `NearOptimalConclusion`, every large
`K₃`-divisible graph with `δ(G) ≥ (9/10 + ε)n` is triangle-decomposable. -/
theorem erdos81_ax2half_faithful
    (hDross : FracTriangleThreshold) (hHR : FracToApprox) (hDirac : PerfectMatchingDirac)
    (hNOC : NearOptimalConclusion) :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ,
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        n₀ ≤ Fintype.card V →
        (3 ∣ G.edgeFinset.card ∧ ∀ v, Even (G.degree v)) →
        (9 / 10 + ε) * (Fintype.card V : ℝ) ≤ (G.minDegree : ℝ) →
        TriangleDecomposable G :=
  triangle_decomposition_of_inputs hDross hHR hDirac (fun _ _ _ => hNOC)

end BKLO
