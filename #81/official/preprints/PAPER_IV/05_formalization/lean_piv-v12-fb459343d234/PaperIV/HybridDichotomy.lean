import PaperIV.NearH1Localization
import PaperIV.NearH1StructureWitness
import PaperIV.NearRegimePackingInterface
import PaperIV.RC01FarAssembly
import PaperIV.CertifiedOptimumExistence

/-!
# The hybrid route: a structural far/near dichotomy for chordal graphs

This module builds the third Paper IV route to Erdős #81.  Its shape is

```
certified rational optimum
  → proved far-or-near split
  → { RC01 only in FAR ; H1/RD09 only in NEAR }
  → common physical clique-partition budget
  → final theorem
```

The two sides of the split are the two sides of one scalar inequality in the
certified mixed defect `e(G) - w`:

* **far**: the quantitative quadratic slack certificate
  `e(G) - w < n²/6 - η n²` — exactly the hypothesis of the internally proved
  RC01 far rounding theorem `PaperIV.RC01FarAssembly.farRegime_cliquePartition`;
* **near**: its negation, from which `chordal_near_extremal_stability` returns
  *literal structural witnesses* (`NearStructureWitness`): the descent
  localization of `PaperIV.NearH1Localization`, a split core with its edit
  budget and calibrated residual square, a `RegularizedRoot` with its
  calibrated reference clique, and the physical H1/RD09 terminal accounts of
  the original graph.

The near branch never uses a universal rounding shortcut, and the far branch
never uses the H1/RD09 accounts.  The two branches meet only at the common
physical budget `exists_cliquePartition_target_of_physicalAccounts` /
`farRegime_cliquePartition`, both of which produce a clique partition of order
at most four and size at most `targetSize n`.
-/

namespace PaperIV.HybridDichotomy

open PaperIV.FarRounding PaperIV.RC01FarAssembly
open PaperIV.NearH1StructureWitness

/-- **Structural extremal stability of the near regime.**  A large chordal
graph with a certified rational optimum and *no* quadratic far slack carries
the full near structural package: a literal split core with a quadratic edit
budget and a calibrated residual square, a regularized root, and the physical
H1/RD09 accounts of the original graph.  Nothing here is a restatement of the
target conclusion: the output is concrete graph data. -/
theorem chordal_near_extremal_stability :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      PaperIV.FarRounding.IsChordal G → ∀ w : ℚ, CertifiedFractionalOptimum G w →
        ¬ ((G.edgeFinset.card : ℚ) - w <
          (n : ℚ) ^ 2 / 6 - PaperIV.NearH1Calibration.eta * (n : ℚ) ^ 2) →
          Nonempty (NearStructureWitness G) := by
  refine ⟨4 * 10 ^ 12, ?_⟩
  intro n hn G _ hG w hw hnear
  -- Las dos cordalidades son ahora el mismo enunciado: `PaperIV.IsChordal` y
  -- `PaperIV.FarRounding.IsChordal` son alias (`export`) de `SimpleGraph.IsChordal`.
  -- El paquete estructural se construye una sola vez, en `NearH1Localization`.
  exact PaperIV.NearH1Localization.exists_nearStructureWitness_of_nearRegime
    hn G hG hw hnear

/-- **The exhaustive far/near dichotomy.**  For every sufficiently large
chordal graph with a certified rational optimum, either the quadratic slack
certificate consumed by the RC01 rounding branch holds, or the near structural
package exists. -/
theorem chordal_far_or_nearStructure :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      PaperIV.FarRounding.IsChordal G → ∀ w : ℚ, CertifiedFractionalOptimum G w →
        ((G.edgeFinset.card : ℚ) - w <
            (n : ℚ) ^ 2 / 6 - PaperIV.NearH1Calibration.eta * (n : ℚ) ^ 2) ∨
          Nonempty (NearStructureWitness G) := by
  obtain ⟨N, hN⟩ := chordal_near_extremal_stability
  refine ⟨N, ?_⟩
  intro n hn G _ hG w hw
  by_cases hslack : (G.edgeFinset.card : ℚ) - w <
      (n : ℚ) ^ 2 / 6 - PaperIV.NearH1Calibration.eta * (n : ℚ) ^ 2
  · exact Or.inl hslack
  · exact Or.inr (hN n hn G hG w hw hslack)

/-- **Erdős #81 from the structural dichotomy.**  RC01 is used *only* on the
far side; the H1/RD09 physical accounts are used *only* on the near side; both
sides are converted to a clique partition by the same physical budget.  The
certified rational optimum is constructed internally, so the statement has no
LP or analytic input. -/
theorem erdos81_of_structuralDichotomy :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      PaperIV.FarRounding.IsChordal G →
        ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size ≤ targetSize n := by
  classical
  obtain ⟨Nfar, hfar⟩ :=
    farRegime_cliquePartition PaperIV.NearH1Calibration.eta
      (by dsimp [PaperIV.NearH1Calibration.eta]; positivity)
  obtain ⟨Nsplit, hsplit⟩ := chordal_far_or_nearStructure
  refine ⟨max Nfar Nsplit, ?_⟩
  intro n hn G _ hG
  obtain ⟨w, hw⟩ :=
    PaperIV.CertifiedOptimumExistence.exists_certifiedFractionalOptimum G
  rcases hsplit n (le_trans (Nat.le_max_right _ _) hn) G hG w hw with
    hslack | hnearW
  · exact hfar n (le_trans (Nat.le_max_left _ _) hn) G hG w hw hslack
  · obtain ⟨W⟩ := hnearW
    simpa using
      PaperIV.NearRegimePacking.exists_cliquePartition_target_of_physicalAccounts
        W.isPacking W.accounts W.accounts_order

end PaperIV.HybridDichotomy
