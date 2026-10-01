import PaperIV.HybridDichotomy
import PaperIV.FarRounding

/-!
# Dual separation and absorbable critical structure

This module exposes the conceptual core of the final Paper IV proof without
changing its mathematics.  The far side is a quantitative dual separation
certificate.  The complementary side is not merely a graph close to a split
graph: it contains a literal mixed packing and the paid RD09 accounts that
complete it at the sharp target.

Thus the public route has the form

```
certified fractional optimum
  -> quadratic dual slack OR absorbable critical structure
  -> physical clique partition at `targetSize`
```

The construction is RootEngine-free through the already proved regularized
root bridge used by `NearStructureWitness`.  The present file is deliberately
small: it records the correct public interface and proves that the existing
near constructor supplies it.
-/

namespace PaperIV.SeparationAbsorptionRoute

open PaperIV.FarRounding
open PaperIV.RC01FarAssembly
open PaperIV.NearH1StructureWitness

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A literal critical structure that already carries its physical absorber.
The fields are deliberately restricted to the data consumed by the final
partition theorem.  Structural localization remains available from the
stronger `NearStructureWitness` that constructs this object. -/
structure AbsorbableCriticalStructure (G : SimpleGraph V) [DecidableRel G.Adj] where
  packing : Finset (Finset V)
  isPacking : PaperIV.PhysicalCompletion.IsK34Packing G packing
  accounts : PaperIV.RD09PhysicalLedger.PhysicalAccounts G packing
  accounts_order : accounts.order = (Fintype.card V : ℚ)

/-- Forget the localization witnesses and retain exactly the physical
absorption certificate. -/
def AbsorbableCriticalStructure.ofNearStructureWitness
    (W : NearStructureWitness G) : AbsorbableCriticalStructure G where
  packing := W.packing
  isPacking := W.isPacking
  accounts := W.accounts
  accounts_order := W.accounts_order

namespace AbsorbableCriticalStructure

/-- An absorbable critical structure closes at the sharp target. -/
theorem exists_target_partition (A : AbsorbableCriticalStructure G) :
    ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧
      Q.size ≤ targetSize (Fintype.card V) := by
  exact PaperIV.NearRegimePacking.exists_cliquePartition_target_of_physicalAccounts
    A.isPacking A.accounts A.accounts_order

end AbsorbableCriticalStructure

/-- **Dual separation or physical absorption.**  Every sufficiently large
chordal graph with a certified optimum either has the quadratic slack needed
by RC01 or carries a literal absorbable critical structure. -/
theorem chordal_dualSeparated_or_absorbable :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n ->
      ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      PaperIV.FarRounding.IsChordal G ->
      ∀ w : ℚ, CertifiedFractionalOptimum G w ->
        ((G.edgeFinset.card : ℚ) - w <
            (n : ℚ) ^ 2 / 6 -
              PaperIV.NearH1Calibration.eta * (n : ℚ) ^ 2) ∨
          Nonempty (AbsorbableCriticalStructure G) := by
  classical
  let N := Classical.choose PaperIV.HybridDichotomy.chordal_far_or_nearStructure
  have hN := Classical.choose_spec PaperIV.HybridDichotomy.chordal_far_or_nearStructure
  refine ⟨N, ?_⟩
  intro n hn G _ hG w hw
  rcases hN n hn G hG w hw with hfar | hnear
  · exact Or.inl hfar
  · exact Or.inr ⟨AbsorbableCriticalStructure.ofNearStructureWitness hnear.some⟩

/-- **Erdős #81 by separation--absorption.**  This is the final theorem with
the proof architecture exposed: RC01 consumes dual slack, while the critical
side is closed by the physical absorber carried by the structural witness. -/
theorem erdos81_of_dualSeparation_absorption :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n ->
      ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      PaperIV.FarRounding.IsChordal G ->
        ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size ≤ targetSize n := by
  classical
  have hfarExists :=
    farRegime_cliquePartition PaperIV.NearH1Calibration.eta
      (by dsimp [PaperIV.NearH1Calibration.eta]; positivity)
  let Nfar := Classical.choose hfarExists
  have hfar := Classical.choose_spec hfarExists
  let Nsep := Classical.choose chordal_dualSeparated_or_absorbable
  have hsep := Classical.choose_spec chordal_dualSeparated_or_absorbable
  refine ⟨max Nfar Nsep, ?_⟩
  intro n hn G _ hG
  obtain ⟨w, hw⟩ :=
    PaperIV.CertifiedOptimumExistence.exists_certifiedFractionalOptimum G
  rcases hsep n (le_trans (Nat.le_max_right _ _) hn) G hG w hw with
    hslack | habs
  · exact hfar n (le_trans (Nat.le_max_left _ _) hn) G hG w hw hslack
  · -- `Fintype.card (Fin n)` es `n`, pero no por reduccion definicional.
    have h := habs.some.exists_target_partition
    rwa [Fintype.card_fin] at h

end PaperIV.SeparationAbsorptionRoute
