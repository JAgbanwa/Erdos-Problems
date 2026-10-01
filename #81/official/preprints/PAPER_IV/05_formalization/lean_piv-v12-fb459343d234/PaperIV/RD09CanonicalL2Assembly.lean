import PaperIV.RD09CanonicalBadAccounts

/-!
# Canonical physical input for RD09-L2

This module removes the abstract vertex loads `a` and `u` from the phase-II
interface.  They are instantiated by the literal missing-spoke and used-spoke
accounts extracted from the graph and the phase-I packing.
-/

namespace PaperIV.RD09CanonicalL2Assembly

open Finset PaperIV.Model PaperIV.MultiHostTriangleLift
open PaperIV.RD09PhaseII PaperIV.RD09FactorCandidateMoments
open PaperIV.RD09FactorCandidateAverage PaperIV.RD09H1SpokeRealization
open PaperIV.RD09CanonicalBadAccounts

variable {V I Z Cand : Type*}
variable [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
variable [Fintype Z] [DecidableEq Z] [LinearOrder Z]
variable [Fintype Cand] [DecidableEq Cand]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable {k s p D t A : ℕ}
variable {core : Z ↪ V} {cand : Cand ↪ V}
variable {z : I → V} {E : I → Finset (Sym2 V)}
variable {fac : Z × Z → Fin k} {used : Finset (Z × Z)}

/-- The canonical RD09 assignment without the obsolete cross-phase
`IsPhaseISeparated` premise.  The assignment and its moment bound only use
the literal missing/used accounts.  Physical compatibility is discharged
later by `isSpokeCompatible_surviving_canonicalBad`, whose orientation is the
one appropriate when the phase-I hosts are the root vertices themselves. -/
theorem exists_canonical_assignment
    (roots : I ≃ Z) (hroot : ∀ i, z i = core (roots i))
    (hp : Fintype.card Z = p) (hp2 : 2 ≤ p)
    (hsk : s ≤ k) (hkp : p - 1 ≤ k) (hk : 0 < k)
    (hq2 : 2 ≤ Fintype.card Cand)
    (hslots : k + (k - s) ≤ Fintype.card Cand)
    (hD : ∀ x, missingLoad (G := G) core cand x ≤ D)
    (ht : ∀ i, (E i).card ≤ t)
    (hA : (∑ x, missingLoad (G := G) core cand x) = A)
    (h1 : IsMultiExteriorHub G z E) :
    ∃ α : Assign k s Cand,
      ((failedBases s α fac (canonicalBad G core cand z E)).card : ℚ) ≤
        rd09L2Bound (Fintype.card Cand) p D t A
          (multiLiftedPacking z E).card s := by
  obtain ⟨hbad, hu, hsum⟩ := canonicalBad_account_package
    (G := G) core cand z E roots hroot h1 ht
  exact exists_assign_rd09L2
    (Cand := Cand) (k := k) (s := s) (Z := Z)
    hp hp2 hsk hkp hk hq2 hslots fac
    (canonicalBad G core cand z E)
    (missingLoad (G := G) core cand) (usedLoad roots E)
    hbad hD hu hA hsum

/-- RD09-L2 and its physical phase-II packing, with both vertex accounts
canonically extracted from the supplied graph and phase-I family. -/
theorem exists_canonical_phaseTwo_packing
    (roots : I ≃ Z) (hroot : ∀ i, z i = core (roots i))
    (hp : Fintype.card Z = p) (hp2 : 2 ≤ p)
    (hsk : s ≤ k) (hkp : p - 1 ≤ k) (hk : 0 < k)
    (hq2 : 2 ≤ Fintype.card Cand)
    (hslots : k + (k - s) ≤ Fintype.card Cand)
    (hD : ∀ x, missingLoad (G := G) core cand x ≤ D)
    (ht : ∀ i, (E i).card ≤ t)
    (hA : (∑ x, missingLoad (G := G) core cand x) = A)
    (h1 : IsMultiExteriorHub G z E)
    (hdata : IsFactorCandidateData G core cand fac
      (canonicalBad G core cand z E))
    (hsep : IsPhaseISeparated z E core cand used) :
    ∃ α : Assign k s Cand,
      ((failedBases s α fac (canonicalBad G core cand z E)).card : ℚ) ≤
          rd09L2Bound (Fintype.card Cand) p D t A
            (multiLiftedPacking z E).card s
        ∧ IsPhaseTwoFamily G
            (survivingHub s α fac (canonicalBad G core cand z E) used cand)
            (survivingBaseEdge s α fac (canonicalBad G core cand z E) used core)
        ∧ IsPhaseCompatible z E
            (survivingHub s α fac (canonicalBad G core cand z E) used cand)
            (survivingBaseEdge s α fac (canonicalBad G core cand z E) used core)
        ∧ IsPacking G (multiLiftedPacking z E ∪
            phaseTwoPacking
              (survivingHub s α fac (canonicalBad G core cand z E) used cand)
              (survivingBaseEdge s α fac (canonicalBad G core cand z E) used core))
        ∧ PaperIV.PhysicalCompletion.IsK34Packing G
            (multiLiftedPacking z E ∪
              phaseTwoPacking
                (survivingHub s α fac (canonicalBad G core cand z E) used cand)
                (survivingBaseEdge s α fac (canonicalBad G core cand z E) used core))
        ∧ (multiLiftedPacking z E ∪
              phaseTwoPacking
                (survivingHub s α fac (canonicalBad G core cand z E) used cand)
                (survivingBaseEdge s α fac (canonicalBad G core cand z E) used core)).card
            = (∑ i, (E i).card) +
              (survivingBases s α fac (canonicalBad G core cand z E) used).card := by
  obtain ⟨hbad, hu, hsum⟩ := canonicalBad_account_package
    (G := G) core cand z E roots hroot h1 ht
  exact exists_rd09L2_phaseTwo_packing
    (Cand := Cand) (k := k) (s := s) (Z := Z)
    hp hp2 hsk hkp hk hq2 hslots
    (missingLoad (G := G) core cand) (usedLoad roots E)
    hbad hD hu hA hsum h1 hdata hsep

end PaperIV.RD09CanonicalL2Assembly
