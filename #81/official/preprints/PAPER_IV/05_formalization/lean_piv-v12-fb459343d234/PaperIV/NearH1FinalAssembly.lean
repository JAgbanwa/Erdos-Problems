import PaperIV.NearH1PhaseI
import PaperIV.RD09CanonicalL2Assembly
import PaperIV.RD09CompleteFactorAdapter
import PaperIV.RD09SplitEditAccount
import PaperIV.H1ImprovedConstants
import PaperIV.PhysicalCompletion

/-! # Final literal H1 assembly

This module joins the physical phase-I witness to the canonical RD09 phase-II
assignment.  All graph-theoretic data are instantiated literally.  The only
remaining inputs are the denominator-cleared scalar estimates produced by root
regularization.
-/

namespace PaperIV.NearH1FinalAssembly

open Finset PaperIV.Model PaperIV.MultiHostTriangleLift
open PaperIV.RD09RootExteriorAdapter PaperIV.RD09CanonicalBadAccounts
open PaperIV.RD09FactorCandidateAverage PaperIV.RD09H1SpokeRealization
open PaperIV.RD09CompleteFactorAdapter PaperIV.RD09CanonicalL2Assembly
open PaperIV.RD09PhaseII
open PaperIV.H1ImprovedConstants PaperIV.RootVocab
open PaperIV.PhysicalCompletion

variable {V I : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
variable [Fintype I] [DecidableEq I]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Once the explicit near-root scalar bounds hold, the already constructed
phase-I packing extends to literal physical RD09 accounts. -/
theorem exists_physicalAccounts_of_regularized_phaseI
    (R : PaperIV.NearH1RootRegularization.RegularizedRoot G)
    (roots : I ≃ {x : V // x ∈ R.root})
    (z : I → V) (E : I → Finset (Sym2 V))
    (hroot : ∀ i, z i = (roots i).1)
    (h1 : IsMultiExteriorHub G z E)
    (hL9 : 1600 * (outsideEdges G R.root).card ≤
      2920 * (multiLiftedPacking z E).card +
        219 * missingIncidences G R.root)
    (hq : R.root.card ≤ (outsideVertices R.root).card)
    (hq2 : 2 ≤ (outsideVertices R.root).card)
    (ha : (1024 : ℚ) ≤ R.reference.card)
    (hqRatio : (87947 : ℚ) / 44352 * R.reference.card ≤
      (outsideVertices R.root).card)
    (hpRatio : (R.root.card : ℚ) / R.reference.card ≤ (101 : ℚ) / 100)
    (hDRatio : (maxMissingColumn G R.root : ℚ) /
      R.reference.card ≤ (1 : ℚ) / 3)
    (htRatio : ((Finset.univ.sup fun i : I => (E i).card : ℕ) : ℚ) /
      R.reference.card ≤ (1 : ℚ) / 256)
    (hsRatio : ((2 * R.root.card - (outsideVertices R.root).card : ℕ) : ℚ) /
      R.reference.card ≤ (1 : ℚ) / 48)
    (hmass : (missingIncidences G R.root : ℚ) +
        2 * (multiLiftedPacking z E).card ≤
      (11 : ℚ) / 2000 * (R.reference.card : ℚ) ^ 2) :
    ∃ P : Finset (Finset V),
      ∃ acc : PaperIV.RD09PhysicalLedger.PhysicalAccounts G P,
        IsK34Packing G P ∧ acc.split = R.root.card ∧
        acc.order = Fintype.card V ∧
        acc.missingEdges = outsideEdges G R.root ∧
        acc.rootLossEdges = PaperIV.RD09SplitEditAccount.missingSpokeEdges G R.root ∧
        ((completion G P).card : ℚ) ≤
          splitBaseline acc.order acc.split -
            (117 : ℚ) / 1825 * (acc.missingEdges.card : ℚ) -
            (12687 : ℚ) / 20000 * (acc.rootLossEdges.card : ℚ) := by
  classical
  have hrootPos : 0 < R.root.card :=
    lt_of_lt_of_le (by omega : 0 < 1000) R.card_ge
  have hrootNonempty : R.root.Nonempty := Finset.card_pos.mp hrootPos
  letI : Nonempty {x : V // x ∈ R.root} :=
    ⟨⟨hrootNonempty.choose, hrootNonempty.choose_spec⟩⟩
  let core := rootEmbedding R.root
  let cand := exteriorEmbedding R.root
  let fac := completeFactor (Z := {x : V // x ∈ R.root})
  let k := Fintype.card {x : V // x ∈ R.root}
  let s := 2 * k - (outsideVertices R.root).card
  let D := maxMissingColumn G R.root
  let t := Finset.univ.sup fun i : I => (E i).card
  let bad := canonicalBad G core cand z E
  have hp : Fintype.card {x : V // x ∈ R.root} = R.root.card := by simp
  have hCandCard : Fintype.card (ExteriorVertex R.root) =
      (outsideVertices R.root).card := by
    simp [ExteriorVertex, card_outsideVertices]
  have hp2 : 2 ≤ R.root.card :=
    le_trans (by omega : 2 ≤ 1000) R.card_ge
  have hk : 0 < k := by simpa [k] using hrootPos
  have hsk : s ≤ k := by dsimp [s, k]; simp; omega
  have hkp : R.root.card - 1 ≤ k := by simp [k]
  have hslots : k + (k - s) ≤
      Fintype.card (ExteriorVertex R.root) := by
    rw [hCandCard]
    dsimp [s, k]
    simp only [Fintype.card_coe]
    omega
  have hA : (∑ x : {v : V // v ∈ R.root},
      missingLoad (G := G) core cand x) = missingIncidences G R.root := by
    simpa [core, cand] using sum_missingLoad_root_exterior (G := G) R.root
  have hD : ∀ x : {v : V // v ∈ R.root},
      missingLoad (G := G) core cand x ≤ D := by
    intro x
    rw [show missingLoad (G := G) core cand x =
      (missingColumn G R.root x.1).card by
        simpa [core, cand] using missingLoad_root_exterior_eq (G := G) R.root x]
    exact card_missingColumn_le_max G R.root x.2
  have ht : ∀ i, (E i).card ≤ t := by
    intro i
    exact Finset.le_sup (f := fun j : I => (E j).card) (Finset.mem_univ i)
  have hroot' : ∀ i, z i = core (roots i) := by
    intro i
    simpa [core, rootEmbedding] using hroot i
  have hassign := exists_canonical_assignment
    (G := G) (k := k) (s := s) (D := D) (t := t)
    (A := missingIncidences G R.root) (fac := fac)
    roots hroot' hp hp2 hsk hkp hk
    (by rwa [hCandCard]) hslots hD ht hA h1
  obtain ⟨α, hraw⟩ := hassign
  have hL10Q :
      ((failedBases s α fac bad).card : ℚ) ≤
        (11 : ℚ) / 100 * missingIncidences G R.root +
          (29 : ℚ) / 1000 * (multiLiftedPacking z E).card := by
    apply l10_of_raw_rd09L2
      (a := (R.reference.card : ℚ))
      (q := ((outsideVertices R.root).card : ℚ))
      (p := (R.root.card : ℚ)) (D := (D : ℚ)) (t := (t : ℚ))
      (s := (s : ℚ)) (A := (missingIncidences G R.root : ℚ))
      (f := ((multiLiftedPacking z E).card : ℚ))
    · exact ha
    · exact hqRatio
    · exact_mod_cast hp2
    · exact hpRatio
    · simpa [D] using hDRatio
    · simpa [t] using htRatio
    · simpa [s, k] using hsRatio
    · positivity
    · positivity
    · positivity
    · positivity
    · positivity
    · exact hmass
    · rw [rd09L2Bound] at hraw
      rw [hCandCard] at hraw
      simpa [hp, bad, fac, core, cand] using hraw
  have hL10 : 200 * (failedBases s α fac bad).card ≤
      35 * missingIncidences G R.root +
        8 * (multiLiftedPacking z E).card := by
    have hA0 : (0 : ℚ) ≤ (missingIncidences G R.root : ℚ) := Nat.cast_nonneg _
    have hf0 : (0 : ℚ) ≤ ((multiLiftedPacking z E).card : ℚ) := Nat.cast_nonneg _
    exact_mod_cast (show
      (200 : ℚ) * (failedBases s α fac bad).card ≤
        35 * missingIncidences G R.root +
          8 * (multiLiftedPacking z E).card by linarith)
  have hcore : ∀ x y : {v : V // v ∈ R.root}, x ≠ y →
      G.Adj (core x) (core y) := by
    intro x y hxy
    exact R.isClique x.2 y.2 (fun h => hxy (Subtype.ext h))
  have hcand : ∀ c : ExteriorVertex R.root,
      ∀ x : {v : V // v ∈ R.root}, cand c ≠ core x := by
    intro c x h
    apply (mem_outsideVertices.mp c.2)
    change cand c ∈ R.root
    rw [h]
    exact x.2
  have hdata : IsFactorCandidateData G core cand fac bad := by
    apply isFactorCandidateData_canonicalBad
    · exact hcore
    · exact hcand
    · exact completeFactor_facMatching
  let B := R.root.card * (outsideVertices R.root).card - Nat.choose R.root.card 2
  have hchoose : Nat.choose R.root.card 2 ≤
      R.root.card * (outsideVertices R.root).card := by
    rw [Nat.choose_two_right]
    have hpred : R.root.card - 1 ≤ (outsideVertices R.root).card := by omega
    exact (Nat.div_le_self _ _).trans
      (Nat.mul_le_mul_left R.root.card hpred)
  have hbase : B + Nat.choose R.root.card 2 =
      R.root.card * (outsideVertices R.root).card := by
    dsimp [B]
    omega
  have hgraph : (graphEdges G).card +
      (PaperIV.RD09SplitEditAccount.missingSpokeEdges G R.root).card =
        Nat.choose R.root.card 2 +
          R.root.card * (outsideVertices R.root).card +
            (outsideEdges G R.root).card := by
    have hrootEdges : (rootEdges G R.root).card = Nat.choose R.root.card 2 :=
      PaperIV.RootVocab.card_rootEdges _ R.root R.isClique
    -- La identidad propia: aristas mas defecto es bloques mas rectangulo completo.
    have hid := PaperIV.RootVocab.card_edgeFinset_add_missingIncidences G R.root
    have hspoke := PaperIV.RD09SplitEditAccount.card_missingSpokeEdges G R.root
    have hge : (graphEdges G).card = G.edgeFinset.card := rfl
    omega
  have hL9' : 1600 * (outsideEdges G R.root).card ≤
      2920 * (multiLiftedPacking z E).card +
        219 * (PaperIV.RD09SplitEditAccount.missingSpokeEdges G R.root).card := by
    rw [PaperIV.RD09SplitEditAccount.card_missingSpokeEdges]
    exact hL9
  have hL10' : 200 * (failedBases s α fac bad).card ≤
      35 * (PaperIV.RD09SplitEditAccount.missingSpokeEdges G R.root).card +
        8 * (multiLiftedPacking z E).card := by
    rw [PaperIV.RD09SplitEditAccount.card_missingSpokeEdges]
    exact hL10
  obtain ⟨acc, hPacking, hsplit0, horder0, hmissing, hrootLoss,
      hremoved, hrecoveredPieces⟩ :=
    exists_h1_literal_physicalAccounts
      (G := G) (s := s) (α := α) (fac := fac)
      h1 roots hroot' hcand hdata
      (B := B) (outsideEdges G R.root)
      (PaperIV.RD09SplitEditAccount.missingSpokeEdges G R.root)
      (by rw [hp, hCandCard]; exact hgraph)
      (by rw [hp, hCandCard]; exact hbase) hL9' hL10'
  have horder : acc.order = Fintype.card V := by
    have hcard : R.root.card + (outsideVertices R.root).card = Fintype.card V := by
      rw [card_outsideVertices]
      exact Nat.add_sub_of_le (Finset.card_le_univ R.root)
    rw [horder0, hp, hCandCard]
    exact_mod_cast hcard
  have hsplit : acc.split = R.root.card := by
    rw [hsplit0, hp]
  have hledger := PaperIV.RD09PhysicalLedger.ledger_of_L3 acc.base_eq acc.L3
  have hremovedLower :=
    PaperIV.RD09PhysicalLedger.removed_lower_of_L9 acc.L9
  have hrecoveredStrong : (acc.recoveredPieces.card : ℚ) ≤
      (11 : ℚ) / 100 * (acc.rootLossEdges.card : ℚ) +
        (29 : ℚ) / 1000 * (acc.removedPieces.card : ℚ) := by
    rw [hrecoveredPieces, card_failedEdgePieces, hrootLoss,
      PaperIV.RD09SplitEditAccount.card_missingSpokeEdges, hremoved]
    exact hL10Q
  have hstrong := ledger_le_improved
    (hA := (by positivity : (0 : ℚ) ≤ (acc.rootLossEdges.card : ℚ)))
    (hf := (by positivity : (0 : ℚ) ≤ (acc.removedPieces.card : ℚ)))
    hledger hremovedLower hrecoveredStrong
  exact ⟨_, acc, hPacking, hsplit, horder, hmissing, hrootLoss, hstrong⟩

/-- Fully discharged scalar wrapper: a scalar-ready regularized root and the
canonical phase-I witness suffice for the literal physical accounts. -/
theorem exists_physicalAccounts_of_ready_phaseI
    [Group I]
    (R : PaperIV.NearH1RootRegularization.RegularizedRoot G)
    (roots : I ≃ {x : V // x ∈ R.root})
    (z : I → V) (E : I → Finset (Sym2 V))
    (hroot : ∀ i, z i = (roots i).1)
    (hE : ∀ i, E i = PaperIV.RD09PaddedHostBase.compatiblePaddedHostBase G
      (exteriorGraph G R.root) I (exteriorEmbedding R.root) (z i) i)
    (h1 : IsMultiExteriorHub G z E)
    (hL9 : 1600 * (outsideEdges G R.root).card ≤
      2920 * (multiLiftedPacking z E).card +
        219 * missingIncidences G R.root) :
    ∃ P : Finset (Finset V),
      ∃ acc : PaperIV.RD09PhysicalLedger.PhysicalAccounts G P,
        IsK34Packing G P ∧ acc.split = R.root.card ∧
        acc.order = Fintype.card V ∧
        acc.missingEdges = outsideEdges G R.root ∧
        acc.rootLossEdges = PaperIV.RD09SplitEditAccount.missingSpokeEdges G R.root ∧
        ((completion G P).card : ℚ) ≤
          splitBaseline acc.order acc.split -
            (117 : ℚ) / 1825 * (acc.missingEdges.card : ℚ) -
            (12687 : ℚ) / 20000 * (acc.rootLossEdges.card : ℚ) := by
  classical
  have hrootPos : 0 < R.root.card :=
    lt_of_lt_of_le (by omega : 0 < 1000) R.card_ge
  have hIcard : Fintype.card I = R.root.card := by
    simpa using Fintype.card_congr roots
  let t := Finset.univ.sup fun i : I => (E i).card
  have hEach : ∀ i : I, (E i).card ≤
      PaperIV.EquitableEdgeColouring.classCeiling (outsideEdges G R.root).card
        (PaperIV.PaddedEquitableColouring.paddedPaletteSize
          (exteriorGraph G R.root) (Fintype.card I)) := by
    intro i
    rw [hE i]
    have hb := (Finset.card_le_card
      (PaperIV.RD09PaddedHostBase.compatiblePaddedHostBase_subset
        (G := G) (H := exteriorGraph G R.root)
        (exteriorEmbedding R.root) (z i) i)).trans
      (PaperIV.RD09PaddedHostBase.card_paddedHostBase_le
        (H := exteriorGraph G R.root) (I := I) (exteriorEmbedding R.root) i)
    rw [card_graphEdges_exteriorGraph (G := G) R.root] at hb
    exact hb
  have hceil :
      PaperIV.EquitableEdgeColouring.classCeiling (outsideEdges G R.root).card
          (PaperIV.PaddedEquitableColouring.paddedPaletteSize
            (exteriorGraph G R.root) (Fintype.card I)) ≤ R.reference.card / 256 := by
    apply PaperIV.NearH1FinalScalars.classCeiling_le_reference_div
      R.reference_large R.root_lower_ratio (by simpa [pow_two] using R.outside_edges_small)
    rw [← hIcard]
    exact PaperIV.PaddedEquitableColouring.hostCount_le_paddedPaletteSize
      (exteriorGraph G R.root) (Fintype.card I)
  have htNat : 256 * t ≤ R.reference.card := by
    have ht : t ≤ R.reference.card / 256 := by
      apply Finset.sup_le
      intro i _
      exact (hEach i).trans hceil
    omega
  have hfNat : (multiLiftedPacking z E).card ≤ (outsideEdges G R.root).card :=
    card_multiLiftedPacking_le_outsideEdges R.root z E hE h1
  have hmassNat : 2000 * (missingIncidences G R.root +
      2 * (multiLiftedPacking z E).card) ≤ 11 * R.reference.card ^ 2 :=
    le_trans (Nat.mul_le_mul_left 2000
      (Nat.add_le_add_left (Nat.mul_le_mul_left 2 hfNat) _)) R.mass_envelope
  have haQ : (0 : ℚ) < R.reference.card := by
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 1024) R.reference_large)
  apply exists_physicalAccounts_of_regularized_phaseI R roots z E hroot h1 hL9
  · exact R.root_le_outside
  · exact R.outside_two
  · exact_mod_cast R.reference_large
  · have hqQ : (87947 : ℚ) * R.reference.card ≤
        44352 * (outsideVertices R.root).card := by exact_mod_cast R.outside_ratio
    nlinarith
  · have hpQ : (100 : ℚ) * R.root.card ≤ 101 * R.reference.card := by
      exact_mod_cast R.root_ratio
    apply (div_le_iff₀ haQ).2
    nlinarith
  · have hDQ : (3 : ℚ) * maxMissingColumn G R.root ≤ R.reference.card := by
      exact_mod_cast R.maxMissing_ratio
    apply (div_le_iff₀ haQ).2
    nlinarith
  · have htQ : (256 : ℚ) * t ≤ R.reference.card := by exact_mod_cast htNat
    apply (div_le_iff₀ haQ).2
    dsimp [t]
    nlinarith
  · have hsQ : (48 : ℚ) *
        (2 * R.root.card - (outsideVertices R.root).card : ℕ) ≤
          R.reference.card := by exact_mod_cast R.slack_ratio
    apply (div_le_iff₀ haQ).2
    nlinarith
  · have hmassQ : (2000 : ℚ) * (missingIncidences G R.root +
        2 * (multiLiftedPacking z E).card) ≤
          11 * (R.reference.card : ℚ) ^ 2 := by
      exact_mod_cast hmassNat
    nlinarith

end PaperIV.NearH1FinalAssembly
