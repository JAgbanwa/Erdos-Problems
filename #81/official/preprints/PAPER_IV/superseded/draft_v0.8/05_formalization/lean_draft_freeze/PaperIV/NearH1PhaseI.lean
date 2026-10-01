import PaperIV.NearH1RootRegularization
import PaperIV.RD09RootExteriorAdapter

/-! # Phase I from a calibrated regularized root -/

namespace PaperIV.NearH1PhaseI

open PaperIV.Model PaperIV.MultiHostTriangleLift
open PaperIV.RootedEliminationOrder
open PaperIV.RD09RootExteriorAdapter

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A regularized root canonically supplies the cyclic indexing, rooted PEO,
and the two scalar inequalities needed by literal RD09 phase I. -/
theorem exists_phaseI_of_regularizedRoot
    (hchordal : PaperIV.IsChordal G)
    (R : PaperIV.NearH1RootRegularization.RegularizedRoot G)
    [NeZero R.root.card] :
    ∃ roots : RootIndex R.root ≃ {x : V // x ∈ R.root},
      ∃ z : RootIndex R.root → V,
      ∃ E : RootIndex R.root → Finset (Sym2 V),
        (∀ i, z i = (roots i).1) ∧
        (∀ i, E i = PaperIV.RD09PaddedHostBase.compatiblePaddedHostBase G
          (exteriorGraph G R.root) (RootIndex R.root)
          (exteriorEmbedding R.root) (z i) i) ∧
        IsMultiExteriorHub G z E ∧
        IsPacking G (multiLiftedPacking z E) ∧
        1600 * (PaperIV.RootVocab.outsideEdges G R.root).card ≤
          2920 * (multiLiftedPacking z E).card +
            219 * PaperIV.RootVocab.missingIncidences G R.root := by
  obtain ⟨O⟩ := exists_order R.root hchordal R.isClique
  have hpalette :
      40 * PaperIV.PaddedEquitableColouring.paddedPaletteSize
          (exteriorGraph G R.root) (Fintype.card (RootIndex R.root)) ≤
        73 * Fintype.card (RootIndex R.root) := by
    have hd := maxDegree_exteriorGraph_le (G := G) R.root
    have hp := R.palette
    simp only [card_RootIndex] at hp ⊢
    unfold PaperIV.PaddedEquitableColouring.paddedPaletteSize at hp ⊢
    omega
  have hwidth :
      40 * ((exteriorGraph G R.root).cliqueNum - 1) ≤
        3 * Fintype.card (RootIndex R.root) := by
    have hc := cliqueNum_exteriorGraph_le (G := G) R.root
    have hw := R.width
    simp only [card_RootIndex]
    omega
  exact exists_rooted_phaseI_with_L9_and_roots O
    (cyclicRootEquiv R.root) hpalette hwidth

end PaperIV.NearH1PhaseI
