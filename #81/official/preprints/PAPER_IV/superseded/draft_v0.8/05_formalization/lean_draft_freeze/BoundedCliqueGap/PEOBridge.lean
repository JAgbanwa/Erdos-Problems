import BoundedCliqueGap.QPES
import PaperIV.CliqueTree

/-!
# Bridge: the tree's own chordality primitives feed the Route B recursion

The extracted Route B development carries its own encoding of chordality (a *peeling
list*, `BoundedCliqueGap.IsPeelOrder`, and the derived numbering
`BoundedCliqueGap.RevPES`).  This module removes that duplication at the entry point of
the theory by producing a `RevPES` numbering directly from the primitives that this tree
already has:

* `SimpleGraph.IsPEO` and `SimpleGraph.peoRank` (`PaperIV/CliqueTree/PEO.lean`),
* `SimpleGraph.IsChordal` and `SimpleGraph.IsChordal.exists_isPEO`
  (`PaperIV/ChordalStructure.lean` + `PaperIV/CliqueTree/PEO.lean`).

## Main results

* `BoundedCliqueGap.revPES_peoRank` — a perfect elimination order in the sense of
  `SimpleGraph.IsPEO` yields the reverse numbering `RevPES` used by the recursion.
* `BoundedCliqueGap.exists_revPES_of_simpleGraph_isChordal` — hence every graph that is
  chordal in the sense of `SimpleGraph.IsChordal` carries such a numbering.
-/

namespace BoundedCliqueGap

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
/-- `SimpleGraph.peoRank` reverses the order: it is strictly antitone in `ord`. -/
theorem peoRank_le_of_ord_le {ord : V → ℕ} {u v : V} (h : ord u ≤ ord v) :
    SimpleGraph.peoRank ord v ≤ SimpleGraph.peoRank ord u := by
  refine Finset.card_le_card ?_
  intro w hw
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
  omega

omit [DecidableEq V] in
/-- The reverse numbering is strictly decreasing exactly where `ord` increases. -/
theorem ord_lt_of_peoRank_lt {ord : V → ℕ} {u v : V} (h : SimpleGraph.peoRank ord v <
    SimpleGraph.peoRank ord u) : ord u < ord v := by
  by_contra hle
  exact absurd (peoRank_le_of_ord_le (le_of_not_gt hle)) (not_le.2 h)

/-- **From a perfect elimination order to the reverse numbering.**  If `ord` is a perfect
elimination order of `H` in the sense of `SimpleGraph.IsPEO`, then `SimpleGraph.peoRank ord`
is a reverse perfect elimination numbering in the sense of `RevPES`. -/
theorem revPES_peoRank {H : SimpleGraph V} {ord : V → ℕ} (h : H.IsPEO ord) :
    RevPES H (SimpleGraph.peoRank ord) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro a b hab
    rcases lt_trichotomy (ord a) (ord b) with hlt | heq | hgt
    · exact absurd hab (by
        have := SimpleGraph.peoRank_lt_of_ord_lt hlt
        omega)
    · exact h.injective heq
    · exact absurd hab (by
        have := SimpleGraph.peoRank_lt_of_ord_lt hgt
        omega)
  · intro v
    have hv : v ∉ Finset.univ.filter fun u => ord v < ord u := by simp
    have : (Finset.univ.filter fun u => ord v < ord u) ⊂ (Finset.univ : Finset V) :=
      ⟨Finset.filter_subset _ _, fun hsub => hv (hsub (Finset.mem_univ v))⟩
    simpa [SimpleGraph.peoRank, Finset.card_univ] using Finset.card_lt_card this
  · intro v u w hvu hvw hu hw huw
    have hu' : ord v < ord u := ord_lt_of_peoRank_lt hu
    have hw' : ord v < ord w := ord_lt_of_peoRank_lt hw
    exact h.isClique_later v (by exact ⟨hu', hvu⟩) (by exact ⟨hw', hvw⟩) huw

/-- **Every chordal graph carries a reverse perfect elimination numbering**, with
chordality taken in the sense of `SimpleGraph.IsChordal` (no chordless cycle of length
`≥ 4`) rather than in the peeling-list sense of the extracted development. -/
theorem exists_revPES_of_simpleGraph_isChordal {H : SimpleGraph V} (hc : H.IsChordal) :
    ∃ ord : V → ℕ, RevPES H ord := by
  obtain ⟨f, hf⟩ := hc.exists_isPEO
  exact ⟨SimpleGraph.peoRank f, revPES_peoRank hf⟩

end BoundedCliqueGap
