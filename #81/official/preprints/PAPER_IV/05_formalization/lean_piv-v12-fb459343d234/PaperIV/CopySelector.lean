import PaperIV.TerminalSplit
import PaperIV.CloneMeasure
import PaperIV.Dirac1
import PaperIV.ChordalStructure

/-!
# A literal admissible copy selector

For every chordal graph not already in the terminal universal-core split class,
we construct one orientation of a class copy.  All graph-theoretic side
conditions used by chordality preservation and clone-count descent are fields
proved from the selected pair, rather than assumptions of an interface.
-/

namespace PaperIV.CopySelector

open Finset SimpleGraph
open PaperIV.ChordalBasics

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The cycle formulation used by the copy operation supplies the structural
Dirac package consumed by the terminal selector. -/
def chordalStructure_of_isChordal (G : SimpleGraph V) (hG : PaperIV.IsChordal G) :
    PaperIV.ChordalStructure G where
  isChordal := hG
  simplicial_hereditary := by
    intro W hW
    letI : Fintype W := Fintype.ofFinite W
    have hWchord : PaperIV.IsChordal (G.induce W) :=
      PaperIV.isChordal_induce G hG W
    obtain ⟨v, hv⟩ := PaperIV.dirac_simplicial (G.induce W) hWchord (by
      rcases hW with ⟨x, hx⟩
      exact ⟨⟨x, hx⟩⟩)
    exact ⟨v, hv⟩
  two_nonadj_simplicial := by
    intro hconn hnoncomplete
    have hG' : G.IsChordal := by
      simpa only [PaperIV.IsChordal, SimpleGraph.IsChordal] using hG
    exact hG'.exists_two_nonadj_isSimplicial hconn hnoncomplete

/-- Data of one structurally admissible class-copy step. -/
structure AdmissibleCopy (G : SimpleGraph V) [DecidableRel G.Adj] where
  source : Finset V
  target : Finset V
  source_nonempty : (univ.filter (fun v => G.neighborFinset v = source)).Nonempty
  target_nonempty : (univ.filter (fun v => G.neighborFinset v = target)).Nonempty
  distinct : source ≠ target
  source_avoids_target : ∀ v, G.neighborFinset v = source → v ∉ target
  target_clique : G.IsClique (target : Set V)

theorem chordal_after (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : AdmissibleCopy G) (hG : PaperIV.IsChordal G) :
    PaperIV.IsChordal (PaperIV.ClassCopy.graph G s.source s.target) :=
  PaperIV.chordal_classCopy G s.source s.target hG s.target_clique

theorem cloneClassCount_after_lt (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : AdmissibleCopy G) :
    PaperIV.CloneMeasure.cloneClassCount (PaperIV.ClassCopy.graph G s.source s.target) <
      PaperIV.CloneMeasure.cloneClassCount G :=
  PaperIV.CloneMeasure.cloneClassCount_classCopy_lt G s.source s.target
    s.source_nonempty s.target_nonempty s.distinct s.source_avoids_target

/-- A non-terminal chordal graph has an admissible class-copy orientation.
The target is the neighbourhood of a simplicial vertex, hence a clique; the
source class is disjoint from it because all of its members have the same
neighbourhood as a vertex nonadjacent to that target vertex. -/
theorem exists_admissibleCopy (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : PaperIV.IsChordal G)
    (hnonsplit : ¬ PaperIV.TerminalSplit.IsUniversalCoreSplit G) :
    Nonempty (AdmissibleCopy G) := by
  obtain ⟨x, y, hx, hy, hxy, hneq⟩ :=
    PaperIV.TerminalSplit.exists_nonterminal_simplicial_pair G
      (chordalStructure_of_isChordal G hG) hnonsplit
  let A := G.neighborFinset x
  let B := G.neighborFinset y
  have hxA : G.neighborFinset x = A := rfl
  have hyB : G.neighborFinset y = B := rfl
  have hAneB : A ≠ B := by
    intro h
    apply hneq
    have hset := congrArg (fun T : Finset V => (T : Set V)) h
    simpa [A, B] using hset
  have hsource : (univ.filter (fun v => G.neighborFinset v = A)).Nonempty := by
    refine ⟨x, ?_⟩
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hxA⟩
  have htarget : (univ.filter (fun v => G.neighborFinset v = B)).Nonempty := by
    refine ⟨y, ?_⟩
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hyB⟩
  have havoid : ∀ v, G.neighborFinset v = A → v ∉ B := by
    intro v hvA hvB
    have hyv : G.Adj y v := (G.mem_neighborFinset y v).mp (by
      rw [hyB]
      exact hvB)
    have hyNv : y ∈ G.neighborFinset v := (G.mem_neighborFinset v y).mpr hyv.symm
    have hyNx : y ∈ G.neighborFinset x := by
      rw [hvA, ← hxA] at hyNv
      exact hyNv
    exact hxy ((G.mem_neighborFinset x y).mp hyNx)
  have hclique : G.IsClique (B : Set V) := by
    simpa [B] using hy
  exact ⟨⟨A, B, hsource, htarget, hAneB, havoid, hclique⟩⟩

end PaperIV.CopySelector
