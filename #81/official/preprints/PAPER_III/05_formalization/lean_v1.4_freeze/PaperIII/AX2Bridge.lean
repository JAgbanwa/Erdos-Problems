/-
# Paper III — AX2 bridge from the standalone AX2 project

This module converts the standalone `Ax2.ax2` theorem to the exact `PaperIII.AX2`
statement shape. It is intentionally separate from `AX.lean` while the release
perimeter is being migrated.
-/
import PaperIII.AXDefs
import Ax2.Basic

namespace PaperIII

open SimpleGraph

variable {V : Type} [Fintype V] [DecidableEq V]

theorem hasTriangleDecomposition_of_ax2
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (h : Ax2.TriangleDecomposable H) :
    HasTriangleDecomposition H := by
  classical
  obtain ⟨T, hTclique, huniq⟩ := h
  refine ⟨T, hTclique, ?_⟩
  intro e he
  induction e using Sym2.ind with
  | _ a b =>
    obtain ⟨t, ht, huniq_t⟩ := huniq s(a, b) he
    refine ⟨t, ?_, ?_⟩
    · constructor
      · exact ht.1
      · intro v hv
        have he_tri : s(a, b) ∈ Ax2.triEdges t := ht.2
        unfold Ax2.triEdges at he_tri
        rw [Finset.mem_filter] at he_tri
        rcases Sym2.mem_iff.mp hv with rfl | rfl
        · exact (Finset.mk_mem_sym2_iff.mp he_tri.1).1
        · exact (Finset.mk_mem_sym2_iff.mp he_tri.1).2
    · intro u hu
      apply huniq_t
      refine ⟨hu.1, ?_⟩
      unfold Ax2.triEdges
      rw [Finset.mem_filter]
      refine ⟨?_, ?_⟩
      · rw [Finset.mk_mem_sym2_iff]
        exact ⟨hu.2 a (by simp), hu.2 b (by simp)⟩
      · intro hdiag
        rw [Sym2.mk_isDiag_iff] at hdiag
        subst hdiag
        rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
        exact SimpleGraph.irrefl H he

-- (The legacy `AX2_from_Ax2_of_nibbleGap`, which routed through the sorried ax2 Part B via
-- `Ax2.ax2_of_nibbleGap`, was removed: the unconditional assembly uses
-- `hasTriangleDecomposition_of_ax2` with `BKLO.triangle_decomposition_dense`, so this bridge needs
-- only `Ax2.Basic` and the sorried Part B leaves the dependency closure entirely.)

end PaperIII
