import PaperIV.TerminalSplit
import PaperIV.SplitUniformIncidence

/-!
# Literal adapter from a terminal universal-core split graph to `splitGraph`
-/

namespace PaperIV.TerminalSplitAdapter

open Finset
open PaperIV.SplitUniformIncidence

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def coreFinset (C : Set V) : Finset V := by
  classical
  exact univ.filter fun v => v ∈ C

noncomputable def hostFinset (C : Set V) : Finset V := by
  classical
  exact univ.filter fun v => v ∉ C

@[simp] theorem mem_coreFinset (C : Set V) (v : V) : v ∈ coreFinset C ↔ v ∈ C := by
  classical
  simp [coreFinset]

@[simp] theorem mem_hostFinset (C : Set V) (v : V) : v ∈ hostFinset C ↔ v ∉ C := by
  classical
  simp [hostFinset]

theorem core_host_disjoint (C : Set V) : Disjoint (coreFinset C) (hostFinset C) := by
  classical
  refine Finset.disjoint_left.mpr fun v hvC hvH => ?_
  exact (mem_hostFinset C v).mp hvH ((mem_coreFinset C v).mp hvC)

/-- A graph with a universal core and independent complement is literally the
complete split graph on the core and its complement, on the same vertex type. -/
theorem eq_splitGraph_of_isUniversalCoreSplit
    (G : SimpleGraph V) (hG : PaperIV.TerminalSplit.IsUniversalCoreSplit G) :
    ∃ C : Set V, G = splitGraph (coreFinset C) (hostFinset C) := by
  classical
  obtain ⟨C, huniv, hind⟩ := hG
  refine ⟨C, ?_⟩
  ext x y
  constructor
  · intro hxy
    have hne : x ≠ y := hxy.ne
    by_cases hx : x ∈ C
    · by_cases hy : y ∈ C
      · exact ⟨hne, Or.inl ⟨(mem_coreFinset C x).mpr hx, (mem_coreFinset C y).mpr hy⟩⟩
      · exact ⟨hne, Or.inr (Or.inl ⟨(mem_coreFinset C x).mpr hx,
          (mem_hostFinset C y).mpr hy⟩)⟩
    · by_cases hy : y ∈ C
      · exact ⟨hne, Or.inr (Or.inr ⟨(mem_hostFinset C x).mpr hx,
          (mem_coreFinset C y).mpr hy⟩)⟩
      · exact False.elim (hind x hx y hy hxy)
  · rintro ⟨hne, ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩⟩
    · exact huniv x ((mem_coreFinset C x).mp hx) y hne.symm
    · exact huniv x ((mem_coreFinset C x).mp hx) y hne.symm
    · exact (huniv y ((mem_coreFinset C y).mp hy) x hne).symm

end PaperIV.TerminalSplitAdapter
