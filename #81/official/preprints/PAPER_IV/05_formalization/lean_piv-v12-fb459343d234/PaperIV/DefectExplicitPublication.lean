import E35.Theorem
import PaperIV.DefectSharpPublication

/-! Version 1.2 public upper bound and maximum use the explicit E34 removal
route. The earlier existential interface is preserved, not overwritten.
Its independently proved lower witness is reused below. -/
namespace PaperIV.DefectExplicitPublication
open PaperIV.FarRounding PaperIV.RootedSimplicialDefect PaperIV.DefectTargetArithmetic

theorem rooted_defect_eventual (s : ℕ) :
    ∃ N, ∀ n, N ≤ n → ∀ G : SimpleGraph (Fin n), ∀ [DecidableRel G.Adj],
      RootedDefectAt G s →
      ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size ≤ defectTarget s n := by
  exact ⟨E33.Fexp E34.NeditE s, fun n hn G _ hG =>
    E34.theoremC_fully_explicit_final s n hn G hG⟩

theorem rooted_defect_maximum (s : ℕ) :
    ∃ N, ∀ n, N ≤ n →
      (∀ G : SimpleGraph (Fin n), ∀ [DecidableRel G.Adj], RootedDefectAt G s →
        ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size ≤ defectTarget s n) ∧
      (∃ (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj), RootedDefectAt G s ∧
        ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size = defectTarget s n ∧
          ∀ R : CliquePartition G, Q.size ≤ R.size) := by
  obtain ⟨N, hN⟩ := rooted_defect_eventual s
  refine ⟨max N (2 * s + 2), fun n hn => ?_⟩
  have hlarge : N ≤ n := (le_max_left _ _).trans hn
  refine ⟨hN n hlarge, ?_⟩
  obtain ⟨G, inst, hG, hl⟩ := DefectSharpPublication.exists_defect_lower_witness s n
    ((le_max_right _ _).trans hn)
  letI := inst
  obtain ⟨Q, hQ4, hQ⟩ := hN n hlarge G hG
  have heq : Q.size = defectTarget s n := le_antisymm hQ (hl Q)
  exact ⟨G, inst, hG, Q, hQ4, heq, fun R => heq.trans_le (hl R)⟩

end PaperIV.DefectExplicitPublication

