import ErdosProblems.Problem261.Basic
import ErdosProblems.Problem261.Corridor
import ErdosProblems.Problem261.Q1

import Mathlib.Tactic

/-!
# Explicit certificates from Table 1 (paper Theorem 4.3)

Each entry is verified by exact rational arithmetic (`native_decide`), except
`n = 4` and `n = 11` which follow from Theorem 1.
-/

namespace ErdosProblem261

theorem tableCert_1 : HasFiniteRepresentation 1 {4, 5, 6} := by
  unfold HasFiniteRepresentation; refine ⟨by decide, by intro k hk; simp at hk; omega, ?_⟩
  native_decide

theorem tableCert_2 : HasFiniteRepresentation 2 {4, 5, 6} := by
  unfold HasFiniteRepresentation; refine ⟨by decide, by intro k hk; simp at hk; omega, ?_⟩
  native_decide

theorem tableCert_3 : HasFiniteRepresentation 3 {4, 6, 8} := by
  unfold HasFiniteRepresentation; refine ⟨by decide, by intro k hk; simp at hk; omega, ?_⟩
  native_decide

theorem tableCert_4 : HasFiniteRepresentation 4 {5, 6} :=
  familyRepresentation 3 (by decide)

theorem tableCert_5 : HasFiniteRepresentation 5 {6, 7, 11, 13, 14} := by
  unfold HasFiniteRepresentation; refine ⟨by decide, by intro k hk; simp at hk; omega, ?_⟩
  native_decide

theorem tableCert_6 : HasFiniteRepresentation 6 {7, 8, 11, 13, 14} := by
  unfold HasFiniteRepresentation; refine ⟨by decide, by intro k hk; simp at hk; omega, ?_⟩
  native_decide

theorem tableCert_7 : HasFiniteRepresentation 7 {8, 9, 12, 13, 14, 15, 20, 21, 24} := by
  unfold HasFiniteRepresentation; refine ⟨by decide, by intro k hk; simp at hk; omega, ?_⟩
  native_decide

theorem tableCert_9 : HasFiniteRepresentation 9 {10, 11, 13, 14} := by
  unfold HasFiniteRepresentation; refine ⟨by decide, by intro k hk; simp at hk; omega, ?_⟩
  native_decide

theorem tableCert_11 : HasFiniteRepresentation 11 {12, 13, 14} :=
  familyRepresentation 4 (by decide)

theorem tableCert_12 : HasFiniteRepresentation 12 {13, 14, 15, 20, 21, 24} := by
  unfold HasFiniteRepresentation; refine ⟨by decide, by intro k hk; simp at hk; omega, ?_⟩
  native_decide

theorem tableCert_15 : HasFiniteRepresentation 15 {16, 17, 18, 21, 22} := by
  unfold HasFiniteRepresentation; refine ⟨by decide, by intro k hk; simp at hk; omega, ?_⟩
  native_decide

theorem question1_table (n : ℕ) :
    n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 9 ∨
      n = 11 ∨ n = 12 ∨ n = 15 → Question1 n := by
  rintro hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨{4, 5, 6}, tableCert_1⟩
  · exact ⟨{4, 5, 6}, tableCert_2⟩
  · exact ⟨{4, 6, 8}, tableCert_3⟩
  · exact ⟨{5, 6}, tableCert_4⟩
  · exact ⟨{6, 7, 11, 13, 14}, tableCert_5⟩
  · exact ⟨{7, 8, 11, 13, 14}, tableCert_6⟩
  · exact ⟨{8, 9, 12, 13, 14, 15, 20, 21, 24}, tableCert_7⟩
  · exact ⟨{10, 11, 13, 14}, tableCert_9⟩
  · exact ⟨{12, 13, 14}, tableCert_11⟩
  · exact ⟨{13, 14, 15, 20, 21, 24}, tableCert_12⟩
  · exact ⟨{16, 17, 18, 21, 22}, tableCert_15⟩

end ErdosProblem261
