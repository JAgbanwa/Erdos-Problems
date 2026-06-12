import ErdosProblems.Problem261.Basic

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Tactic

/-!
# Telescoping identities for `f(k) = k/2^k`

Paper Lemma 0 and the block-sum formula \eqref{eq:block}.
-/

namespace ErdosProblem261

lemma f_pos (k : ℕ) (hk : 0 < k) : 0 < f k := by
  unfold f
  exact div_pos (Nat.cast_pos.mpr hk) (pow_pos (by norm_num) k)

lemma G_sub_G_succ (m : ℕ) (hm : 0 < m) :
    G m hm - G (m + 1) (Nat.succ_pos m) = f m := by
  unfold G f
  field_simp
  ring_nf
  rcases m with _ | m
  · exact hm.false.elim
  · simp [Nat.add_sub_cancel, pow_succ]
    ring

/-- Block sum `∑_{k=m}^{M} f(k) = G(m) - G(M+1)` (paper \eqref{eq:block}). -/
lemma blockSum (m M : ℕ) (hm : 0 < m) (hM : m ≤ M) :
    (Finset.Icc m M).sum f = G m hm - G (M + 1) (Nat.succ_pos M) := by
  induction hM with
  | refl =>
      simp [Finset.Icc_self, G_sub_G_succ m hm]
  | @step M hle ih =>
      have hIcc :
          Finset.Icc m (M + 1) = insert (M + 1) (Finset.Icc m M) := by
        ext x
        simp only [Finset.mem_Icc, Finset.mem_insert]
        constructor
        · intro ⟨hm1, hx⟩
          rcases le_iff_eq_or_lt.mp hx with (rfl | hxlt)
          · exact Or.inl rfl
          · exact Or.inr ⟨hm1, Nat.le_of_lt_succ hxlt⟩
        · intro hx
          rcases hx with (rfl | ⟨hm1, hx⟩)
          · exact ⟨Nat.le_trans hle (Nat.le_succ M), le_rfl⟩
          · exact ⟨hm1, Nat.le_succ_of_le hx⟩
      rw [hIcc, Finset.sum_insert]
      · rw [ih]; linarith [G_sub_G_succ (M + 1) (Nat.succ_pos M)]
      · simp [Finset.mem_Icc]

end ErdosProblem261
