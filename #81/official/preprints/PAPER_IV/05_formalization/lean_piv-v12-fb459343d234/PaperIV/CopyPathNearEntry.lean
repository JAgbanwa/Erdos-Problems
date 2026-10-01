import PaperIV.CopyPathWindow
import PaperIV.DeficitAlongPath

/-!
# The near-entry contract of a bounded copy path

This module is deliberately graph-free.  A future simplicial-copy construction
supplies the literal edge supports, its `n - 2` edit bound, and monotonicity of
the value along the path.  The theorem below then returns one *same* canonical
index carrying both the E3 first-entry window and the propagated near-envelope
bound.  Thus the copy construction cannot accidentally use different indices
for its metric and numerical obligations.
-/

namespace PaperIV.CopyPathNearEntry

open PaperIV.EditMetric
open PaperIV.CopyPathWindow

variable {V : Type*} [DecidableEq V]
variable {N : ℕ}

theorem exists_window_and_near_value_of_copy_steps
    (n : ℕ) (hn : 2 ≤ n)
    (F : Finset (Finset V)) (hF : F.Nonempty)
    (A : Fin (N + 1) → Finset V) (r Q δ : ℚ)
    (value : Fin (N + 1) → ℚ)
    (hstart : r ≤ famDistNorm F hF (A 0) ((n : ℚ) ^ 2))
    (hend : famDistNorm F hF (A (Fin.last N)) ((n : ℚ) ^ 2) < r)
    (hstep : ∀ i : Fin N, editDist (A i.succ) (A i.castSucc) ≤ n - 2)
    (hupper : ∀ i, value i ≤ Q)
    (hmono : ∀ i, value 0 ≤ value i)
    (hnear : Q - value 0 ≤ δ) :
    ∃ j : Fin (N + 1),
      (∀ i : Fin (N + 1), famDistNorm F hF (A i) ((n : ℚ) ^ 2) < r → j ≤ i) ∧
      r - 1 / (n : ℚ) ≤ famDistNorm F hF (A j) ((n : ℚ) ^ 2) ∧
      famDistNorm F hF (A j) ((n : ℚ) ^ 2) < r ∧
      Q - δ ≤ value j := by
  obtain ⟨j, hj_min, hj_low, hj_high⟩ :=
    exists_window_of_copy_steps n hn F hF A r hstart hend hstep
  refine ⟨j, hj_min, hj_low, hj_high, ?_⟩
  exact terminal_near_of_initial_near (hupper j) (hmono j) hnear

end PaperIV.CopyPathNearEntry
