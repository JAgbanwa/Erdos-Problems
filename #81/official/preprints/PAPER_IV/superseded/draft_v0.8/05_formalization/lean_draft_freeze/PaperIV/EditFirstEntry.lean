import PaperIV.EditMetric
import PaperIV.FirstEntryWindow

/-!
# First entry induced by bounded edit steps

This is the E3 interface in the exact form consumed by the copy path.  It
contains no graph-theoretic construction: a labelled path of finite supports,
a fixed nonempty target family, and a per-step edit budget yield the canonical
first-entry window for distance to that family.
-/

namespace PaperIV.EditFirstEntry

open PaperIV.EditMetric
open PaperIV.FirstEntryWindow

variable {V : Type*} [DecidableEq V]
variable {N : ℕ}

theorem exists_window_of_edit_steps
    (F : Finset (Finset V)) (hF : F.Nonempty)
    (A : Fin (N + 1) → Finset V) (m r δ : ℚ) (hm : 0 < m)
    (h0 : r ≤ famDistNorm F hF (A 0) m)
    (hlast : famDistNorm F hF (A (Fin.last N)) m < r)
    (hstep : ∀ i : Fin N,
      (editDist (A i.succ) (A i.castSucc) : ℚ) / m ≤ δ) :
    ∃ j : Fin (N + 1),
      (∀ i : Fin (N + 1), famDistNorm F hF (A i) m < r → j ≤ i) ∧
      r - δ ≤ famDistNorm F hF (A j) m ∧
      famDistNorm F hF (A j) m < r := by
  apply exists_first_entry_window (d := fun i => famDistNorm F hF (A i) m)
    (r := r) h0 hlast
  intro i
  exact le_trans (abs_sub_famDistNorm_le F hF (A i.succ) (A i.castSucc) hm) (hstep i)

end PaperIV.EditFirstEntry
