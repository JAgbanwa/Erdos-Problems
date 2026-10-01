import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Data.Rat.Star
import Mathlib.Tactic.Positivity

/-!
# Uniform capacity accounting for a complete split

The scalar split LP supplies aggregate consumptions of the inner-edge and
cross-edge classes.  Once a graph construction distributes a given aggregate
uniformly within its edge class, this module proves the per-edge unit-capacity
condition.  The remaining graph-specific task is solely to establish that the
chosen clique families have those uniform incidences.
-/

namespace PaperIV.UniformSplitLoads

theorem uniform_load_le_one {classSize total : ℚ}
    (hsize : 0 < classSize) (htotal : total ≤ classSize) :
    total / classSize ≤ 1 := by
  exact (div_le_one₀ hsize).mpr htotal

/-- The aggregate LP constraints imply unit capacity in both nonempty edge
classes after uniform distribution. -/
theorem uniform_split_capacities {a b u v w : ℚ}
    (ha : 0 < a) (hb : 0 < b)
    (hinner : u + 3 * v + 6 * w ≤ a)
    (hcross : 2 * u + 3 * v ≤ b) :
    (u + 3 * v + 6 * w) / a ≤ 1 ∧ (2 * u + 3 * v) / b ≤ 1 :=
  ⟨uniform_load_le_one ha hinner, uniform_load_le_one hb hcross⟩

/-- If an edge class is empty, a nonnegative aggregate load bounded by its
size is necessarily zero.  This is the arithmetic guard for split
degeneracies. -/
theorem zero_class_forces_zero {total : ℚ}
    (hnonneg : 0 ≤ total) (hbound : total ≤ 0) : total = 0 := by
  linarith

end PaperIV.UniformSplitLoads
