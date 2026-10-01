import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Data.Rat.Star
import Mathlib.Tactic.Positivity

/-!
# The sharp quadratic envelope

This is the scalar identity used to turn a paid terminal partition into local stability. We work over rationals first; graph cardinalities will later be cast into this statement.
-/

namespace PaperIV

def sharpEnvelope (n : ℚ) : ℚ := (2 * n + 1) ^ 2 / 24

def splitBaseline (n p : ℚ) : ℚ := p * (n - p) - p * (p - 1) / 2

theorem sharpEnvelope_sub_splitBaseline (n p : ℚ) :
    sharpEnvelope n - splitBaseline n p = (6 * p - 2 * n - 1) ^ 2 / 24 := by
  simp only [sharpEnvelope, splitBaseline]
  ring

theorem splitBaseline_le_sharpEnvelope (n p : ℚ) :
    splitBaseline n p ≤ sharpEnvelope n := by
  rw [← sub_nonneg]
  rw [sharpEnvelope_sub_splitBaseline]
  positivity

end PaperIV
