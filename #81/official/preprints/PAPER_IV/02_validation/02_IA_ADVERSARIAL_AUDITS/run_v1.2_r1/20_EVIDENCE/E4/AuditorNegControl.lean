import Lean.Elab.Command
/-! Auditor negative control for E4 (expected: the runner reports FAIL because of the `sorry`
warning, and `#print axioms` lists `sorryAx` and `AuditorNeg.bogus`). Not part of the author's cut. -/
namespace AuditorNeg
axiom bogus : False
theorem uses_bogus : 1 = 2 := bogus.elim
theorem uses_sorry : 2 = 3 := by sorry
end AuditorNeg
#print axioms AuditorNeg.uses_bogus
#print axioms AuditorNeg.uses_sorry
