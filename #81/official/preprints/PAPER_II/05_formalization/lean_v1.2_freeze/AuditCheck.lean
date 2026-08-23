import PaperII.Unconditional

open PaperII

-- Independent audit checks (Gate H).
-- 1. The exact axiom footprint of the unconditional Theorem 1.2.
#print axioms PaperII.theorem_1_2

-- 2. The statement type (hypotheses must be exactly IsChordal; no ChordalStructure / A2Transfer).
#check @PaperII.theorem_1_2

-- 3. The standard chord definition used.
#check @PaperII.IsChordal
#print PaperII.IsChordal
