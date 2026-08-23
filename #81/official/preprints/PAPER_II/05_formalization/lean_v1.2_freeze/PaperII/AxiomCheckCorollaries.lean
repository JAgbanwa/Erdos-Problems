import PaperII.AsymptoticCorollaries

-- Gate check: the arithmetic corollaries rest only on Lean's standard classical axioms
-- (`propext`, `Classical.choice`, `Quot.sound`) — no `sorryAx`, no project axiom.
#print axioms PaperII.phiTau_max_sandwich
#print axioms PaperII.phiTau_max_le_paperI_bound
#print axioms PaperII.odd_sq_emod_24
#print axioms PaperII.phiTau_max_closed
