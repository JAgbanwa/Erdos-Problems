import PaperIV.PhysicalCompletion
import PaperIV.CanonicalBudget

/-!
# Terminal physical ledger

This is the accounting interface for T01--T08.  It does not construct the
edge-colouring, factors, or paired hosts.  Instead, it makes their one
remaining numerical obligation explicit: a `K3`/`K4` packing with the stated
two-phase ledger immediately yields an exact physical partition and pays the
RD09 terminal budget.
-/

namespace PaperIV.TerminalLedger

open PaperIV.Model PaperIV.PhysicalCompletion

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The output promised by the still-open physical constructor.  The
`ledger` equality is deliberately its only numerical input: the earlier
construction stages must establish it from their literal `f` and `g` counts. -/
structure PhysicalTerminal where
  packing : Finset (Finset V)
  isK34 : IsK34Packing G packing
  base : ℚ
  missing : ℚ
  rootLoss : ℚ
  removed : ℚ
  recovered : ℚ
  ledger : ((completion G packing).card : ℚ) =
    base + missing - rootLoss - 2 * removed + 2 * recovered
  removed_lower : (40 : ℚ) / 73 * missing - (3 : ℚ) / 40 * rootLoss ≤ removed
  recovered_upper : recovered ≤ (7 : ℚ) / 40 * rootLoss + removed / 25

/-- Any literal physical packing has a canonical neutral terminal ledger:
take the exact completion count as baseline and set every defect account to
zero.  This is useful when a construction already supplies its target bound
directly, independently of the non-neutral RD09 regularization ledger. -/
def PhysicalTerminal.neutral (P : Finset (Finset V)) (hP : IsK34Packing G P) :
    PhysicalTerminal (G := G) where
  packing := P
  isK34 := hP
  base := ((completion G P).card : ℚ)
  missing := 0
  rootLoss := 0
  removed := 0
  recovered := 0
  ledger := by norm_num
  removed_lower := by norm_num
  recovered_upper := by norm_num

@[simp] theorem PhysicalTerminal.neutral_packing (P : Finset (Finset V))
    (hP : IsK34Packing G P) : (PhysicalTerminal.neutral P hP).packing = P := rfl

@[simp] theorem PhysicalTerminal.neutral_base (P : Finset (Finset V))
    (hP : IsK34Packing G P) :
    (PhysicalTerminal.neutral P hP).base = ((completion G P).card : ℚ) := rfl

@[simp] theorem PhysicalTerminal.neutral_zero_accounts (P : Finset (Finset V))
    (hP : IsK34Packing G P) :
    (PhysicalTerminal.neutral P hP).missing = 0 ∧
      (PhysicalTerminal.neutral P hP).rootLoss = 0 ∧
      (PhysicalTerminal.neutral P hP).removed = 0 ∧
      (PhysicalTerminal.neutral P hP).recovered = 0 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Every terminal constructor output has a literal exact edge partition. -/
theorem PhysicalTerminal.exactPartition (T : PhysicalTerminal (G := G)) :
    IsExactPartition G (completion G T.packing) :=
  isExactPartition_completion T.isK34.toIsPacking

/-- The two-phase ledger with the RD09 lower bound on removed pieces and upper
bound on recovered pieces yields the stronger exact-piece terminal estimate. -/
theorem PhysicalTerminal.count_le_exact_piece_bound
    (T : PhysicalTerminal (G := G)) :
    ((completion G T.packing).card : ℚ) ≤
      T.base - (19 : ℚ) / 365 * T.missing - (253 : ℚ) / 500 * T.rootLoss :=
  PaperIV.ParametricBudget.exact_piece_budget T.ledger T.removed_lower T.recovered_upper

/-- In particular, the physical output pays the weaker RD09 budget required
by the canonical-deficit interface. -/
theorem PhysicalTerminal.count_le_paid
    (T : PhysicalTerminal (G := G))
    (hmissing : 0 ≤ T.missing) (hrootLoss : 0 ≤ T.rootLoss) :
    ((completion G T.packing).card : ℚ) ≤
      T.base - T.missing / 20 - T.rootLoss / 2 := by
  have hstrong := T.count_le_exact_piece_bound
  have hcoeff := PaperIV.ParametricBudget.rd09_coefficients
  nlinarith

/-- The terminal ledger is now a direct input to the global factor-20 defect
budget.  Thus T07--T08 reduce to proving the physical constructor's ledger
and the nonnegativity/base displacement conditions. -/
theorem PhysicalTerminal.defects_le_twenty_total
    (T : PhysicalTerminal (G := G))
    {M U : ℚ}
    (hbase : 0 ≤ M - T.base)
    (hmissing : 0 ≤ T.missing) (hrootLoss : 0 ≤ T.rootLoss)
    : T.missing + T.rootLoss ≤ 20 *
      (PaperIV.CanonicalBudget.historicalDeficit M U +
        PaperIV.CanonicalBudget.geometricDeficit U ((completion G T.packing).card : ℚ)) := by
  apply PaperIV.CanonicalBudget.physical_defects_le_twenty_total hbase hmissing hrootLoss
  exact T.count_le_paid hmissing hrootLoss

end PaperIV.TerminalLedger
