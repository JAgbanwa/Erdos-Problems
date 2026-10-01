import PaperIV.RD09TerminalAssembly
import PaperIV.SharpEnvelope

/-!
# The genuine physical RD09 ledger: from literal counts to the paid terminal

`RD09TerminalAssembly.RD09NumericLedger` and
`TerminalLedger.PhysicalTerminal` are stated over `ℚ`.  Their five accounts
are, physically,

```text
base      = splitBaseline n p      (the split baseline of the near regime)
missing   = m                      (number of missing edges)
rootLoss  = A                      (root-factor loss)
removed   = f = |removedPieces|    (cardinality of the removed family)
recovered = g = |recoveredPieces|  (cardinality of the recovered family)
```

This module builds the adapter in the *only* legitimate direction: the three
literal counting identities

* **L3** (two-phase ledger, a `Nat` identity)
  `|completion G P| + A + 2 f = B + m + 2 g`,
* **L9** (removed lower bound, a `Nat` inequality)
  `1600 m ≤ 2920 f + 219 A`,
* **L10** (recovered upper bound, a `Nat` inequality)
  `200 g ≤ 35 A + 8 f`,

together with the baseline identification `(B : ℚ) = splitBaseline n p`, are
turned into a genuine `RD09NumericLedger` and hence into a
`PhysicalTerminal`, and then into the paid bound

```text
|completion G P| ≤ splitBaseline n p - m / 20 - A / 2 .
```

Three design constraints are respected.

* The baseline is `splitBaseline n p`, fixed **before** any inspection of
  `(completion G P).card`; nothing here uses
  `RD09NonNeutralLedger.paidLedger`, which chooses its accounts *after* seeing
  the completion count.
* The accounts are natural numbers coming from literal finite families
  (`PhysicalAccounts` below carries the removed and recovered families
  themselves, and `f`, `g` are their cardinalities), so all four nonnegativity
  side conditions are theorems, not hypotheses.
* The orientation of the RD09 inequalities is the verified one: `removed`
  absorbs the mismatch (`L9` allows `f` to be as large as needed) while
  `rootLoss` is kept small (`A` enters `L9` only with the small coefficient
  `219/2920 = 3/40`).

`L9` and `L10` are the exact integral forms of the rational RD09 bounds
`40/73 · m - 3/40 · A ≤ f` and `g ≤ 7/40 · A + f/25`; see
`removed_lower_of_L9` and `recovered_upper_of_L10`.

## What is still missing physically

The adapter is *exact*: no counting fact is fabricated.  For the literal
two-phase root-factor configuration the piece count
`card_union_rootFactorPhases` is available, and
`PhysicalCompletion.card_completion` splits the completion count into pieces
plus uncovered edges, so `L3` is reduced by
`twoPhase_L3_of_uncovered_counts` to a statement about

```text
(uncoveredEdges G (multiLiftedPacking z E ∪ phaseTwoPacking hub base)).card .
```

**The first absent counting lemma is exactly the evaluation of that number.**
The source computes the covered-edge count
(`card_coveredEdges_union_rootFactorPhases`) and the completion count *under
the hypothesis of exact global coverage* (`card_completion_of_covers`), but it
contains no lemma bounding or computing the uncovered-edge count of the
two-phase packing in terms of the phase data when coverage is not assumed.
Until that lemma exists, `L3` for the actual RD09 construction must remain an
explicit hypothesis, as it is here.
-/

namespace PaperIV.RD09PhysicalLedger

open Finset PaperIV.Model PaperIV.PhysicalCompletion
open PaperIV.RD09TerminalAssembly PaperIV.TerminalLedger

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ## The integral RD09 inequalities -/

/-- **L9 → the RD09 removed lower bound.**  The integral inequality
`1600 m ≤ 2920 f + 219 A` is exactly `40/73 · m - 3/40 · A ≤ f`. -/
theorem removed_lower_of_L9 {m A f : ℕ} (L9 : 1600 * m ≤ 2920 * f + 219 * A) :
    (40 : ℚ) / 73 * (m : ℚ) - (3 : ℚ) / 40 * (A : ℚ) ≤ (f : ℚ) := by
  have h : (1600 : ℚ) * (m : ℚ) ≤ 2920 * (f : ℚ) + 219 * (A : ℚ) := by
    exact_mod_cast L9
  linarith

/-- **L10 → the RD09 recovered upper bound.**  The integral inequality
`200 g ≤ 35 A + 8 f` is exactly `g ≤ 7/40 · A + f / 25`. -/
theorem recovered_upper_of_L10 {A f g : ℕ} (L10 : 200 * g ≤ 35 * A + 8 * f) :
    (g : ℚ) ≤ (7 : ℚ) / 40 * (A : ℚ) + (f : ℚ) / 25 := by
  have h : (200 : ℚ) * (g : ℚ) ≤ 35 * (A : ℚ) + 8 * (f : ℚ) := by
    exact_mod_cast L10
  linarith

/-- **L3 → the rational ledger equality.** -/
theorem ledger_of_L3 {P : Finset (Finset V)} {B m A f g : ℕ} {n p : ℚ}
    (hbase : (B : ℚ) = splitBaseline n p)
    (L3 : (completion G P).card + A + 2 * f = B + m + 2 * g) :
    ((completion G P).card : ℚ) =
      splitBaseline n p + (m : ℚ) - (A : ℚ) - 2 * (f : ℚ) + 2 * (g : ℚ) := by
  have h : (((completion G P).card : ℚ)) + (A : ℚ) + 2 * (f : ℚ)
      = (B : ℚ) + (m : ℚ) + 2 * (g : ℚ) := by exact_mod_cast L3
  rw [hbase] at h
  linarith

/-! ## The adapter -/

/-- **The adapter.**  The three literal counting facts `L3`, `L9`, `L10`, with
the baseline pinned to `splitBaseline n p`, produce a genuine RD09 numeric
ledger for the packing `P`. -/
def ledgerOfNatIdentities (P : Finset (Finset V)) {B m A f g : ℕ} {n p : ℚ}
    (hbase : (B : ℚ) = splitBaseline n p)
    (L3 : (completion G P).card + A + 2 * f = B + m + 2 * g)
    (L9 : 1600 * m ≤ 2920 * f + 219 * A)
    (L10 : 200 * g ≤ 35 * A + 8 * f) :
    RD09NumericLedger G P where
  base := splitBaseline n p
  missing := (m : ℚ)
  rootLoss := (A : ℚ)
  removed := (f : ℚ)
  recovered := (g : ℚ)
  ledger := ledger_of_L3 hbase L3
  removed_lower := removed_lower_of_L9 L9
  recovered_upper := recovered_upper_of_L10 L10

@[simp] theorem ledgerOfNatIdentities_base (P : Finset (Finset V)) {B m A f g : ℕ} {n p : ℚ}
    (hbase : (B : ℚ) = splitBaseline n p)
    (L3 : (completion G P).card + A + 2 * f = B + m + 2 * g)
    (L9 : 1600 * m ≤ 2920 * f + 219 * A) (L10 : 200 * g ≤ 35 * A + 8 * f) :
    (ledgerOfNatIdentities P hbase L3 L9 L10).base = splitBaseline n p := rfl

@[simp] theorem ledgerOfNatIdentities_missing (P : Finset (Finset V)) {B m A f g : ℕ} {n p : ℚ}
    (hbase : (B : ℚ) = splitBaseline n p)
    (L3 : (completion G P).card + A + 2 * f = B + m + 2 * g)
    (L9 : 1600 * m ≤ 2920 * f + 219 * A) (L10 : 200 * g ≤ 35 * A + 8 * f) :
    (ledgerOfNatIdentities P hbase L3 L9 L10).missing = (m : ℚ) := rfl

@[simp] theorem ledgerOfNatIdentities_rootLoss (P : Finset (Finset V)) {B m A f g : ℕ} {n p : ℚ}
    (hbase : (B : ℚ) = splitBaseline n p)
    (L3 : (completion G P).card + A + 2 * f = B + m + 2 * g)
    (L9 : 1600 * m ≤ 2920 * f + 219 * A) (L10 : 200 * g ≤ 35 * A + 8 * f) :
    (ledgerOfNatIdentities P hbase L3 L9 L10).rootLoss = (A : ℚ) := rfl

@[simp] theorem ledgerOfNatIdentities_removed (P : Finset (Finset V)) {B m A f g : ℕ} {n p : ℚ}
    (hbase : (B : ℚ) = splitBaseline n p)
    (L3 : (completion G P).card + A + 2 * f = B + m + 2 * g)
    (L9 : 1600 * m ≤ 2920 * f + 219 * A) (L10 : 200 * g ≤ 35 * A + 8 * f) :
    (ledgerOfNatIdentities P hbase L3 L9 L10).removed = (f : ℚ) := rfl

@[simp] theorem ledgerOfNatIdentities_recovered (P : Finset (Finset V)) {B m A f g : ℕ} {n p : ℚ}
    (hbase : (B : ℚ) = splitBaseline n p)
    (L3 : (completion G P).card + A + 2 * f = B + m + 2 * g)
    (L9 : 1600 * m ≤ 2920 * f + 219 * A) (L10 : 200 * g ≤ 35 * A + 8 * f) :
    (ledgerOfNatIdentities P hbase L3 L9 L10).recovered = (g : ℚ) := rfl

/-- **Nonnegativity of all four accounts** — a theorem, because the accounts
are cardinalities. -/
theorem ledgerOfNatIdentities_nonneg (P : Finset (Finset V)) {B m A f g : ℕ} {n p : ℚ}
    (hbase : (B : ℚ) = splitBaseline n p)
    (L3 : (completion G P).card + A + 2 * f = B + m + 2 * g)
    (L9 : 1600 * m ≤ 2920 * f + 219 * A) (L10 : 200 * g ≤ 35 * A + 8 * f) :
    0 ≤ (ledgerOfNatIdentities P hbase L3 L9 L10).missing ∧
      0 ≤ (ledgerOfNatIdentities P hbase L3 L9 L10).rootLoss ∧
      0 ≤ (ledgerOfNatIdentities P hbase L3 L9 L10).removed ∧
      0 ≤ (ledgerOfNatIdentities P hbase L3 L9 L10).recovered :=
  ⟨by simp, by simp, by simp, by simp⟩

/-- The same adapter into the canonical paid-terminal interface. -/
def terminalOfNatIdentities {P : Finset (Finset V)} (hP : IsK34Packing G P)
    {B m A f g : ℕ} {n p : ℚ}
    (hbase : (B : ℚ) = splitBaseline n p)
    (L3 : (completion G P).card + A + 2 * f = B + m + 2 * g)
    (L9 : 1600 * m ≤ 2920 * f + 219 * A)
    (L10 : 200 * g ≤ 35 * A + 8 * f) :
    PhysicalTerminal (G := G) where
  packing := P
  isK34 := hP
  base := splitBaseline n p
  missing := (m : ℚ)
  rootLoss := (A : ℚ)
  removed := (f : ℚ)
  recovered := (g : ℚ)
  ledger := ledger_of_L3 hbase L3
  removed_lower := removed_lower_of_L9 L9
  recovered_upper := recovered_upper_of_L10 L10

@[simp] theorem terminalOfNatIdentities_packing {P : Finset (Finset V)} (hP : IsK34Packing G P)
    {B m A f g : ℕ} {n p : ℚ}
    (hbase : (B : ℚ) = splitBaseline n p)
    (L3 : (completion G P).card + A + 2 * f = B + m + 2 * g)
    (L9 : 1600 * m ≤ 2920 * f + 219 * A) (L10 : 200 * g ≤ 35 * A + 8 * f) :
    (terminalOfNatIdentities hP hbase L3 L9 L10).packing = P := rfl

/-! ## The paid bound against the split baseline -/

/-- **The paid RD09 bound with a physical baseline.**  From the three literal
counting facts alone,
`|completion G P| ≤ splitBaseline n p - m / 20 - A / 2`. -/
theorem count_le_splitBaseline_sub {P : Finset (Finset V)} {B m A f g : ℕ} {n p : ℚ}
    (hbase : (B : ℚ) = splitBaseline n p)
    (L3 : (completion G P).card + A + 2 * f = B + m + 2 * g)
    (L9 : 1600 * m ≤ 2920 * f + 219 * A)
    (L10 : 200 * g ≤ 35 * A + 8 * f) :
    ((completion G P).card : ℚ) ≤ splitBaseline n p - (m : ℚ) / 20 - (A : ℚ) / 2 := by
  have hledger := ledger_of_L3 (G := G) (P := P) hbase L3
  have hrem := removed_lower_of_L9 L9
  have hrec := recovered_upper_of_L10 L10
  have hpaid :=
    PaperIV.ParametricBudget.exact_piece_budget hledger hrem hrec
  have hcoeff := PaperIV.ParametricBudget.rd09_coefficients
  have hm : (0 : ℚ) ≤ (m : ℚ) := by positivity
  have hA : (0 : ℚ) ≤ (A : ℚ) := by positivity
  nlinarith

/-- The strong exact-piece form of the same bound. -/
theorem count_le_exact_piece_splitBaseline {P : Finset (Finset V)} {B m A f g : ℕ} {n p : ℚ}
    (hbase : (B : ℚ) = splitBaseline n p)
    (L3 : (completion G P).card + A + 2 * f = B + m + 2 * g)
    (L9 : 1600 * m ≤ 2920 * f + 219 * A)
    (L10 : 200 * g ≤ 35 * A + 8 * f) :
    ((completion G P).card : ℚ) ≤
      splitBaseline n p - (19 : ℚ) / 365 * (m : ℚ) - (253 : ℚ) / 500 * (A : ℚ) :=
  PaperIV.ParametricBudget.exact_piece_budget (ledger_of_L3 (G := G) (P := P) hbase L3)
    (removed_lower_of_L9 L9) (recovered_upper_of_L10 L10)

/-- Since `splitBaseline n p ≤ sharpEnvelope n`, the paid bound is also a bound
against the sharp envelope. -/
theorem count_le_sharpEnvelope_sub {P : Finset (Finset V)} {B m A f g : ℕ} {n p : ℚ}
    (hbase : (B : ℚ) = splitBaseline n p)
    (L3 : (completion G P).card + A + 2 * f = B + m + 2 * g)
    (L9 : 1600 * m ≤ 2920 * f + 219 * A)
    (L10 : 200 * g ≤ 35 * A + 8 * f) :
    ((completion G P).card : ℚ) ≤ sharpEnvelope n - (m : ℚ) / 20 - (A : ℚ) / 2 := by
  have h := count_le_splitBaseline_sub (G := G) (P := P) hbase L3 L9 L10
  have hb := splitBaseline_le_sharpEnvelope n p
  linarith

/-! ## Physical accounts carried by literal finite families -/

variable (G) in
/-- The physical RD09 accounts of a literal packing: the split parameters, the
baseline count, the missing and root-loss edge sets, and the **actual finite
families** of removed and recovered pieces.  The three counting facts are the
structure's only proof obligations. -/
structure PhysicalAccounts (P : Finset (Finset V)) where
  /-- order parameter of the split baseline -/
  order : ℚ
  /-- split parameter of the split baseline -/
  split : ℚ
  /-- the integral baseline count -/
  baseCount : ℕ
  /-- the baseline is the split baseline, fixed before the packing is counted -/
  base_eq : (baseCount : ℚ) = splitBaseline order split
  /-- the literal family of missing edges -/
  missingEdges : Finset (Sym2 V)
  /-- the literal family of root-factor losses -/
  rootLossEdges : Finset (Sym2 V)
  /-- the literal family of removed pieces -/
  removedPieces : Finset (Finset V)
  /-- the literal family of recovered pieces -/
  recoveredPieces : Finset (Finset V)
  /-- **L3**: the two-phase ledger identity between natural counts -/
  L3 : (completion G P).card + rootLossEdges.card + 2 * removedPieces.card
    = baseCount + missingEdges.card + 2 * recoveredPieces.card
  /-- **L9**: the integral RD09 lower bound on removed pieces -/
  L9 : 1600 * missingEdges.card
    ≤ 2920 * removedPieces.card + 219 * rootLossEdges.card
  /-- **L10**: the integral RD09 upper bound on recovered pieces -/
  L10 : 200 * recoveredPieces.card
    ≤ 35 * rootLossEdges.card + 8 * removedPieces.card

namespace PhysicalAccounts

variable {P : Finset (Finset V)}

/-- The numeric ledger of the physical accounts. -/
def toNumericLedger (acc : PhysicalAccounts G P) : RD09NumericLedger G P :=
  ledgerOfNatIdentities P acc.base_eq acc.L3 acc.L9 acc.L10

@[simp] theorem toNumericLedger_base (acc : PhysicalAccounts G P) :
    acc.toNumericLedger.base = splitBaseline acc.order acc.split := rfl

@[simp] theorem toNumericLedger_missing (acc : PhysicalAccounts G P) :
    acc.toNumericLedger.missing = (acc.missingEdges.card : ℚ) := rfl

@[simp] theorem toNumericLedger_rootLoss (acc : PhysicalAccounts G P) :
    acc.toNumericLedger.rootLoss = (acc.rootLossEdges.card : ℚ) := rfl

@[simp] theorem toNumericLedger_removed (acc : PhysicalAccounts G P) :
    acc.toNumericLedger.removed = (acc.removedPieces.card : ℚ) := rfl

@[simp] theorem toNumericLedger_recovered (acc : PhysicalAccounts G P) :
    acc.toNumericLedger.recovered = (acc.recoveredPieces.card : ℚ) := rfl

/-- All four accounts of a physical ledger are nonnegative. -/
theorem nonneg (acc : PhysicalAccounts G P) :
    0 ≤ acc.toNumericLedger.missing ∧ 0 ≤ acc.toNumericLedger.rootLoss ∧
      0 ≤ acc.toNumericLedger.removed ∧ 0 ≤ acc.toNumericLedger.recovered :=
  ⟨by simp, by simp, by simp, by simp⟩

/-- The physical accounts of a literal `K3`/`K4` packing give a paid terminal. -/
def toPhysicalTerminal (hP : IsK34Packing G P) (acc : PhysicalAccounts G P) :
    PhysicalTerminal (G := G) :=
  terminalOfNatIdentities hP acc.base_eq acc.L3 acc.L9 acc.L10

@[simp] theorem toPhysicalTerminal_packing (hP : IsK34Packing G P)
    (acc : PhysicalAccounts G P) : (acc.toPhysicalTerminal hP).packing = P := rfl

/-- **Item (2).**  The completed physical packing pays the RD09 discount
against its own split baseline. -/
theorem count_le_paid (acc : PhysicalAccounts G P) :
    ((completion G P).card : ℚ) ≤ splitBaseline acc.order acc.split
      - (acc.missingEdges.card : ℚ) / 20 - (acc.rootLossEdges.card : ℚ) / 2 :=
  count_le_splitBaseline_sub acc.base_eq acc.L3 acc.L9 acc.L10

/-- The same accounts also give the strong exact-piece estimate. -/
theorem count_le_exact_piece (acc : PhysicalAccounts G P) :
    ((completion G P).card : ℚ) ≤ splitBaseline acc.order acc.split
      - (19 : ℚ) / 365 * (acc.missingEdges.card : ℚ)
      - (253 : ℚ) / 500 * (acc.rootLossEdges.card : ℚ) :=
  count_le_exact_piece_splitBaseline acc.base_eq acc.L3 acc.L9 acc.L10

end PhysicalAccounts

/-! ## The verified orientation: removed absorbs the mismatch, rootLoss stays small -/

/-- With no root loss, `L9` is just `40 m ≤ 73 f`: the removed family absorbs
the whole mismatch. -/
theorem L9_of_no_rootLoss {m f : ℕ} (h : 40 * m ≤ 73 * f) :
    1600 * m ≤ 2920 * f + 219 * 0 := by omega

/-- With no root loss, `L10` is just `25 g ≤ f`: the recovered family is a small
fraction of the removed one. -/
theorem L10_of_no_rootLoss {f g : ℕ} (h : 25 * g ≤ f) :
    200 * g ≤ 35 * 0 + 8 * f := by omega

/-- **The removed-absorbing ledger.**  In the orientation the route prescribes
— all mismatch charged to `removed`, root loss kept at zero — the two RD09
inequalities reduce to `40 m ≤ 73 f` and `25 g ≤ f`, and the paid bound becomes
`count ≤ splitBaseline n p - m / 20`. -/
theorem count_le_splitBaseline_sub_of_no_rootLoss {P : Finset (Finset V)}
    {B m f g : ℕ} {n p : ℚ}
    (hbase : (B : ℚ) = splitBaseline n p)
    (L3 : (completion G P).card + 0 + 2 * f = B + m + 2 * g)
    (L9 : 40 * m ≤ 73 * f)
    (L10 : 25 * g ≤ f) :
    ((completion G P).card : ℚ) ≤ splitBaseline n p - (m : ℚ) / 20 := by
  have h := count_le_splitBaseline_sub (G := G) (P := P) (A := 0) hbase L3
    (L9_of_no_rootLoss L9) (L10_of_no_rootLoss L10)
  simpa using h

/-! ## Reduction of `L3` to pieces and uncovered edges -/

/-- `L3` for a `K3`/`K4` packing is equivalent to the same identity with the
completion count replaced by *pieces plus uncovered edges*.  This is the form
in which the physical construction produces it. -/
theorem L3_of_pieces_uncovered {P : Finset (Finset V)} (hP : IsK34Packing G P)
    {B m A f g : ℕ}
    (h : P.card + (uncoveredEdges G P).card + A + 2 * f = B + m + 2 * g) :
    (completion G P).card + A + 2 * f = B + m + 2 * g := by
  rw [card_completion hP]
  exact h

section TwoPhase

open PaperIV.ExteriorTriangleLift PaperIV.MultiHostTriangleLift
open PaperIV.RD09PhaseII PaperIV.RD09RootFactorPhase

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
variable {z : I → V} {E : I → Finset (Sym2 V)}
variable {root : Finset V} {hub : J → Finset V} {base : J → Sym2 V}

omit [DecidableEq J] in
/-- **`L3` for the literal two-phase root-factor packing.**  Its piece count is
already known (`card_union_rootFactorPhases`), so the identity is reduced to
the *uncovered-edge count* of the two-phase configuration — the first counting
lemma the source does not yet supply. -/
theorem twoPhase_L3_of_uncovered_counts (h1 : IsMultiExteriorHub G z E)
    (h : IsRootFactorFamily G root hub base) (hsep : IsRootHostSeparated z E root hub)
    {B m A f g : ℕ}
    (hcount : ((∑ i, (E i).card) + Fintype.card J)
        + (uncoveredEdges G (multiLiftedPacking z E ∪ phaseTwoPacking hub base)).card
        + A + 2 * f = B + m + 2 * g) :
    (completion G (multiLiftedPacking z E ∪ phaseTwoPacking hub base)).card + A + 2 * f
      = B + m + 2 * g := by
  refine L3_of_pieces_uncovered (isK34Packing_union_rootFactorPhases h1 h hsep) ?_
  rwa [card_union_rootFactorPhases h1 h hsep]

omit [DecidableEq J] in
/-- **The exact two-phase adapter.**  A literal RD09 two-phase root-factor
configuration whose uncovered-edge count satisfies the physical ledger
identity, together with the two integral RD09 inequalities and a split
baseline fixed in advance, is a paid `PhysicalTerminal` obeying
`|completion| ≤ splitBaseline n p - m/20 - A/2`. -/
theorem twoPhase_count_le_splitBaseline_sub (h1 : IsMultiExteriorHub G z E)
    (h : IsRootFactorFamily G root hub base) (hsep : IsRootHostSeparated z E root hub)
    {B m A f g : ℕ} {n p : ℚ}
    (hbase : (B : ℚ) = splitBaseline n p)
    (hcount : ((∑ i, (E i).card) + Fintype.card J)
        + (uncoveredEdges G (multiLiftedPacking z E ∪ phaseTwoPacking hub base)).card
        + A + 2 * f = B + m + 2 * g)
    (L9 : 1600 * m ≤ 2920 * f + 219 * A)
    (L10 : 200 * g ≤ 35 * A + 8 * f) :
    ((completion G (multiLiftedPacking z E ∪ phaseTwoPacking hub base)).card : ℚ)
      ≤ splitBaseline n p - (m : ℚ) / 20 - (A : ℚ) / 2 :=
  count_le_splitBaseline_sub hbase
    (twoPhase_L3_of_uncovered_counts h1 h hsep hcount) L9 L10

/-- The same configuration, presented through the canonical paid-terminal
interface. -/
def twoPhaseTerminal (h1 : IsMultiExteriorHub G z E)
    (h : IsRootFactorFamily G root hub base) (hsep : IsRootHostSeparated z E root hub)
    {B m A f g : ℕ} {n p : ℚ}
    (hbase : (B : ℚ) = splitBaseline n p)
    (hcount : ((∑ i, (E i).card) + Fintype.card J)
        + (uncoveredEdges G (multiLiftedPacking z E ∪ phaseTwoPacking hub base)).card
        + A + 2 * f = B + m + 2 * g)
    (L9 : 1600 * m ≤ 2920 * f + 219 * A)
    (L10 : 200 * g ≤ 35 * A + 8 * f) :
    PhysicalTerminal (G := G) :=
  terminalOfNatIdentities (isK34Packing_union_rootFactorPhases h1 h hsep) hbase
    (twoPhase_L3_of_uncovered_counts h1 h hsep hcount) L9 L10

end TwoPhase

end PaperIV.RD09PhysicalLedger

