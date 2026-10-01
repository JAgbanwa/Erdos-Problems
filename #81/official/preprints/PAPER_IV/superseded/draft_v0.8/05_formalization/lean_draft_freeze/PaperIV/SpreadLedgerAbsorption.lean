import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import PaperIV.SpreadAbsorption
import PaperIV.RD09PhysicalLedger

/-!
# Paying spread absorption from the literal RD09 ledger

The generic spread theorem selects a perfect matching whose oriented conflict
cost is at most a `1 / (t+1)` fraction of the total conflict mass.  This module
supplies the missing application to the physical RD09 accounts.

The conflict graph has precisely the non-diagonal edges recorded by
`missingEdges ∪ rootLossEdges`.  Its oriented mass is twice its number of
edges, by the handshaking lemma, and hence at most twice the sum of the two
ledger accounts.  When `40 ≤ t+1`, the existing RD09 discount

`missing / 20 + rootLoss / 2`

pays that selected mass.  No abstract conflict function remains in the final
statement.
-/

namespace PaperIV.SpreadLedgerAbsorption

open Finset PaperIV.Model PaperIV.PhysicalCompletion PaperIV.SpreadAbsorption
open PaperIV.RD09PhysicalLedger

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable {P : Finset (Finset V)}

/-- The literal edge account that can obstruct a spread repair. -/
def ledgerConflictEdges (acc : PhysicalAccounts G P) : Finset (Sym2 V) :=
  acc.missingEdges ∪ acc.rootLossEdges

/-- The simple graph obtained from the literal conflict account.  Diagonal
entries, should an abstract account contain any, are harmlessly discarded by
`SimpleGraph.fromEdgeSet`. -/
def ledgerConflictGraph (acc : PhysicalAccounts G P) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet (ledgerConflictEdges acc : Set (Sym2 V))

/-- The oriented `0/1` conflict cost used by the spread theorem. -/
noncomputable def ledgerBad (acc : PhysicalAccounts G P) (y x : V) : ℝ := by
  classical
  exact if (ledgerConflictGraph acc).Adj y x then 1 else 0

theorem ledgerBad_nonneg (acc : PhysicalAccounts G P) (y x : V) :
    0 ≤ ledgerBad acc y x := by
  classical
  unfold ledgerBad
  split <;> norm_num

/-- Restricting the oriented conflict mass to `N × N` cannot exceed the
global oriented mass of the conflict graph. -/
theorem sum_ledgerBad_le_global (acc : PhysicalAccounts G P) (N : Finset V) :
    ∑ y ∈ N, ∑ x ∈ N, ledgerBad acc y x ≤
      (2 : ℝ) * (ledgerConflictEdges acc).card := by
  classical
  let H := ledgerConflictGraph acc
  have hsub : (N ×ˢ N).filter (fun p => H.Adj p.1 p.2) ⊆
      (Finset.univ : Finset (V × V)).filter (fun p => H.Adj p.1 p.2) := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_product] at hp ⊢
    exact ⟨Finset.mem_univ _, hp.2⟩
  have hcard := Finset.card_le_card hsub
  have hhand := H.two_mul_card_edgeFinset
  have hsum : ∑ y ∈ N, ∑ x ∈ N, ledgerBad acc y x =
      (((N ×ˢ N).filter (fun p => H.Adj p.1 p.2)).card : ℝ) := by
    change (∑ y ∈ N, ∑ x ∈ N, if H.Adj y x then (1 : ℝ) else 0) = _
    rw [← Finset.sum_product']
    exact Finset.sum_boole _ _
  have hedge : H.edgeFinset.card ≤ (ledgerConflictEdges acc).card := by
    apply Finset.card_le_card
    intro e he
    rw [SimpleGraph.mem_edgeFinset] at he
    change e ∈ (ledgerConflictGraph acc).edgeSet at he
    rw [ledgerConflictGraph, SimpleGraph.edgeSet_fromEdgeSet] at he
    exact he.1
  rw [hsum]
  have hnat : ((N ×ˢ N).filter (fun p => H.Adj p.1 p.2)).card ≤
      2 * (ledgerConflictEdges acc).card := by
    calc
      ((N ×ˢ N).filter (fun p => H.Adj p.1 p.2)).card
          ≤ ((Finset.univ : Finset (V × V)).filter
              (fun p => H.Adj p.1 p.2)).card := hcard
      _ = 2 * H.edgeFinset.card := hhand.symm
      _ ≤ 2 * (ledgerConflictEdges acc).card := Nat.mul_le_mul_left 2 hedge
  exact_mod_cast hnat

/-- The complete mass estimate demanded by the spread interface, now derived
from the actual RD09 accounts. -/
theorem total_ledgerBad_le_two_accounts (acc : PhysicalAccounts G P)
    (N : Finset V) :
    ∑ y ∈ N, ∑ x ∈ N, ledgerBad acc y x ≤
      2 * ((acc.missingEdges.card : ℝ) + acc.rootLossEdges.card) := by
  refine (sum_ledgerBad_le_global acc N).trans ?_
  exact_mod_cast Nat.mul_le_mul_left 2 (Finset.card_union_le
    acc.missingEdges acc.rootLossEdges)

/-- Forty units of Dirac slack make the literal RD09 discount large enough to
pay the selected spread conflicts. -/
theorem total_ledgerBad_le_paid_mass (acc : PhysicalAccounts G P)
    (N : Finset V) {t : ℕ} (ht : 40 ≤ t + 1) :
    ∑ y ∈ N, ∑ x ∈ N, ledgerBad acc y x ≤
      ((t : ℝ) + 1) *
        ((acc.missingEdges.card : ℝ) / 20 +
          (acc.rootLossEdges.card : ℝ) / 2) := by
  have hmass := total_ledgerBad_le_two_accounts acc N
  have htR : (40 : ℝ) ≤ (t : ℝ) + 1 := by exact_mod_cast ht
  have hm : (0 : ℝ) ≤ acc.missingEdges.card := by positivity
  have hA : (0 : ℝ) ≤ acc.rootLossEdges.card := by positivity
  calc
    ∑ y ∈ N, ∑ x ∈ N, ledgerBad acc y x
        ≤ 2 * ((acc.missingEdges.card : ℝ) + acc.rootLossEdges.card) := hmass
    _ ≤ ((t : ℝ) + 1) *
        ((acc.missingEdges.card : ℝ) / 20 +
          (acc.rootLossEdges.card : ℝ) / 2) := by nlinarith

/-- **Closed spread-ledger gate.**  Under the Dirac surplus already required
by the spread constructor, the physical RD09 ledger itself defines the
conflict cost and pays the selected literal triangle absorber.

The conclusion simultaneously records physical edge-disjointness, exact gain,
and the budget charged to the two genuine ledger accounts. -/
theorem exists_paid_spread_absorber (acc : PhysicalAccounts G P)
    {N : Finset V} {t : ℕ} (heven : Even N.card)
    (hdeg : ∀ v ∈ N, N.card / 2 + t ≤ (N.filter fun z => G.Adj v z).card)
    (ht : 40 ≤ t + 1) {z : V} (hz : ∀ a ∈ N, G.Adj z a) :
    ∃ C : Certificate G N,
      IsPacking G (physicalTriangleAbsorber C z) ∧
      totalGain (physicalTriangleAbsorber C z) = N.card ∧
      ∑ y ∈ N, ledgerBad acc y (C.partner y) ≤
        (acc.missingEdges.card : ℝ) / 20 +
          (acc.rootLossEdges.card : ℝ) / 2 := by
  apply exists_budgeted_physical_triangle_absorber heven hdeg
    (ledgerBad acc) (ledgerBad_nonneg acc)
  · exact total_ledgerBad_le_paid_mass acc N ht
  · exact hz

/-- The paid spread selection and the existing physical completion fit jointly
under the split baseline.  This is the numerical closure of the application:
the matching does not introduce an unpaid reserve. -/
theorem exists_spread_absorber_count_add_cost_le_baseline
    (acc : PhysicalAccounts G P) {N : Finset V} {t : ℕ}
    (heven : Even N.card)
    (hdeg : ∀ v ∈ N, N.card / 2 + t ≤ (N.filter fun z => G.Adj v z).card)
    (ht : 40 ≤ t + 1) {z : V} (hz : ∀ a ∈ N, G.Adj z a) :
    ∃ C : Certificate G N,
      IsPacking G (physicalTriangleAbsorber C z) ∧
      totalGain (physicalTriangleAbsorber C z) = N.card ∧
      ((completion G P).card : ℝ) +
          ∑ y ∈ N, ledgerBad acc y (C.partner y) ≤
        ((splitBaseline acc.order acc.split : ℚ) : ℝ) := by
  obtain ⟨C, hpack, hgain, hcost⟩ :=
    exists_paid_spread_absorber acc heven hdeg ht hz
  refine ⟨C, hpack, hgain, ?_⟩
  have hpaidQ := acc.count_le_paid
  have hpaidR : ((completion G P).card : ℝ) ≤
      ((splitBaseline acc.order acc.split : ℚ) : ℝ) -
        (acc.missingEdges.card : ℝ) / 20 -
        (acc.rootLossEdges.card : ℝ) / 2 := by
    have hcast := (Rat.cast_le (K := ℝ)).2 hpaidQ
    norm_num at hcast ⊢
    exact hcast
  linarith

end PaperIV.SpreadLedgerAbsorption
