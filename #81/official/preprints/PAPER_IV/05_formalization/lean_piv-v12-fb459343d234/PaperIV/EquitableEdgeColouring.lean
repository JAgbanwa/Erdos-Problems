import PaperIV.LineGraphColouring
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Data.Int.Star

/-!
# Equal-size refinement target for the local Vizing colouring

This module fixes the exact endpoint needed by the H1/RD09 constructor in the
native `PaperIV.ColourClasses` model.  It is deliberately independent of the
published external formalization: edges are literal `Sym2` resources and
properness is `ColourClasses.ProperOn`.

The remaining theorem in this workstream is constructive: an arbitrary
`ProperOn E colour` can be changed, on the same finite palette, into one
satisfying `IsEquitable`.  Its proof will use alternating components and
strict descent of `energy`.  Everything after that descent is closed below,
including the precise ceiling bound consumed by RD09.
-/

namespace PaperIV.EquitableEdgeColouring

open PaperIV.ColourClasses

variable {V Color : Type*} [DecidableEq V]
  [Fintype Color] [DecidableEq Color]

/-- All literal colour classes differ in cardinality by at most one. -/
def IsEquitable (E : Finset (Sym2 V)) (colour : Sym2 V → Color) : Prop :=
  ∀ a b : Color,
    (colourClass E colour a).card ≤ (colourClass E colour b).card + 1

/-- The square-energy used by alternating-component descent. -/
def energy (E : Finset (Sym2 V)) (colour : Sym2 V → Color) : ℕ :=
  ∑ a : Color, (colourClass E colour a).card ^ 2

/-- The exact arithmetic behind one balancing move.  Moving one edge from a
class of size `large` to a class of size `small` strictly decreases the
square-energy as soon as the two sizes differ by at least two. -/
theorem two_class_energy_drop {small large : ℕ}
    (hgap : small + 1 < large) :
    (large - 1) ^ 2 + (small + 1) ^ 2 < large ^ 2 + small ^ 2 := by
  have hlarge : 1 ≤ large := by omega
  nlinarith [Nat.sub_add_cancel hlarge]

/-- Finite descent is logically separate from the Kempe-component lemma.  If
every non-equitable proper colouring admits one proper recolouring of smaller
energy, then an equitable proper colouring exists.  This packages the global
termination argument without assuming any graph-theoretic input. -/
theorem exists_equitable_of_energy_descent
    (E : Finset (Sym2 V))
    (step : ∀ colour : Sym2 V → Color,
      ProperOn E colour → ¬ IsEquitable E colour →
      ∃ colour' : Sym2 V → Color,
        ProperOn E colour' ∧ energy E colour' < energy E colour)
    (colour : Sym2 V → Color) (hproper : ProperOn E colour) :
    ∃ colour' : Sym2 V → Color,
      ProperOn E colour' ∧ IsEquitable E colour' := by
  classical
  induction henergy : energy E colour using Nat.strong_induction_on generalizing colour with
  | h n ih =>
      by_cases hEq : IsEquitable E colour
      · exact ⟨colour, hproper, hEq⟩
      · obtain ⟨colour', hproper', hdrop⟩ := step colour hproper hEq
        exact ih (energy E colour') (henergy ▸ hdrop) colour' hproper' rfl

/-- Summing over the whole declared palette counts every literal edge once;
unused colours simply contribute zero. -/
theorem sum_card_colourClass_univ
    (E : Finset (Sym2 V)) (colour : Sym2 V → Color) :
    ∑ a : Color, (colourClass E colour a).card = E.card := by
  classical
  simpa [colourClass] using
    (Finset.sum_card_fiberwise_eq_card_filter
      E (Finset.univ : Finset Color) colour)

/-- The natural ceiling of the average class size. -/
def classCeiling (m c : ℕ) : ℕ := m ⌈/⌉ c

theorem edge_count_le_colors_mul_ceiling (m c : ℕ) (hc : 0 < c) :
    m ≤ c * classCeiling m c := by
  simpa [classCeiling, Nat.nsmul_eq_mul] using
    (le_smul_ceilDiv (a := c) (b := m) hc)

/-- The endpoint needed by the physical constructor: equitability forces each
class below the ceiling of the average. -/
theorem class_card_le_ceiling_of_equitable
    [Nonempty Color] (E : Finset (Sym2 V)) (colour : Sym2 V → Color)
    (hEq : IsEquitable E colour) (a : Color) :
    (colourClass E colour a).card ≤ classCeiling E.card (Fintype.card Color) := by
  classical
  let t := classCeiling E.card (Fintype.card Color)
  have hc : 0 < Fintype.card Color := Fintype.card_pos
  have htotal := sum_card_colourClass_univ E colour
  have hceil := edge_count_le_colors_mul_ceiling E.card (Fintype.card Color) hc
  by_contra hnot
  have ha : t < (colourClass E colour a).card := by
    simpa [t] using Nat.lt_of_not_ge hnot
  have hall : ∀ b : Color, t ≤ (colourClass E colour b).card := by
    intro b
    have hab := hEq a b
    omega
  have hstrict :
      (∑ _b : Color, t) < ∑ b : Color, (colourClass E colour b).card := by
    exact Finset.sum_lt_sum (fun b _ => hall b)
      ⟨a, Finset.mem_univ a, ha⟩
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hstrict
  rw [htotal] at hstrict
  have : Fintype.card Color * t < E.card := by
    simpa [Nat.mul_comm] using hstrict
  simp only [t] at this
  omega

/-- A proper literal edge colouring together with the exact uniform class
bound required by phase I of RD09. -/
structure BoundedColouring (E : Finset (Sym2 V)) (Color : Type*)
    [Fintype Color] [DecidableEq Color] (t : ℕ) where
  colour : Sym2 V → Color
  proper : ProperOn E colour
  class_card_le : ∀ a, (colourClass E colour a).card ≤ t

/-- Package an equitable proper colouring as the bounded object consumed by
the future phase-I constructor. -/
def boundedColouringOfEquitable [Nonempty Color]
    (E : Finset (Sym2 V)) (colour : Sym2 V → Color)
    (hproper : ProperOn E colour) (hEq : IsEquitable E colour) :
    BoundedColouring E Color (classCeiling E.card (Fintype.card Color)) where
  colour := colour
  proper := hproper
  class_card_le := class_card_le_ceiling_of_equitable E colour hEq

end PaperIV.EquitableEdgeColouring
